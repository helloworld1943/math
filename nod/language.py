"""Tokenize and compose occurrence descriptions; semantics lives in runtime."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

from lark import Lark, Token, Transformer, Tree, UnexpectedInput
from lark.exceptions import VisitError
from node import Graph, GraphSnapshot, Node


MAX_SOURCE = 32_000
MAX_NODES = 20_000
MAX_STEPS = 20_000
EXPRESSION_CATEGORIES = frozenset({
    "expression", "or_expr", "and_expr", "equality", "comparison",
    "sum", "product", "unary", "postfix", "atom", "arrow_expr",
})


class LanguageError(ValueError):
    def __init__(self, stage: str, message: str, line: int = 1, column: int = 1) -> None:
        self.stage, self.message, self.line, self.column = stage, message, line, column
        super().__init__(f"{stage} at {line}:{column}: {message}")

    def as_dict(self) -> dict[str, object]:
        return {"stage": self.stage, "message": self.message, "line": self.line, "column": self.column}


@dataclass(frozen=True)
class Description:
    kind: str
    children: tuple[Node, ...]
    slots: tuple[int, ...]
    line: int
    column: int
    token: bool = False
    located: bool = True


@dataclass(frozen=True)
class Program:
    graph: GraphSnapshot
    final: Node
    descriptions: dict[Node, Description]
    tokens: tuple[Node, ...]
    occurrences: tuple[dict[str, object], ...] = ()

    def description(self, node: Node) -> Description:
        return self.descriptions[node]

    def text(self, node: Node) -> str:
        if node.value is None:
            raise ValueError("Not an information-bearing token")
        return node.value.decode("utf-8")

    def name(self, node: Node) -> str:
        return self.text(self.description(node).children[0])

    def path(self, node: Node) -> str:
        return ".".join(self.name(child) for child in self.description(node).children)

    def fail(self, stage: str, node: Node, message: str) -> LanguageError:
        info = self.description(node)
        return LanguageError(stage, message, info.line, info.column)

    def expression_layers(self, node: Node) -> tuple[tuple[Node, ...], Node]:
        layers = []
        while True:
            info = self.description(node)
            if info.kind not in EXPRESSION_CATEGORIES or len(info.children) != 1:
                return tuple(layers), node
            layers.append(node)
            node = info.children[0]

    def type_node(self, node: Node) -> Node:
        while self.description(node).kind == "type":
            node = self.description(node).children[0]
        return self.expression_layers(node)[1]

    def binding(self, node: Node) -> tuple[Node, str | None, bool, bool]:
        """Return type, optional name, const, public for ordered declarations."""
        constant, public = False, False
        while self.description(node).kind in (
            "const_field", "public_const_field", "const_parameter", "const_declaration",
        ):
            constant = True
            public = public or self.description(node).kind == "public_const_field"
            node = self.description(node).children[0]
        info = self.description(node)
        public = public or info.kind.startswith("public_")
        if len(info.children) == 1:
            candidate = self.type_node(info.children[0])
            if self.description(candidate).kind == "annotation":
                name, type_node = self.description(candidate).children
                _, name = self.expression_layers(name)
                declaration = self.description(name)
                if declaration.kind != "variable" or len(self.description(declaration.children[0]).children) != 1:
                    raise self.fail("type", node, "A named binding must use a simple identifier")
                return type_node, self.path(declaration.children[0]), constant, public
            return info.children[0], None, constant, public
        type_node, name = info.children[:2]
        return type_node, self.name(name), constant, public

    def top(self) -> tuple[Node, ...]:
        return self.description(self.description(self.final).children[0]).children

    def items(self) -> tuple[Node, ...]:
        return tuple(
            self.description(node).children[0] for node in self.top()
            if self.description(node).kind == "item"
        )


class Composer(Transformer):
    """Every successful reduction constructs a fresh occurrence node."""

    def __init__(self) -> None:
        super().__init__()
        self.graph = Graph()
        self.descriptions = {self.graph.root: Description("Root", (), (), 1, 1, located=False)}
        self.by_position: dict[int, Node] = {}
        self.tokens: list[Node] = []
        self.occurrences: list[dict[str, object]] = []

    def token(self, token: Token) -> None:
        node = self.graph.create_node(value=str(token).encode())
        self.graph.edit_link(node, 0, self.graph.root)
        self.descriptions[node] = Description(str(token.type), (), (), token.line or 1, token.column or 1, True)
        self.by_position[token.start_pos] = node
        self.tokens.append(node)
        self.occurrences.append({
            "node": node.number, "line": token.line or 1, "column": token.column or 1,
            "start": token.start_pos, "end": token.end_pos,
        })

    def compose(self, kind: str, children: tuple[Node, ...]) -> Node:
        if len(self.descriptions) >= MAX_NODES:
            raise LanguageError("limit", "Description graph is too large")
        targets = tuple(dict.fromkeys((self.graph.root, *children)))
        node = self.graph.create_node(len(targets))
        for slot, target in enumerate(targets):
            self.graph.edit_link(node, slot, target)
        first = next(
            (self.descriptions[child] for child in children
             if self.descriptions[child].located),
            self.descriptions[self.graph.root],
        )
        self.descriptions[node] = Description(
            kind, children, tuple(targets.index(child) for child in children), first.line, first.column,
            located=first.located,
        )
        return node

    def __default__(self, data, children, meta):
        if str(data).startswith("__"):
            return Tree(data, children)
        return self.compose(str(data), tuple(
            self.by_position[child.start_pos] if isinstance(child, Token) else child for child in children
        ))


GRAMMAR = Path(__file__).with_name("grammar.lark").read_text()


def make_parser(composer: Composer | None = None) -> Lark:
    return Lark(GRAMMAR, parser="lalr", lexer="basic", transformer=composer, maybe_placeholders=False, start="start")


def build_description(source: str, *, syntax: bool) -> Program:
    if not isinstance(source, str):
        raise LanguageError("input", "Source must be text")
    if len(source) > MAX_SOURCE:
        raise LanguageError("limit", f"Source exceeds {MAX_SOURCE} characters")
    composer, tokens = Composer(), []
    parser = make_parser(composer)
    try:
        depth = 0
        for token in parser.lex(source):
            if len(tokens) >= 5000:
                raise LanguageError("limit", "Too many tokens", token.line, token.column)
            if token.type in ("INTEGER", "DECIMAL") and len(str(token)) > 1024:
                raise LanguageError("limit", "Numeric literal exceeds 1024 characters", token.line, token.column)
            if str(token) in ("(", "{"):
                depth += 1
            elif str(token) in (")", "}"):
                depth -= 1
            if syntax and depth > 80:
                raise LanguageError("limit", "Source nesting exceeds 80 levels", token.line, token.column)
            composer.token(token)
            tokens.append(token)
        if syntax:
            parsing = parser.parse_interactive()
            for token in tokens:
                parsing.feed_token(token)
            syntax_node = parsing.feed_eof()
            if not isinstance(syntax_node, Node):
                raise TypeError("Grammar actions must produce a Node")
        sequence = composer.compose("TokenSequence", tuple(composer.tokens))
        final = composer.compose("Program", (syntax_node, sequence)) if syntax else sequence
        return Program(composer.graph.commit(), final, composer.descriptions, tuple(composer.tokens), tuple(composer.occurrences))
    except UnexpectedInput as error:
        stage = "tokenizer" if type(error).__name__ == "UnexpectedCharacters" else "syntax"
        raise LanguageError(stage, f"Unexpected input. {error.get_context(source, span=35).strip()}",
                            max(1, error.line), max(1, error.column)) from error
    except VisitError as error:
        if isinstance(error.orig_exc, LanguageError):
            raise error.orig_exc from error
        raise


def tokenize(source: str) -> Program:
    return build_description(source, syntax=False)


def parse(source: str) -> Program:
    return build_description(source, syntax=True)


def export_program(program: Program, checker=None) -> dict[str, object]:
    return {
        "final": program.final.number, "tokens": [node.number for node in program.tokens],
        "occurrences": list(program.occurrences),
        "nodes": [
            {
                "id": node.number, "position": position, "kind": info.kind, "token": info.token,
                "value": list(node.value) if node.value is not None else None,
                "text": node.value.decode() if node.value is not None else None,
                "line": info.line, "column": info.column,
                "outputs": [program.graph.get_output(node, slot).number for slot in range(program.graph.get_output_count(node))],
                "children": [child.number for child in info.children], "childSlots": list(info.slots),
                "type": str(checker.types[node]) if checker is not None and node in checker.types else None,
                "binding": checker.bindings[node].number if checker is not None and node in checker.bindings else None,
                **(checker.annotations.get(node, {}) if checker is not None else {}),
            }
            for position, node in enumerate(program.graph.node_order)
            for info in (program.description(node),)
        ],
    }


def inspect_stage(source: str, *, syntax: bool) -> dict[str, object]:
    try:
        return export_program(parse(source) if syntax else tokenize(source))
    except RecursionError as error:
        raise LanguageError("limit", "Description nesting is too deep") from error


def run_source(
    source: str, packages: dict[str, str] | None = None, *, check_only: bool = False,
) -> dict[str, object]:
    try:
        program = parse(source)
        from .runtime import World
        return World(program, packages or {}).run(
            check_only=check_only or any(program.description(item).kind == "check_command" for item in program.items()),
        )
    except RecursionError as error:
        raise LanguageError("limit", "Description or execution nesting is too deep") from error
