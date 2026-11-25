"""Tokenizer, graph composers, semantic checker, and bounded Nod interpreter."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Literal

from lark import Lark, Token, Transformer, Tree, UnexpectedInput
from lark.exceptions import VisitError

from node import Graph, GraphSnapshot, Node


Type = Literal["int", "bool"]
Value = int | bool
MAX_SOURCE = 32_000
MAX_NODES = 12_000
MAX_STEPS = 20_000


class LanguageError(ValueError):
    def __init__(self, stage: str, message: str, line: int = 1, column: int = 1) -> None:
        self.stage, self.message = stage, message
        self.line, self.column = line, column
        super().__init__(f"{stage} at {line}:{column}: {message}")

    def as_dict(self) -> dict[str, object]:
        return {
            "stage": self.stage, "message": self.message,
            "line": self.line, "column": self.column,
        }


@dataclass(frozen=True)
class Description:
    kind: str
    children: tuple[Node, ...]
    slots: tuple[int, ...]
    line: int
    column: int
    token: bool = False


@dataclass(frozen=True)
class Program:
    graph: GraphSnapshot
    final: Node
    descriptions: dict[Node, Description]
    tokens: tuple[Node, ...]

    def description(self, node: Node) -> Description:
        return self.descriptions[node]

    def text(self, node: Node) -> str:
        if node.value is None:
            raise ValueError("This description is not an information-bearing token")
        return node.value.decode("utf-8")

    def name(self, node: Node) -> str:
        return self.text(self.description(node).children[0])

    def fail(self, stage: str, node: Node, message: str) -> LanguageError:
        info = self.description(node)
        return LanguageError(stage, message, info.line, info.column)


class Composer(Transformer):
    """LALR reductions call this constructor; no separate parse tree is built."""

    def __init__(self) -> None:
        super().__init__()
        self.graph = Graph()
        self.descriptions: dict[Node, Description] = {
            self.graph.root: Description("Root", (), (), 1, 1),
        }
        self.by_position: dict[int, Node] = {}
        self.tokens: list[Node] = []
        self.cache: dict[tuple[str, tuple[Node, ...]], Node] = {}

    def token(self, token: Token) -> None:
        node = self.graph.create_node(value=str(token).encode("utf-8"))
        self.graph.edit_link(node, 0, self.graph.root)
        self.descriptions[node] = Description(
            str(token.type), (), (), token.line or 1, token.column or 1, True,
        )
        self.by_position[token.start_pos] = node
        self.tokens.append(node)

    def compose(self, kind: str, children: tuple[Node, ...]) -> Node:
        key = kind, children
        if key in self.cache:
            return self.cache[key]
        if len(self.descriptions) >= MAX_NODES:
            raise LanguageError("limit", "Description graph is too large")
        targets = tuple(dict.fromkeys((self.graph.root, *children)))
        node = self.graph.create_node(len(targets))
        for slot, target in enumerate(targets):
            self.graph.edit_link(node, slot, target)
        first = next(
            (self.descriptions[child] for child in children
             if self.descriptions[child].token or self.descriptions[child].children),
            self.descriptions[self.graph.root],
        )
        self.descriptions[node] = Description(
            kind, children, tuple(targets.index(child) for child in children),
            first.line, first.column,
        )
        self.cache[key] = node
        return node

    def __default__(self, data, children, meta):
        if str(data).startswith("__"):
            return Tree(data, children)
        return self.compose(str(data), tuple(
            self.by_position[child.start_pos] if isinstance(child, Token) else child
            for child in children
        ))


GRAMMAR = Path(__file__).with_name("grammar.lark").read_text("utf-8")


def make_parser(composer: Composer | None = None) -> Lark:
    return Lark(
        GRAMMAR, parser="lalr", lexer="basic", transformer=composer,
        maybe_placeholders=False, start="start",
    )


def build_description(source: str, *, syntax: bool) -> Program:
    if not isinstance(source, str):
        raise LanguageError("input", "Source must be text")
    if len(source) > MAX_SOURCE:
        raise LanguageError("limit", f"Source exceeds {MAX_SOURCE} characters")
    composer = Composer()
    parser = make_parser(composer)
    try:
        depth = 0
        tokens = []
        for token in parser.lex(source):
            if len(composer.tokens) >= 5000:
                raise LanguageError("limit", "Too many tokens", token.line, token.column)
            if token.type == "INTEGER" and len(str(token)) > 256:
                raise LanguageError("limit", "Integer literal exceeds 256 digits", token.line, token.column)
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
                raise TypeError("Grammar actions must produce a final Node")
        sequence = composer.compose("TokenSequence", tuple(composer.tokens))
        final = composer.compose("Program", (syntax_node, sequence)) if syntax else sequence
        return Program(composer.graph.commit(), final, composer.descriptions, tuple(composer.tokens))
    except UnexpectedInput as error:
        context = error.get_context(source, span=35).strip()
        stage = "tokenizer" if type(error).__name__ == "UnexpectedCharacters" else "syntax"
        raise LanguageError(stage, f"Unexpected input. {context}", max(1, error.line), max(1, error.column)) from error
    except VisitError as error:
        if isinstance(error.orig_exc, LanguageError):
            raise error.orig_exc from error
        raise


def tokenize(source: str) -> Program:
    """Produce token nodes without requiring a grammatical or well-typed program."""
    return build_description(source, syntax=False)


def parse(source: str) -> Program:
    return build_description(source, syntax=True)


@dataclass(frozen=True)
class Signature:
    node: Node
    parameters: tuple[tuple[str, Type], ...]
    result: Type
    body: Node


class Checker:
    def __init__(self, program: Program) -> None:
        self.program = program
        self.functions: dict[str, Signature] = {}
        self.types: dict[Node, Type] = {}
        self.bindings: dict[Node, Node] = {}
        self.scopes: list[dict[str, tuple[Type, Node]]] = [{}]
        self.expected_return: Type | None = None

    def children(self, node: Node) -> tuple[Node, ...]:
        return self.program.description(node).children

    def declared_type(self, node: Node) -> Type:
        kind = self.program.description(node).kind
        if kind == "int_type":
            return "int"
        if kind == "bool_type":
            return "bool"
        raise self.program.fail("type", node, "Expected int or bool")

    def lookup(self, name: str, node: Node) -> tuple[Type, Node]:
        for scope in reversed(self.scopes):
            if name in scope:
                return scope[name]
        raise self.program.fail("type", node, f"Unknown variable '{name}'")

    def require(self, actual: Type, expected: Type, node: Node) -> None:
        if actual != expected:
            raise self.program.fail("type", node, f"Expected {expected}, got {actual}")

    def expression(self, node: Node) -> Type:
        info = self.program.description(node)
        args, kind = info.children, info.kind
        if kind == "integer":
            result: Type = "int"
        elif kind == "boolean":
            result = "bool"
        elif kind == "variable":
            result, declaration = self.lookup(self.program.name(args[0]), node)
            self.bindings[node] = declaration
        elif kind == "call":
            name = self.program.name(args[0])
            if any(name in scope for scope in self.scopes):
                raise self.program.fail("type", node, f"Variable '{name}' is not callable")
            if name not in self.functions:
                raise self.program.fail("type", node, f"Unknown function '{name}'")
            function = self.functions[name]
            values = self.children(args[1])
            if len(values) != len(function.parameters):
                raise self.program.fail(
                    "type", node, f"'{name}' expects {len(function.parameters)} arguments, got {len(values)}",
                )
            for value, (_, expected) in zip(values, function.parameters):
                self.require(self.expression(value), expected, value)
            self.bindings[node] = function.node
            result = function.result
        elif kind == "unary":
            operator = self.program.text(args[0])
            result = "bool" if operator == "!" else "int"
            self.require(self.expression(args[1]), result, node)
        elif kind == "binary":
            left, right = self.expression(args[0]), self.expression(args[2])
            operator = self.program.text(args[1])
            if operator in ("|", "||", "&", "&&"):
                self.require(left, "bool", args[0])
                self.require(right, "bool", args[2])
                result = "bool"
            elif operator in ("==", "!="):
                self.require(right, left, args[2])
                result = "bool"
            else:
                self.require(left, "int", args[0])
                self.require(right, "int", args[2])
                result = "bool" if operator in ("<", ">", "<=", ">=") else "int"
        else:
            raise self.program.fail("type", node, f"Not an expression: {kind}")
        self.types[node] = result
        return result

    def block(self, node: Node) -> bool:
        self.scopes.append({})
        try:
            returns = False
            for statement in self.children(node):
                current = self.statement(statement)
                returns = returns or current
            return returns
        finally:
            self.scopes.pop()

    def statement(self, node: Node) -> bool:
        info = self.program.description(node)
        args, kind = info.children, info.kind
        if kind == "declaration":
            declared, name = self.declared_type(args[0]), self.program.name(args[1])
            if name in self.scopes[-1] or (len(self.scopes) == 1 and name in self.functions):
                raise self.program.fail("type", node, f"Duplicate declaration '{name}'")
            self.require(self.expression(args[2]), declared, args[2])
            self.scopes[-1][name] = declared, node
            self.types[node] = declared
        elif kind == "assignment":
            declared, declaration = self.lookup(self.program.name(args[0]), node)
            self.require(self.expression(args[1]), declared, args[1])
            self.bindings[node] = declaration
        elif kind in ("print_stmt", "expression_statement"):
            self.expression(args[0])
        elif kind == "return_stmt":
            if self.expected_return is None:
                raise self.program.fail("type", node, "return is only allowed inside a function")
            self.require(self.expression(args[0]), self.expected_return, node)
            return True
        elif kind == "if_stmt":
            self.require(self.expression(args[0]), "bool", args[0])
            yes = self.block(args[1])
            no = self.block(args[2]) if len(args) == 3 else False
            return yes and no
        elif kind == "while_stmt":
            self.require(self.expression(args[0]), "bool", args[0])
            self.block(args[1])
        else:
            raise self.program.fail("type", node, f"Not a statement: {kind}")
        return False

    def check(self) -> None:
        syntax = self.children(self.program.final)[0]
        items = self.children(syntax)
        for item in items:
            if self.program.description(item).kind != "function":
                continue
            name_node, parameters, result, body = self.children(item)
            name = self.program.name(name_node)
            if name in self.functions:
                raise self.program.fail("type", item, f"Duplicate function '{name}'")
            params: list[tuple[str, Type]] = []
            seen: set[str] = set()
            for parameter in self.children(parameters):
                param_type, param_name = self.children(parameter)
                spelling = self.program.name(param_name)
                if spelling in seen:
                    raise self.program.fail("type", parameter, f"Duplicate parameter '{spelling}'")
                seen.add(spelling)
                params.append((spelling, self.declared_type(param_type)))
            self.functions[name] = Signature(item, tuple(params), self.declared_type(result), body)
        for item in items:
            if self.program.description(item).kind != "function":
                self.statement(item)
        for function in self.functions.values():
            saved = self.scopes
            self.scopes = [{}]
            self.expected_return = function.result
            try:
                for parameter, (name, kind) in zip(
                    self.children(self.children(function.node)[1]), function.parameters,
                ):
                    self.scopes[-1][name] = kind, parameter
                returns = False
                for statement in self.children(function.body):
                    returns = self.statement(statement) or returns
                if not returns:
                    raise self.program.fail("type", function.node, "Function must return a value on every path")
            finally:
                self.scopes = saved
                self.expected_return = None


class Returned(Exception):
    def __init__(self, value: Value) -> None:
        self.value = value


class Runtime:
    def __init__(self, checker: Checker) -> None:
        self.checker, self.program = checker, checker.program
        self.scopes: list[dict[str, Value]] = [{}]
        self.output: list[str] = []
        self.steps = 0
        self.depth = 0

    def tick(self, node: Node) -> None:
        self.steps += 1
        if self.steps > MAX_STEPS:
            raise self.program.fail("runtime", node, f"Execution exceeded {MAX_STEPS} steps")

    def frame(self, name: str) -> dict[str, Value]:
        for scope in reversed(self.scopes):
            if name in scope:
                return scope
        raise RuntimeError(f"Checker/runtime binding disagreement for {name}")

    def expression(self, node: Node) -> Value:
        self.tick(node)
        info = self.program.description(node)
        args, kind = info.children, info.kind
        if kind == "integer":
            value: Value = int(self.program.text(args[0]))
        elif kind == "boolean":
            value = self.program.text(args[0]) == "true"
        elif kind == "variable":
            name = self.program.name(args[0])
            value = self.frame(name)[name]
        elif kind == "call":
            function = self.checker.functions[self.program.name(args[0])]
            values = [self.expression(arg) for arg in self.program.description(args[1]).children]
            self.depth += 1
            if self.depth > 64:
                raise self.program.fail("runtime", node, "Function call depth exceeded 64")
            saved = self.scopes
            self.scopes = [dict(zip((name for name, _ in function.parameters), values))]
            try:
                for statement in self.program.description(function.body).children:
                    self.statement(statement)
            except Returned as result:
                value = result.value
            else:
                raise RuntimeError("Checked function finished without returning")
            finally:
                self.scopes = saved
                self.depth -= 1
        elif kind == "unary":
            operator, operand = self.program.text(args[0]), self.expression(args[1])
            value = not operand if operator == "!" else -operand if operator == "-" else operand
        elif kind == "binary":
            operator = self.program.text(args[1])
            left = self.expression(args[0])
            if operator == "&&" and not left:
                return False
            if operator == "||" and left:
                return True
            right = self.expression(args[2])
            if operator in ("&&", "&"):
                value = bool(left and right)
            elif operator in ("||", "|"):
                value = bool(left or right)
            elif operator == "+":
                value = left + right
            elif operator == "-":
                value = left - right
            elif operator == "*":
                value = left * right
            elif operator in ("/", "%"):
                if right == 0:
                    raise self.program.fail("runtime", node, "Division by zero")
                quotient = abs(left) // abs(right)
                if (left < 0) != (right < 0):
                    quotient = -quotient
                value = quotient if operator == "/" else left - quotient * right
            elif operator == "==":
                value = left == right
            elif operator == "!=":
                value = left != right
            elif operator == "<":
                value = left < right
            elif operator == ">":
                value = left > right
            elif operator == "<=":
                value = left <= right
            elif operator == ">=":
                value = left >= right
            else:
                raise RuntimeError(f"Unknown checked operator {operator}")
        else:
            raise RuntimeError(f"Unknown checked expression {kind}")
        if isinstance(value, int) and value.bit_length() > 4096:
            raise self.program.fail("runtime", node, "Integer result exceeds 4096 bits")
        return value

    def block(self, node: Node) -> None:
        self.scopes.append({})
        try:
            for statement in self.program.description(node).children:
                self.statement(statement)
        finally:
            self.scopes.pop()

    def statement(self, node: Node) -> None:
        self.tick(node)
        info = self.program.description(node)
        args, kind = info.children, info.kind
        if kind == "declaration":
            self.scopes[-1][self.program.name(args[1])] = self.expression(args[2])
        elif kind == "assignment":
            name = self.program.name(args[0])
            self.frame(name)[name] = self.expression(args[1])
        elif kind == "print_stmt":
            value = self.expression(args[0])
            self.output.append(str(value).lower() if isinstance(value, bool) else str(value))
        elif kind == "return_stmt":
            raise Returned(self.expression(args[0]))
        elif kind == "expression_statement":
            self.expression(args[0])
        elif kind == "if_stmt":
            if self.expression(args[0]):
                self.block(args[1])
            elif len(args) == 3:
                self.block(args[2])
        elif kind == "while_stmt":
            while self.expression(args[0]):
                self.block(args[1])
        else:
            raise RuntimeError(f"Unknown checked statement {kind}")

    def run(self) -> None:
        syntax = self.program.description(self.program.final).children[0]
        for item in self.program.description(syntax).children:
            if self.program.description(item).kind != "function":
                self.statement(item)


def run_source(source: str) -> dict[str, object]:
    """Return only a fully parsed, checked and successfully executed proposal."""
    try:
        program = parse(source)
        checker = Checker(program)
        checker.check()
        runtime = Runtime(checker)
        runtime.run()
    except RecursionError as error:
        raise LanguageError("limit", "Description or execution nesting is too deep") from error
    return {
        **export_program(program, checker),
        "output": runtime.output, "steps": runtime.steps,
        "variables": runtime.scopes[0],
        "functions": [
            {"name": name, "parameters": list(signature.parameters), "returns": signature.result}
            for name, signature in checker.functions.items()
        ],
    }


def export_program(program: Program, checker: Checker | None = None) -> dict[str, object]:
    return {
        "final": program.final.number,
        "tokens": [node.number for node in program.tokens],
        "nodes": [
            {
                "id": node.number, "position": program.graph.position(node),
                "kind": info.kind, "token": info.token,
                "value": list(node.value) if node.value is not None else None,
                "text": node.value.decode("utf-8") if node.value is not None else None,
                "line": info.line, "column": info.column,
                "outputs": [
                    None if target is None else target.number
                    for target in (
                        program.graph.get_output(node, slot)
                        for slot in range(program.graph.get_output_count(node))
                    )
                ],
                "children": [child.number for child in info.children],
                "childSlots": list(info.slots),
                "type": checker.types.get(node) if checker is not None else None,
                "binding": checker.bindings[node].number
                if checker is not None and node in checker.bindings else None,
            }
            for node in program.graph.node_order
            for info in (program.description(node),)
        ],
    }


def inspect_stage(source: str, *, syntax: bool) -> dict[str, object]:
    try:
        return export_program(parse(source) if syntax else tokenize(source))
    except RecursionError as error:
        raise LanguageError("limit", "Description nesting is too deep") from error
