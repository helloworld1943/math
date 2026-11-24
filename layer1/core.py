"""Graph-backed Layer 1 expressions and fixed primitive relations."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from types import MappingProxyType
from typing import TYPE_CHECKING

from node import Graph, GraphSnapshot, GraphView, Node, UnknownNodeError

from . import _calculus as calculus

if TYPE_CHECKING:
    from .inductive import InductiveBuilder


class EncodingError(ValueError):
    """The visible graph does not follow the Layer 1 encoding."""


_FIELDS = {
    "TypeNode": ("form",),
    "Universe": ("level",),
    "Variable": (),
    "Lambda": ("variable", "domain", "body"),
    "Application": ("function", "argument"),
    "Context": ("declarations",),
    "Parameters": ("entries", "context"),
    "Inductive": ("identity", "parameters", "type", "context", "body"),
    "InductiveBody": ("context",),
    "_Text": ("characters",),
    "Relation": ("kind", "first", "second"),
    "RelationAnd": ("operands",),
    "RelationOr": ("operands",),
    "_ListEnd": (),
    "_ListItem": ("value", "next"),
    "_NumberEnd": (),
    "_Bit0": ("next",),
    "_Bit1": ("next",),
}
_TYPE_FIELDS = {
    "function": ("variable", "domain", "codomain"),
    "variable": ("variable",),
    "application": ("expression",),
}
_PRIMITIVE_FIELDS = {
    "HasType": ("first", "second"),
    "BetaReduces": ("first", "second"),
    "ValidInductive": ("target",),
}
_PRIMITIVE_RELATIONS = tuple(_PRIMITIVE_FIELDS)
_COMBINATIONS = ("RelationAnd", "RelationOr")
_EXPRESSIONS = frozenset(
    ("TypeNode", "Universe", "Variable", "Lambda", "Application")
)
_RELATION_INPUTS = _EXPRESSIONS | {"Inductive"}


@dataclass(frozen=True)
class _Vocabulary:
    kinds: Mapping[str, Node]
    roles: Mapping[str, Node]
    relations: Mapping[str, Node]
    type_forms: Mapping[str, Node]


@dataclass(frozen=True)
class _Record:
    kind: str
    fields: Mapping[str, Node]
    form: str | None = None


@dataclass(frozen=True)
class _Plan:
    kind: str | None
    arguments: tuple[Node, ...]
    operands: tuple[Node, ...] = ()
    combination: str | None = None


class _Reader:
    def __init__(self, graph: GraphView, vocabulary: _Vocabulary) -> None:
        self.graph = graph
        self.vocabulary = vocabulary
        self._records: dict[Node, _Record] = {}
        self._active: set[Node] = set()
        self._constants: dict[Node, calculus.Constant] = {}
        self._validated_inductives: set[Node] = set()
        self._validating_inductives: set[Node] = set()

    def _leaf(self, marker: Node) -> None:
        if self.graph.children(marker):
            raise EncodingError("A Layer 1 marker must not have outgoing links")

    def record(self, node: Node) -> _Record:
        if node in self._records:
            return self._records[node]
        children = self.graph.children(node)
        kinds = [
            kind for kind, marker in self.vocabulary.kinds.items() if marker in children
        ]
        if len(kinds) != 1:
            raise EncodingError("A node must have exactly one recognized kind marker")
        kind = kinds[0]
        marker = self.vocabulary.kinds[kind]
        self._leaf(marker)
        fields: dict[str, Node] = {}
        for slot in children - {marker}:
            links = self.graph.children(slot)
            roles = [
                role for role, tag in self.vocabulary.roles.items() if tag in links
            ]
            if len(roles) != 1 or len(links) != 2:
                raise EncodingError("A field slot must link to one role and one value")
            role = roles[0]
            role_marker = self.vocabulary.roles[role]
            self._leaf(role_marker)
            if role in fields:
                raise EncodingError(f"Duplicate field role {role!r}")
            fields[role] = next(iter(links - {role_marker}))
        form = None
        expected = _FIELDS[kind]
        if kind == "TypeNode":
            forms = [
                name for name, tag in self.vocabulary.type_forms.items()
                if fields.get("form") is tag
            ]
            if len(forms) != 1:
                raise EncodingError("A TypeNode requires a recognized form")
            form = forms[0]
            self._leaf(self.vocabulary.type_forms[form])
            expected = ("form", *_TYPE_FIELDS[form])
        elif kind == "Relation":
            if "kind" in fields:
                rule = self.relation_kind(fields["kind"])
                expected = ("kind", *_PRIMITIVE_FIELDS[rule])
            else:
                expected = ("inputs", "decomposition")
        elif kind == "Variable" and fields:
            expected = ("context", "typing")
            if "name" in fields:
                expected += ("name",)
        elif kind == "Context":
            expected += tuple(role for role in ("parent", "definition") if role in fields)
        if set(fields) != set(expected):
            raise EncodingError(f"{kind} requires fields {expected}")
        result = _Record(kind, MappingProxyType(fields), form)
        self._records[node] = result
        return result

    def relation_kind(self, marker: Node | None) -> str:
        for name, known in self.vocabulary.relations.items():
            if marker is known:
                self._leaf(known)
                return name
        raise EncodingError("Unknown relation kind")

    def sequence(self, node: Node, work: calculus.Work) -> tuple[Node, ...]:
        values: list[Node] = []
        seen: set[Node] = set()
        while True:
            work.spend()
            if node in seen:
                raise EncodingError("An ordered input/operand list contains a cycle")
            seen.add(node)
            record = self.record(node)
            if record.kind == "_ListEnd":
                return tuple(values)
            if record.kind != "_ListItem":
                raise EncodingError("Expected an ordered input/operand list")
            values.append(record.fields["value"])
            node = record.fields["next"]

    def plans(self, root: Node, work: calculus.Work) -> dict[Node, _Plan]:
        plans: dict[Node, _Plan] = {}
        active: set[Node] = set()
        finished: set[Node] = set()
        owners: dict[Node, Node] = {}
        pending = [(root, False)]
        while pending:
            node, exiting = pending.pop()
            work.spend()
            if exiting:
                plan = plans[node]
                allowed = set(plan.arguments)
                for child in plan.operands:
                    if not set(plans[child].arguments) <= allowed:
                        raise EncodingError(
                            "A child Relation has inputs missing from its parent"
                        )
                active.remove(node)
                finished.add(node)
                continue
            if node in active:
                raise EncodingError("Relation decomposition contains a cycle")
            if node in finished:
                continue
            record = self.record(node)
            if record.kind != "Relation":
                raise EncodingError("Only a Relation can be a parent or operand")
            kind = None
            combination_kind = None
            operands: tuple[Node, ...] = ()
            if "decomposition" in record.fields:
                arguments = self.sequence(record.fields["inputs"], work)
                combination = record.fields["decomposition"]
                if combination in owners and owners[combination] is not node:
                    raise EncodingError("A combination must have one Relation owner")
                owners[combination] = node
                group = self.record(combination)
                if group.kind not in _COMBINATIONS:
                    raise EncodingError(
                        "A Relation decomposition requires RelationAnd or RelationOr"
                    )
                combination_kind = group.kind
                operands = self.sequence(group.fields["operands"], work)
                if not operands:
                    raise EncodingError("AND/OR combinations must be nonempty")
            else:
                kind = self.relation_kind(record.fields["kind"])
                arguments = tuple(record.fields[role] for role in _PRIMITIVE_FIELDS[kind])
            for argument in arguments:
                if self.record(argument).kind not in _RELATION_INPUTS:
                    raise EncodingError("A Relation input must be an expression or Inductive")
            plans[node] = _Plan(kind, arguments, operands, combination_kind)
            active.add(node)
            pending.append((node, True))
            pending.extend((child, False) for child in reversed(operands))
        return plans

    def level(self, node: Node, work: calculus.Work) -> int:
        record = self.record(node)
        if record.kind != "Universe":
            raise EncodingError("Expected a Universe node")
        current = record.fields["level"]
        seen: set[Node] = set()
        level = 0
        while True:
            work.spend()
            if current in seen:
                raise EncodingError("A Universe level must not contain a cycle")
            seen.add(current)
            digit = self.record(current)
            if digit.kind == "_NumberEnd":
                return level
            if digit.kind not in ("_Bit0", "_Bit1"):
                raise EncodingError("A Universe level requires a binary number")
            level = 2 * level + (digit.kind == "_Bit1")
            current = digit.fields["next"]

    def term(
        self, node: Node, work: calculus.Work, bound: tuple[Node, ...] = ()
    ) -> calculus.Term:
        work.spend()
        record = self.record(node)
        fields = record.fields
        if record.kind == "Universe":
            return calculus.Universe(self.level(node, work))
        if record.kind == "Variable":
            if node in bound:
                return calculus.Bound(bound.index(node))
            if fields:
                if node in self._constants:
                    return self._constants[node]
                context = self.record(fields["context"])
                if context.kind != "Context":
                    raise EncodingError("A Variable declaration must be owned by a Context")
                definition = context.fields.get("definition")
                if definition is not None:
                    self.validate_inductive(definition, work)
                    if node in self._constants:
                        return self._constants[node]
            if node not in bound:
                raise calculus.TypeCheckError(
                    f"Variable {node.number} is not bound by an enclosing expression"
                )
            return calculus.Bound(bound.index(node))
        if node in self._active:
            raise EncodingError("Expression structure contains a cycle")
        self._active.add(node)
        try:
            if record.kind == "TypeNode" and record.form in ("variable", "application"):
                role = "variable" if record.form == "variable" else "expression"
                target = fields[role]
                expected_kind = (
                    "Variable" if record.form == "variable" else "Application"
                )
                if self.record(target).kind != expected_kind:
                    raise EncodingError(
                        f"TypeNode form {record.form!r} must point to {expected_kind}"
                    )
                return calculus.TypeNode(
                    self.term(target, work, bound)
                )
            if record.kind == "Lambda" or (
                record.kind == "TypeNode" and record.form == "function"
            ):
                variable = fields["variable"]
                declaration = self.record(variable)
                if declaration.kind != "Variable":
                    raise EncodingError("A function binder must be a Variable")
                if "context" in declaration.fields and "definition" in self.record(
                    declaration.fields["context"]
                ).fields:
                    raise EncodingError("A declared inductive identity cannot be a function binder")
                if variable in bound:
                    raise EncodingError("Nested binders must use distinct identities")
                domain = self.term(fields["domain"], work, bound)
                child_bound = (variable, *bound)
                if record.kind == "Lambda":
                    return calculus.Lambda(
                        domain, self.term(fields["body"], work, child_bound)
                    )
                return calculus.Pi(
                    domain, self.term(fields["codomain"], work, child_bound)
                )
            if record.kind == "Application":
                return calculus.Application(
                    self.term(fields["function"], work, bound),
                    self.term(fields["argument"], work, bound),
                )
            raise EncodingError(f"{record.kind} is not an expression")
        finally:
            self._active.remove(node)

    def text(self, node: Node, work: calculus.Work) -> str:
        record = self.record(node)
        if record.kind != "_Text":
            raise EncodingError("Expected a name text node")
        characters = []
        for number in self.sequence(record.fields["characters"], work):
            value = self.level(number, work)
            if value > 0x10FFFF or 0xD800 <= value <= 0xDFFF:
                raise EncodingError("A name contains an invalid character")
            characters.append(chr(value))
        name = "".join(characters)
        if not name.isidentifier():
            raise EncodingError("A declaration name must be an identifier")
        return name

    def validate_inductive(self, node: Node, work: calculus.Work) -> None:
        from .inductive import validate_inductive

        declarations = _Reader(self.graph, self.vocabulary)
        declarations._constants = self._constants
        declarations._validated_inductives = self._validated_inductives
        declarations._validating_inductives = self._validating_inductives
        validate_inductive(declarations, node, work)


class View:
    """Read Layer 1 structure using only a Layer 0 view's visible nodes."""

    def __init__(self, graph: GraphView, vocabulary: _Vocabulary) -> None:
        self._graph = graph
        self._vocabulary = vocabulary
        self._reader = _Reader(graph, vocabulary)

    @property
    def nodes(self) -> frozenset[Node]:
        return self._graph.nodes

    def children(self, node: Node) -> frozenset[Node]:
        return self._graph.children(node)

    def kind(self, node: Node) -> str:
        return self._reader.record(node).kind

    def fields(self, node: Node) -> Mapping[str, Node]:
        return self._reader.record(node).fields

    def form(self, node: Node) -> str:
        form = self._reader.record(node).form
        if form is None:
            raise EncodingError("Only a TypeNode has a type form")
        return form

    def name(self, node: Node, *, max_steps: int = 10_000) -> str | None:
        record = self._reader.record(node)
        text = record.fields.get("name")
        return None if text is None else self._reader.text(text, calculus.Work(max_steps))

    def level(self, node: Node, *, max_steps: int = 10_000) -> int:
        return self._reader.level(node, calculus.Work(max_steps))

    def arguments(self, relation: Node, *, max_steps: int = 10_000) -> tuple[Node, ...]:
        work = calculus.Work(max_steps)
        record = self._reader.record(relation)
        if record.kind != "Relation":
            raise EncodingError("Only a Relation has relation inputs")
        if "decomposition" in record.fields:
            return self._reader.sequence(record.fields["inputs"], work)
        rule = self._reader.relation_kind(record.fields["kind"])
        return tuple(record.fields[role] for role in _PRIMITIVE_FIELDS[rule])

    def operands(self, combination: Node, *, max_steps: int = 10_000) -> tuple[Node, ...]:
        work = calculus.Work(max_steps)
        record = self._reader.record(combination)
        if record.kind not in _COMBINATIONS:
            raise EncodingError("Only a combination has relation operands")
        return self._reader.sequence(record.fields["operands"], work)

    def view(self, *arguments: Node) -> View:
        return View(self._graph.view(*arguments), self._vocabulary)

    def require(self, relation: Node, *, max_steps: int = 10_000) -> None:
        work = calculus.Work(max_steps)
        plans = self._reader.plans(relation, work)
        results: dict[Node, str | None] = {}
        pending: list[tuple[Node, int, tuple[str, ...]]] = [(relation, 0, ())]
        while pending:
            node, index, failures = pending.pop()
            work.spend()
            if node in results:
                continue
            plan = plans[node]
            if plan.combination is None:
                if plan.kind not in _PRIMITIVE_RELATIONS:
                    raise EncodingError("Unknown primitive relation kind")
                # Decomposition metadata grants no extra access to a primitive.
                reader = _Reader(self._graph.view(*plan.arguments), self._vocabulary)
                try:
                    if plan.kind == "ValidInductive":
                        reader.validate_inductive(plan.arguments[0], work)
                    else:
                        expression = reader.term(plan.arguments[0], work)
                        supplied = reader.term(plan.arguments[1], work)
                        if plan.kind == "HasType":
                            calculus.has_type(expression, supplied, work)
                        else:
                            calculus.beta_reduces(expression, supplied, work)
                except calculus.TypeCheckError as error:
                    results[node] = f"{plan.kind} (node {node.number}): {error}"
                else:
                    results[node] = None
                continue
            if index == len(plan.operands):
                results[node] = (
                    None if plan.combination == "RelationAnd"
                    else f"RelationOr (parent {node.number}): no alternative holds\n"
                    + "\n".join(failures)
                )
                continue
            child = plan.operands[index]
            if child not in results:
                pending.append((node, index, failures))
                pending.append((child, 0, ()))
                continue
            failure = results[child]
            if plan.combination == "RelationAnd" and failure is not None:
                results[node] = f"RelationAnd (parent {node.number}): {failure}"
            elif plan.combination == "RelationOr" and failure is None:
                results[node] = None
            else:
                pending.append((
                    node, index + 1,
                    failures if failure is None else (*failures, failure),
                ))
        failure = results[relation]
        if failure is not None:
            raise calculus.TypeCheckError(failure)

    def check(self, relation: Node, *, max_steps: int = 10_000) -> bool:
        try:
            self.require(relation, max_steps=max_steps)
        except calculus.TypeCheckError:
            return False
        return True


class Snapshot:
    def __init__(self, graph: GraphSnapshot, vocabulary: _Vocabulary) -> None:
        self.graph = graph
        self._vocabulary = vocabulary

    @property
    def root(self) -> Node:
        return self.graph.root

    def view(self, *arguments: Node) -> View:
        return View(self.graph.view(*arguments), self._vocabulary)

    def require(self, relation: Node, *, max_steps: int = 10_000) -> None:
        self.view(relation).require(relation, max_steps=max_steps)

    def check(self, relation: Node, *, max_steps: int = 10_000) -> bool:
        return self.view(relation).check(relation, max_steps=max_steps)


class Program:
    """Construct Layer 1 nodes in an ordinary Layer 0 graph."""

    def __init__(self) -> None:
        self.graph = Graph()
        kinds = {name: self._node() for name in _FIELDS}
        roles = {
            name: self._node()
            for name in sorted({
                role for fields in (*_FIELDS.values(), *_TYPE_FIELDS.values())
                for role in fields
            } | {"inputs", "decomposition", "typing", "name", "parent", "definition", "target"})
        }
        relations = {name: self._node() for name in _PRIMITIVE_RELATIONS}
        type_forms = {name: self._node() for name in _TYPE_FIELDS}
        self._vocabulary = _Vocabulary(
            MappingProxyType(kinds), MappingProxyType(roles),
            MappingProxyType(relations), MappingProxyType(type_forms),
        )
        self._kinds: dict[Node, str] = {}
        self._universes: dict[int, Node] = {}
        self._relation_inputs: dict[Node, tuple[Node, ...]] = {}

    def _node(self) -> Node:
        node = self.graph.create_node()
        self.graph.add_link(self.graph.root, node)
        return node

    def _record(self, node_kind: str, **fields: Node) -> Node:
        node = self._node()
        self.graph.add_link(node, self._vocabulary.kinds[node_kind])
        self._fields(node, **fields)
        self._kinds[node] = node_kind
        return node

    def _fields(self, node: Node, **fields: Node) -> None:
        for role, value in fields.items():
            slot = self._node()
            self.graph.add_link(node, slot)
            self.graph.add_link(slot, self._vocabulary.roles[role])
            self.graph.add_link(slot, value)

    def _expression(self, node: Node) -> None:
        if node not in self._kinds:
            raise UnknownNodeError("The expression does not belong to this Program")
        if self._kinds[node] not in _EXPRESSIONS:
            raise EncodingError("Expected an expression node")

    def universe(self, n: int) -> Node:
        if type(n) is not int or n < 0:
            raise ValueError("A Universe level must be a non-negative integer")
        if n not in self._universes:
            number = self._record("_NumberEnd")
            if n:
                for bit in reversed(bin(n)[2:]):
                    number = self._record(f"_Bit{bit}", next=number)
            self._universes[n] = self._record("Universe", level=number)
        return self._universes[n]

    def variable(self) -> Node:
        """Create a fresh binder identity, also used for references to it."""
        return self._record("Variable")

    def type_node(self, expression: Node) -> Node:
        """Describe a Variable/Application; reuse TypeNode/Universe directly."""
        self._expression(expression)
        kind = self._kinds[expression]
        if kind in ("Universe", "TypeNode"):
            return expression
        if kind == "Variable":
            return self._record(
                "TypeNode", form=self._vocabulary.type_forms["variable"],
                variable=expression,
            )
        if kind == "Application":
            return self._record(
                "TypeNode", form=self._vocabulary.type_forms["application"],
                expression=expression,
            )
        raise EncodingError(
            "A Lambda is a function value, not a TypeNode description"
        )

    def _binder(self, variable: Node, domain: Node, body: Node) -> None:
        for node in (variable, domain, body):
            self._expression(node)
        if self._kinds[variable] != "Variable":
            raise EncodingError("A function binder must be a Variable")

    def lambda_(self, variable: Node, domain: Node, body: Node) -> Node:
        self._binder(variable, domain, body)
        return self._record("Lambda", variable=variable, domain=domain, body=body)

    def function_type(self, variable: Node, domain: Node, codomain: Node) -> Node:
        """Create TypeNode(form='function'), not a separate FunctionType node."""
        self._binder(variable, domain, codomain)
        return self._record(
            "TypeNode", form=self._vocabulary.type_forms["function"],
            variable=variable, domain=domain, codomain=codomain,
        )

    def apply(self, function: Node, argument: Node) -> Node:
        self._expression(function)
        self._expression(argument)
        return self._record("Application", function=function, argument=argument)

    def relation(self, kind: str, *arguments: Node) -> Node:
        if kind not in _PRIMITIVE_RELATIONS:
            raise EncodingError(f"Unknown relation kind {kind!r}")
        roles = _PRIMITIVE_FIELDS[kind]
        if len(arguments) != len(roles):
            count = "two" if len(roles) == 2 else "one"
            raise EncodingError(f"{kind} requires exactly {count} arguments")
        for argument in arguments:
            if kind == "ValidInductive":
                if self._kinds.get(argument) != "Inductive":
                    raise EncodingError("ValidInductive requires an Inductive node")
            else:
                self._expression(argument)
        node = self._record(
            "Relation", kind=self._vocabulary.relations[kind],
            **dict(zip(roles, arguments)),
        )
        self._relation_inputs[node] = arguments
        return node

    def _sequence(self, values: tuple[Node, ...]) -> Node:
        node = self._record("_ListEnd")
        for value in reversed(values):
            node = self._record("_ListItem", value=value, next=node)
        return node

    def _combination(
        self, kind: str, arguments: tuple[Node, ...], relations: tuple[Node, ...]
    ) -> Node:
        for argument in arguments:
            if self._kinds.get(argument) != "Inductive":
                self._expression(argument)
        if not relations:
            raise EncodingError("AND/OR combinations must be nonempty")
        allowed = set(arguments)
        for child in relations:
            if child not in self._relation_inputs:
                raise EncodingError("Combination operands must be this Program's Relations")
            if not set(self._relation_inputs[child]) <= allowed:
                raise EncodingError("A child Relation has inputs missing from its parent")
        group = self._record(
            kind, operands=self._sequence(relations)
        )
        node = self._record(
            "Relation", inputs=self._sequence(arguments), decomposition=group,
        )
        self._relation_inputs[node] = arguments
        return node

    def all_of(self, *arguments: Node, relations: tuple[Node, ...]) -> Node:
        """Create a Relation owning a nonempty RelationAnd decomposition."""
        return self._combination("RelationAnd", arguments, relations)

    def any_of(self, *arguments: Node, relations: tuple[Node, ...]) -> Node:
        """Create a Relation owning a nonempty RelationOr decomposition."""
        return self._combination("RelationOr", arguments, relations)

    def inductive(
        self, name: str, universe: Node, *,
        parameters: tuple[tuple[Node, Node], ...] = (),
    ) -> InductiveBuilder:
        """Stage an inductive declaration; finish after adding constructors."""
        from .inductive import InductiveBuilder

        return InductiveBuilder(self, name, universe, parameters)

    def commit(self) -> Snapshot:
        """Commit the Layer 0 graph, not an assertion that all Relations hold."""
        return Snapshot(self.graph.commit(), self._vocabulary)
