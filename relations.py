"""Explicit-parameter relations over a supplied program graph."""

from __future__ import annotations

from collections.abc import Callable, Mapping
from dataclasses import dataclass, field


class DefinitionError(ValueError):
    """The graph or relation specification is malformed."""


class ValidationError(ValueError):
    """A required relationship does not hold."""


@dataclass(frozen=True)
class Node:
    kind: str
    edges: Mapping[str, str] = field(default_factory=dict)


@dataclass(frozen=True)
class Call:
    relation: str
    arguments: tuple[str, ...]


@dataclass(frozen=True)
class Primitive:
    parameters: tuple[str, ...]
    check: Callable[[Mapping[str, Node], tuple[str, ...]], bool]


@dataclass(frozen=True)
class Composite:
    parameters: tuple[str, ...]
    cases: tuple[tuple[Call, ...], ...]


Definition = Primitive | Composite


class Validator:
    def __init__(
        self, graph: Mapping[str, Node], definitions: Mapping[str, Definition]
    ) -> None:
        self.graph = {
            name: Node(node.kind, dict(node.edges)) for name, node in graph.items()
        }
        self.definitions = dict(definitions)
        for name, node in self.graph.items():
            for label, target in node.edges.items():
                if target not in self.graph:
                    raise DefinitionError(
                        f"Node {name!r} edge {label!r} targets unknown node {target!r}"
                    )
        self._check_definitions()

    def _check_definitions(self) -> None:
        for name, definition in self.definitions.items():
            if len(set(definition.parameters)) != len(definition.parameters):
                raise DefinitionError(f"{name}: duplicate parameters")
            if isinstance(definition, Primitive):
                continue
            if not definition.cases or any(not case for case in definition.cases):
                raise DefinitionError(f"{name}: cases and conjunctions must be nonempty")
            for case in definition.cases:
                for call in case:
                    hidden = set(call.arguments) - set(definition.parameters)
                    if hidden:
                        raise DefinitionError(
                            f"{name}: hidden parameters {sorted(hidden)}"
                        )
                    self._check_call(call.relation, call.arguments)

        visited: set[str] = set()
        active: set[str] = set()

        def visit(name: str) -> None:
            if name in active:
                raise DefinitionError(f"Recursive relation dependency at {name}")
            if name in visited:
                return
            active.add(name)
            definition = self.definitions[name]
            if isinstance(definition, Composite):
                for case in definition.cases:
                    for call in case:
                        visit(call.relation)
            active.remove(name)
            visited.add(name)

        for name in self.definitions:
            visit(name)

    def _check_call(self, relation: str, arguments: tuple[str, ...]) -> None:
        if relation not in self.definitions:
            raise DefinitionError(f"Unknown relation {relation!r}")
        expected = len(self.definitions[relation].parameters)
        if len(arguments) != expected:
            raise DefinitionError(
                f"{relation}: expected {expected} arguments, got {len(arguments)}"
            )

    def require(self, relation: str, *arguments: str) -> None:
        """Validate one mandatory relation, raising on failure."""
        self._check_call(relation, arguments)
        for argument in arguments:
            if argument not in self.graph:
                raise DefinitionError(f"Unknown argument node {argument!r}")
        failure = self._failure(relation, arguments)
        if failure is not None:
            raise ValidationError(failure)

    def _failure(self, relation: str, arguments: tuple[str, ...]) -> str | None:
        definition = self.definitions[relation]
        label = f"{relation}({', '.join(arguments)})"
        if isinstance(definition, Primitive):
            result = definition.check(self.graph, arguments)
            if not isinstance(result, bool):
                raise TypeError(f"{relation}: primitive must return bool")
            return None if result else f"{label}: primitive check failed"

        bindings = dict(zip(definition.parameters, arguments))
        failures: list[str] = []
        for index, case in enumerate(definition.cases, start=1):
            for call in case:
                supplied = tuple(bindings[name] for name in call.arguments)
                failure = self._failure(call.relation, supplied)
                if failure is not None:
                    failures.append(f"case {index}: {failure}")
                    break
            else:
                return None
        return f"{label}: no case holds\n" + "\n".join(failures)
