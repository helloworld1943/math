"""Staged inductive declarations and checks for a small positive fragment."""

from __future__ import annotations

from layer0 import Node

from . import _calculus as c
from .core import EncodingError, Program, _Reader


class UnsupportedInductiveError(NotImplementedError):
    """A declaration needs inductive features outside the implemented fragment."""


class InductiveBuilder:
    def __init__(
        self, program: Program, name: str, universe: Node,
        parameters: tuple[tuple[Node, Node], ...],
    ) -> None:
        if not isinstance(name, str) or not name.isidentifier():
            raise ValueError("An inductive name must be an identifier")
        program._expression(universe)
        if program._kinds[universe] != "Universe":
            raise EncodingError("This fragment requires a Universe result")
        seen: set[Node] = set()
        for variable, type_node in parameters:
            program._binder(variable, type_node, type_node)
            if variable in seen:
                raise EncodingError("Inductive parameters must have distinct identities")
            if program.graph.commit().children(variable) != frozenset(
                (program._vocabulary.kinds["Variable"],)
            ):
                raise EncodingError("A parameter is already a declared Variable")
            seen.add(variable)
        self.program = program
        self.node = program._record("Inductive")
        self.identity = program.variable()
        self.parameters = parameters
        self.universe = universe
        self.name = name
        self._constructors: list[tuple[str, Node, Node]] = []
        self._finished = False

    def constructor(self, name: str, signature: Node) -> Node:
        """Introduce a constructor identity; its signature excludes shared parameters."""
        if self._finished:
            raise ValueError("This inductive declaration is already finished")
        if not isinstance(name, str) or not name.isidentifier():
            raise ValueError("A constructor name must be an identifier")
        if any(existing == name for existing, _, _ in self._constructors):
            raise ValueError(f"Duplicate constructor name {name!r}")
        self.program._expression(signature)
        identity = self.program.variable()
        self._constructors.append((name, identity, signature))
        return identity

    def _telescope(self, result: Node) -> Node:
        for variable, type_node in reversed(self.parameters):
            result = self.program.function_type(variable, type_node, result)
        return result

    def _text(self, name: str) -> Node:
        p = self.program
        return p._record(
            "_Text", characters=p._sequence(tuple(p.universe(ord(char)) for char in name))
        )

    def _declare(
        self, variable: Node, context: Node, type_node: Node, name: str | None = None
    ) -> None:
        typing = self.program.relation("HasType", variable, type_node)
        fields = {"context": context, "typing": typing}
        if name is not None:
            fields["name"] = self._text(name)
        self.program._fields(variable, **fields)

    def finish(self) -> Node:
        """Finish the graph structure. Validation is a separate relation check."""
        if self._finished:
            raise ValueError("This inductive declaration is already finished")
        p = self.program
        for variable, _ in self.parameters:
            if p.graph.commit().children(variable) != frozenset(
                (p._vocabulary.kinds["Variable"],)
            ):
                raise EncodingError("A parameter is already a declared Variable")
        parameter_context = p._record(
            "Context", declarations=p._sequence(tuple(v for v, _ in self.parameters))
        )
        parameters_node = p._record(
            "Parameters", context=parameter_context,
            entries=p._sequence(tuple(v for v, _ in self.parameters)),
        )
        declaration_context = p._record(
            "Context", declarations=p._sequence((self.identity,)),
            definition=self.node,
        )
        constructor_context = p._record(
            "Context", parent=parameter_context, definition=self.node,
            declarations=p._sequence(tuple(v for _, v, _ in self._constructors)),
        )
        body = p._record("InductiveBody", context=constructor_context)
        full_type = self._telescope(self.universe)
        for variable, type_node in self.parameters:
            self._declare(variable, parameter_context, type_node)
        self._declare(self.identity, declaration_context, full_type, self.name)
        for name, variable, signature in self._constructors:
            self._declare(
                variable, constructor_context, self._telescope(signature), name
            )
        p._fields(
            self.node, identity=self.identity, parameters=parameters_node,
            type=full_type, context=declaration_context, body=body,
        )
        self._finished = True
        return self.node


def _declaration(
    reader: _Reader, variable: Node, context: Node, work: c.Work
) -> Node:
    work.spend()
    record = reader.record(variable)
    if record.kind != "Variable" or record.fields.get("context") is not context:
        raise EncodingError("A declared identity must be a Variable owned by its Context")
    typing = reader.record(record.fields["typing"])
    if (
        typing.kind != "Relation"
        or reader.relation_kind(typing.fields.get("kind")) != "HasType"
        or typing.fields.get("first") is not variable
    ):
        raise EncodingError("A declaration must have HasType pointing to that identity")
    if "name" in record.fields:
        reader.text(record.fields["name"], work)
    return typing.fields["second"]


def _context(reader: _Reader, node: Node, work: c.Work) -> tuple[Node, ...]:
    record = reader.record(node)
    if record.kind != "Context":
        raise EncodingError("Expected a declaration Context")
    declarations = reader.sequence(record.fields["declarations"], work)
    if len(set(declarations)) != len(declarations):
        raise EncodingError("A Context contains duplicate declaration identities")
    return declarations


def _occurs(term: c.Term, identity: Node, work: c.Work) -> bool:
    work.spend()
    if isinstance(term, c.Constant):
        return term.identity is identity
    if isinstance(term, (c.Universe, c.Bound)):
        return False
    if isinstance(term, c.TypeNode):
        return _occurs(term.expression, identity, work)
    if isinstance(term, (c.Lambda, c.Pi)):
        body = term.body if isinstance(term, c.Lambda) else term.codomain
        return _occurs(term.domain, identity, work) or _occurs(body, identity, work)
    return _occurs(term.function, identity, work) or _occurs(term.argument, identity, work)


def _result_arguments(
    term: c.Term, identity: Node, expected: tuple[c.Term, ...], work: c.Work
) -> bool:
    arguments = []
    term = c.normalize(term, work)
    while isinstance(term, c.Application):
        arguments.append(term.argument)
        term = term.function
    return (
        isinstance(term, c.Constant)
        and term.identity is identity
        and len(arguments) == len(expected)
        and all(
            c.definitionally_equal(actual, wanted, work)
            for actual, wanted in zip(reversed(arguments), expected)
        )
    )


def validate_inductive(reader: _Reader, node: Node, work: c.Work) -> None:
    """Check a declaration before treating any of its identities as constants."""
    work.spend()
    if node in reader._validated_inductives:
        return
    if node in reader._validating_inductives:
        raise c.TypeCheckError("Circular declaration dependency is not a constructor proof")
    reader._validating_inductives.add(node)
    installed: list[Node] = []
    succeeded = False
    try:
        record = reader.record(node)
        if record.kind != "Inductive":
            raise EncodingError("ValidInductive requires an Inductive declaration")
        fields = record.fields
        identity = fields["identity"]
        declaration_context = fields["context"]
        if _context(reader, declaration_context, work) != (identity,):
            raise EncodingError("The inductive Context must declare its type identity")
        if reader.record(declaration_context).fields.get("definition") is not node:
            raise EncodingError("The type Context must identify its inductive definition")
        parameters = reader.record(fields["parameters"])
        if parameters.kind != "Parameters":
            raise EncodingError("An Inductive requires Parameters")
        entries = reader.sequence(parameters.fields["entries"], work)
        parameter_context = parameters.fields["context"]
        if _context(reader, parameter_context, work) != entries:
            raise EncodingError("Parameters and their Context must list the same declarations")
        if set(reader.record(parameter_context).fields) != {"declarations"}:
            raise UnsupportedInductiveError("External parameter Contexts are not implemented")
        if identity in entries:
            raise EncodingError("The type identity cannot be its own parameter")

        bound: tuple[Node, ...] = ()
        environment: tuple[c.Term, ...] = ()
        domains: list[c.Term] = []
        for variable in entries:
            signature = _declaration(reader, variable, parameter_context, work)
            domain = reader.term(signature, work, bound)
            if not isinstance(c.normalize(c.infer(domain, environment, work), work), c.Universe):
                raise c.TypeCheckError("A parameter declaration must have a valid type")
            domains.append(domain)
            bound = (variable, *bound)
            environment = (domain, *environment)

        if _declaration(reader, identity, declaration_context, work) is not fields["type"]:
            raise EncodingError("The inductive signature and its declared type must agree")
        header_type = reader.term(fields["type"], work)
        header = header_type
        for domain in domains:
            if not isinstance(header, c.Pi) or not c.definitionally_equal(
                header.domain, domain, work
            ):
                raise EncodingError("The inductive signature must bind its declared parameters")
            header = header.codomain
        if not isinstance(header, c.Universe):
            raise UnsupportedInductiveError("Indexed inductive signatures are not implemented")
        result_level = header.level
        c.infer(header_type, (), work)
        reader._constants[identity] = c.Constant(identity, header_type)
        installed.append(identity)

        body = reader.record(fields["body"])
        if body.kind != "InductiveBody":
            raise EncodingError("An Inductive requires an InductiveBody")
        constructor_context = body.fields["context"]
        context = reader.record(constructor_context)
        if (
            context.kind != "Context"
            or context.fields.get("parent") is not parameter_context
            or context.fields.get("definition") is not node
        ):
            raise EncodingError("The body Context must identify the definition and parameters")
        constructors = _context(reader, constructor_context, work)
        if set(constructors) & ({identity} | set(entries)):
            raise EncodingError("Constructor identities must be distinct from type and parameters")
        names: set[str] = set()
        signatures: list[tuple[Node, c.Term]] = []
        for constructor in constructors:
            signature_node = _declaration(reader, constructor, constructor_context, work)
            name_node = reader.record(constructor).fields.get("name")
            if name_node is None:
                raise EncodingError("A constructor declaration requires a name")
            name = reader.text(name_node, work)
            if name in names:
                raise EncodingError("Constructor names must be unique within the body Context")
            names.add(name)
            signature = reader.term(signature_node, work)
            c.infer(signature, (), work)
            remaining = c.normalize(signature, work)
            ctor_environment: tuple[c.Term, ...] = ()
            for domain in domains:
                if not isinstance(remaining, c.Pi) or not c.definitionally_equal(
                    remaining.domain, domain, work
                ):
                    raise EncodingError("A constructor must bind the shared parameters")
                ctor_environment = (remaining.domain, *ctor_environment)
                remaining = remaining.codomain
            while isinstance(remaining, c.Pi):
                domain = remaining.domain
                expected = tuple(
                    c.Bound(len(ctor_environment) - 1 - i) for i in range(len(entries))
                )
                if _occurs(domain, identity, work) and not _result_arguments(
                    domain, identity, expected, work
                ):
                    if isinstance(domain, c.Pi) and _occurs(domain.domain, identity, work):
                        raise c.TypeCheckError("A recursive field must be strictly positive")
                    raise UnsupportedInductiveError(
                        "Only direct positive recursive fields are implemented"
                    )
                sort = c.normalize(c.infer(domain, ctor_environment, work), work)
                if not isinstance(sort, c.Universe) or sort.level > result_level:
                    raise c.TypeCheckError("A constructor field exceeds the result universe")
                ctor_environment = (domain, *ctor_environment)
                remaining = remaining.codomain
            expected = tuple(
                c.Bound(len(ctor_environment) - 1 - i) for i in range(len(entries))
            )
            if not _result_arguments(remaining, identity, expected, work):
                raise c.TypeCheckError(
                    "A constructor must return this inductive with its unchanged parameters"
                )
            signatures.append((constructor, signature))
        for constructor, signature in signatures:
            reader._constants[constructor] = c.Constant(constructor, signature)
            installed.append(constructor)
        reader._validated_inductives.add(node)
        succeeded = True
    finally:
        reader._validating_inductives.remove(node)
        if not succeeded:
            for variable in installed:
                reader._constants.pop(variable, None)
