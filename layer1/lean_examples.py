"""Lean-style test fixtures built only with the public Layer 1 graph API."""

from __future__ import annotations

from dataclasses import dataclass

from node import Node

from . import Program


@dataclass(frozen=True)
class Example:
    name: str
    expression: Node
    type: Node


class Examples:
    def __init__(self) -> None:
        self.program = Program()
        self.u0 = self.program.universe(0)
        self.u1 = self.program.universe(1)

    def variables(self, count: int) -> tuple[Node, ...]:
        return tuple(self.program.variable() for _ in range(count))

    def arrows(self, *types: Node) -> Node:
        if len(types) < 2:
            raise ValueError("An arrow needs a domain and a codomain")
        result = types[-1]
        for domain in reversed(types[:-1]):
            result = self.program.function_type(
                self.program.variable(), domain, result
            )
        return result

    def lambdas(self, bindings: tuple[tuple[Node, Node], ...], body: Node) -> Node:
        for variable, domain in reversed(bindings):
            body = self.program.lambda_(variable, domain, body)
        return body

    def forall(self, bindings: tuple[tuple[Node, Node], ...], body: Node) -> Node:
        for variable, domain in reversed(bindings):
            body = self.program.function_type(variable, domain, body)
        return body

    def apply(self, function: Node, *arguments: Node) -> Node:
        for argument in arguments:
            function = self.program.apply(function, argument)
        return function

    def identity(self) -> Example:
        a, x = self.variables(2)
        ta = self.program.type_node(a)
        bindings = ((a, self.u0), (x, ta))
        return Example(
            "identity", self.lambdas(bindings, x), self.forall(bindings, ta)
        )

    def constant(self) -> Example:
        a, b, x, y = self.variables(4)
        ta, tb = self.program.type_node(a), self.program.type_node(b)
        bindings = ((a, self.u0), (b, self.u0), (x, ta), (y, tb))
        return Example(
            "constant", self.lambdas(bindings, x), self.forall(bindings, ta)
        )

    def compose(self) -> Example:
        a, b, c, f, g, x = self.variables(6)
        ta, tb, tc = (self.program.type_node(v) for v in (a, b, c))
        bindings = (
            (a, self.u0), (b, self.u0), (c, self.u0),
            (f, self.arrows(tb, tc)), (g, self.arrows(ta, tb)), (x, ta),
        )
        return Example(
            "compose", self.lambdas(bindings, self.apply(f, self.apply(g, x))),
            self.forall(bindings, tc),
        )

    def flip(self) -> Example:
        a, b, c, f, y, x = self.variables(6)
        ta, tb, tc = (self.program.type_node(v) for v in (a, b, c))
        bindings = (
            (a, self.u0), (b, self.u0), (c, self.u0),
            (f, self.arrows(ta, tb, tc)), (y, tb), (x, ta),
        )
        return Example(
            "flip", self.lambdas(bindings, self.apply(f, x, y)),
            self.forall(bindings, tc),
        )

    def dependent_apply(self) -> Example:
        a, b, f, x, index = self.variables(5)
        ta = self.program.type_node(a)
        family = self.arrows(ta, self.u0)
        dependent_function = self.program.function_type(
            index, ta, self.program.type_node(self.apply(b, index))
        )
        bindings = (
            (a, self.u0), (b, family), (f, dependent_function), (x, ta),
        )
        result_type = self.program.type_node(self.apply(b, x))
        return Example(
            "dependentApply", self.lambdas(bindings, self.apply(f, x)),
            self.forall(bindings, result_type),
        )

    def dependent_compose(self) -> Example:
        a, b, c, f, g, x, i, j, k, z = self.variables(10)
        p = self.program
        ta = p.type_node(a)
        family = self.arrows(ta, self.u0)
        c_domain = p.function_type(i, ta, self.arrows(p.type_node(self.apply(b, i)), self.u0))
        f_type = p.function_type(
            j, ta, p.function_type(
                k, p.type_node(self.apply(b, j)),
                p.type_node(self.apply(c, j, k)),
            ),
        )
        g_type = p.function_type(z, ta, p.type_node(self.apply(b, z)))
        bindings = (
            (a, self.u0), (b, family), (c, c_domain),
            (f, f_type), (g, g_type), (x, ta),
        )
        gx = self.apply(g, x)
        return Example(
            "dependentCompose", self.lambdas(bindings, self.apply(f, x, gx)),
            self.forall(bindings, p.type_node(self.apply(c, x, gx))),
        )

    def type_constructor(self) -> Example:
        a, x = self.variables(2)
        ta = self.program.type_node(a)
        body = self.program.function_type(x, ta, ta)
        return Example(
            "Endo", self.program.lambda_(a, self.u0, body),
            self.program.function_type(a, self.u0, self.u0),
        )

    def computed_domain(self) -> Example:
        constructor = self.type_constructor()
        a, x = self.variables(2)
        ta = self.program.type_node(a)
        identity = self.program.lambda_(x, ta, x)
        return Example(
            "endoIdentity", self.program.lambda_(a, self.u0, identity),
            self.program.function_type(
                a, self.u0, self.program.type_node(self.apply(constructor.expression, a))
            ),
        )

    def let_binding(self) -> Example:
        a, x, y = self.variables(3)
        ta = self.program.type_node(a)
        body = self.apply(self.program.lambda_(y, ta, y), x)
        bindings = ((a, self.u0), (x, ta))
        return Example(
            "letIdentity", self.lambdas(bindings, body), self.forall(bindings, ta)
        )

    def bool_type(self) -> Node:
        a = self.program.variable()
        ta = self.program.type_node(a)
        return self.program.function_type(a, self.u0, self.arrows(ta, ta, ta))

    def boolean(self, value: bool) -> Example:
        a, yes, no = self.variables(3)
        ta = self.program.type_node(a)
        bindings = ((a, self.u0), (yes, ta), (no, ta))
        return Example(
            "churchTrue" if value else "churchFalse",
            self.lambdas(bindings, yes if value else no), self.bool_type(),
        )

    def choose(self) -> Example:
        a, b, yes, no = self.variables(4)
        ta = self.program.type_node(a)
        bindings = ((a, self.u0), (b, self.bool_type()), (yes, ta), (no, ta))
        return Example(
            "choose", self.lambdas(bindings, self.apply(b, a, yes, no)),
            self.forall(bindings, ta),
        )

    def bool_not(self) -> Example:
        b, a, yes, no = self.variables(4)
        ta = self.program.type_node(a)
        bindings = ((b, self.bool_type()), (a, self.u0), (yes, ta), (no, ta))
        return Example(
            "churchNot", self.lambdas(bindings, self.apply(b, a, no, yes)),
            self.forall(((b, self.bool_type()),), self.bool_type()),
        )

    def nat_type(self) -> Node:
        a = self.program.variable()
        ta = self.program.type_node(a)
        return self.program.function_type(
            a, self.u0, self.arrows(self.arrows(ta, ta), ta, ta)
        )

    def numeral(self, value: int) -> Example:
        if value < 0:
            raise ValueError("A Church numeral must be non-negative")
        a, step, zero = self.variables(3)
        ta = self.program.type_node(a)
        bindings = ((a, self.u0), (step, self.arrows(ta, ta)), (zero, ta))
        body = zero
        for _ in range(value):
            body = self.apply(step, body)
        return Example(
            f"church{value}", self.lambdas(bindings, body), self.nat_type()
        )

    def arithmetic(self, multiply: bool = False) -> Example:
        m, n, a, step, zero = self.variables(5)
        ta = self.program.type_node(a)
        bindings = (
            (m, self.nat_type()), (n, self.nat_type()),
            (a, self.u0), (step, self.arrows(ta, ta)), (zero, ta),
        )
        if multiply:
            body = self.apply(m, a, self.apply(n, a, step), zero)
        else:
            body = self.apply(m, a, step, self.apply(n, a, step, zero))
        return Example(
            "churchMul" if multiply else "churchAdd",
            self.lambdas(bindings, body),
            self.forall(bindings[:2], self.nat_type()),
        )

    def pair_type(self, a: Node, b: Node) -> Node:
        result = self.program.variable()
        tr = self.program.type_node(result)
        return self.program.function_type(
            result, self.u0, self.arrows(self.arrows(a, b, tr), tr)
        )

    def pair(self) -> Example:
        a, b, x, y, result, combine = self.variables(6)
        ta, tb, tr = (self.program.type_node(v) for v in (a, b, result))
        bindings = (
            (a, self.u0), (b, self.u0), (x, ta), (y, tb),
            (result, self.u0), (combine, self.arrows(ta, tb, tr)),
        )
        return Example(
            "churchPair", self.lambdas(bindings, self.apply(combine, x, y)),
            self.forall(bindings[:4], self.pair_type(ta, tb)),
        )

    def projection(self, first: bool) -> Example:
        a, b, pair, x, y = self.variables(5)
        ta, tb = self.program.type_node(a), self.program.type_node(b)
        result = a if first else b
        selector = self.lambdas(((x, ta), (y, tb)), x if first else y)
        bindings = ((a, self.u0), (b, self.u0), (pair, self.pair_type(ta, tb)))
        return Example(
            "churchFst" if first else "churchSnd",
            self.lambdas(bindings, self.apply(pair, result, selector)),
            self.forall(bindings, ta if first else tb),
        )

    def eta_conversion(self) -> Example:
        a, b, d, f, value, x = self.variables(6)
        p = self.program
        ta, tb = p.type_node(a), p.type_node(b)
        function_type = self.arrows(ta, tb)
        expanded_f = p.lambda_(x, ta, self.apply(f, x))
        bindings = (
            (a, self.u0), (b, self.u0),
            (d, self.arrows(function_type, self.u0)),
            (f, function_type), (value, p.type_node(self.apply(d, f))),
        )
        return Example(
            "etaWitness", self.lambdas(bindings, value),
            self.forall(bindings, p.type_node(self.apply(d, expanded_f))),
        )

    def supported(self) -> tuple[Example, ...]:
        return (
            self.identity(), self.constant(), self.compose(), self.flip(),
            self.dependent_apply(), self.dependent_compose(),
            self.type_constructor(), self.computed_domain(), self.let_binding(),
            self.boolean(True), self.boolean(False), self.choose(), self.bool_not(),
            self.numeral(0), self.numeral(3), self.arithmetic(),
            self.arithmetic(multiply=True), self.pair(),
            self.projection(True), self.projection(False),
        )


def main() -> None:
    examples = Examples()
    checks = [
        (example.name, examples.program.relation("HasType", example.expression, example.type))
        for example in examples.supported()
    ]
    snapshot = examples.program.commit()
    for name, relation in checks:
        snapshot.require(relation)
        print(f"PASS: {name}")


if __name__ == "__main__":
    main()
