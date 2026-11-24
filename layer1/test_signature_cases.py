"""Additional constructor signatures in the implemented direct-recursion fragment."""

import unittest

from node import Node

from . import TypeCheckError
from .lean_examples import Examples


class SignatureCaseTests(unittest.TestCase):
    def setUp(self) -> None:
        self.examples = Examples()
        self.p = self.examples.program

    def valid(self, definition: Node) -> None:
        relation = self.p.relation("ValidInductive", definition)
        self.p.commit().require(relation, max_steps=100_000)

    def typed(self, expression: Node, supplied: Node) -> None:
        relation = self.p.relation("HasType", expression, supplied)
        self.p.commit().require(relation, max_steps=100_000)

    def ground(self) -> tuple[Node, Node]:
        declaration = self.p.inductive("Ground", self.examples.u0)
        type_node = self.p.type_node(declaration.identity)
        value = declaration.constructor("value", type_node)
        self.valid(declaration.finish())
        return type_node, value

    def handler(self) -> tuple[Node, Node, Node]:
        e, p = self.examples, self.p
        a, family, x, field = e.variables(4)
        ta = p.type_node(a)
        declaration = p.inductive(
            "HandlerBox", e.u0,
            parameters=((a, e.u0), (family, e.arrows(ta, e.u0))),
        )
        handler_type = p.function_type(x, ta, p.type_node(e.apply(family, x)))
        result = p.type_node(e.apply(declaration.identity, a, family))
        make = declaration.constructor("mk", p.function_type(field, handler_type, result))
        return declaration.finish(), declaration.identity, make

    def test_constructor_may_store_a_non_recursive_dependent_function(self) -> None:
        e, p = self.examples, self.p
        definition, identity, make = self.handler()
        self.valid(definition)
        ground, value = self.ground()
        x, y = e.variables(2)
        family = p.lambda_(x, ground, ground)
        handler = p.lambda_(y, ground, value)
        expression = e.apply(make, ground, family, handler)
        self.typed(expression, p.type_node(e.apply(identity, ground, family)))

    def test_function_field_cannot_be_replaced_with_a_plain_value(self) -> None:
        e, p = self.examples, self.p
        _, identity, make = self.handler()
        ground, value = self.ground()
        x = p.variable()
        family = p.lambda_(x, ground, ground)
        expression = e.apply(make, ground, family, value)
        with self.assertRaisesRegex(TypeCheckError, "argument type"):
            self.typed(expression, p.type_node(e.apply(identity, ground, family)))

    def test_constructor_can_have_two_positive_recursive_fields(self) -> None:
        e, p = self.examples, self.p
        tree = p.inductive("BinaryTree", e.u0)
        tree_type = p.type_node(tree.identity)
        leaf = tree.constructor("leaf", tree_type)
        left, right = e.variables(2)
        branch = tree.constructor(
            "branch", e.forall(((left, tree_type), (right, tree_type)), tree_type)
        )
        self.valid(tree.finish())
        first = e.apply(branch, leaf, leaf)
        second = e.apply(branch, first, leaf)
        self.typed(second, tree_type)

    def test_constructor_accepts_a_type_field_when_the_result_level_allows_it(self) -> None:
        e, p = self.examples, self.p
        holder = p.inductive("TypeHolder", e.u1)
        result = p.type_node(holder.identity)
        a = p.variable()
        make = holder.constructor("mk", p.function_type(a, e.u0, result))
        self.valid(holder.finish())
        ground, _ = self.ground()
        self.typed(p.apply(make, ground), result)

    def test_constructor_can_have_no_fields_even_with_a_function_parameter(self) -> None:
        e, p = self.examples, self.p
        a, fn, x = e.variables(3)
        ta = p.type_node(a)
        definition = p.inductive(
            "NamedHandler", e.u0,
            parameters=((a, e.u0), (fn, p.function_type(x, ta, ta))),
        )
        result = p.type_node(e.apply(definition.identity, a, fn))
        make = definition.constructor("mk", result)
        self.valid(definition.finish())
        ground, _ = self.ground()
        y = p.variable()
        identity = p.lambda_(y, ground, y)
        self.typed(
            e.apply(make, ground, identity),
            p.type_node(e.apply(definition.identity, ground, identity)),
        )

    def test_same_result_type_does_not_permit_a_field_with_a_value_as_its_type(self) -> None:
        e, p = self.examples, self.p
        _, value = self.ground()
        d = p.inductive("InvalidField", e.u0)
        result = p.type_node(d.identity)
        x = p.variable()
        d.constructor("mk", p.function_type(x, value, result))
        with self.assertRaisesRegex(TypeCheckError, "domain"):
            self.valid(d.finish())

    def test_computed_negative_recursive_domain_is_not_hidden_by_beta_reduction(self) -> None:
        e, p = self.examples, self.p
        d = p.inductive("NegativeAlias", e.u1)
        result = p.type_node(d.identity)
        t, x, field = e.variables(3)
        alias = p.lambda_(t, e.u1, p.function_type(x, p.type_node(t), e.u0))
        negative = p.type_node(p.apply(alias, result))
        d.constructor("mk", p.function_type(field, negative, result))
        with self.assertRaisesRegex(TypeCheckError, "strictly positive"):
            self.valid(d.finish())

    def test_constructor_result_cannot_point_to_a_different_nominal_type(self) -> None:
        e, p = self.examples, self.p
        other, _ = self.ground()
        d = p.inductive("Different", e.u0)
        d.constructor("mk", other)
        with self.assertRaisesRegex(TypeCheckError, "must return this inductive"):
            self.valid(d.finish())


if __name__ == "__main__":
    unittest.main()
