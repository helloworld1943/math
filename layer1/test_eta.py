import unittest

from . import CheckLimitError, Program, TypeCheckError
from . import _calculus as c
from .lean_examples import Examples


class EtaTests(unittest.TestCase):
    def equal(self, left: c.Term, right: c.Term) -> bool:
        return c.definitionally_equal(left, right, c.Work(10_000))

    def test_eta_contracts_and_shifts_an_outer_reference(self) -> None:
        expanded = c.Lambda(c.Universe(0), c.Application(c.Bound(1), c.Bound(0)))
        self.assertTrue(self.equal(expanded, c.Bound(0)))
        self.assertTrue(self.equal(c.Bound(0), expanded))

    def test_eta_does_not_contract_if_the_function_mentions_its_parameter(self) -> None:
        function = c.Application(c.Bound(1), c.Bound(0))
        expanded = c.Lambda(c.Universe(0), c.Application(function, c.Bound(0)))
        self.assertFalse(self.equal(expanded, c.Bound(0)))
        self.assertEqual(c._eta_normal(expanded, c.Work(100)), expanded)

    def test_free_occurrence_detection_checks_nested_domains_and_bodies(self) -> None:
        for nested in (
            c.Lambda(c.Bound(0), c.Universe(0)),
            c.Lambda(c.Universe(0), c.Bound(1)),
            c.Pi(c.Bound(0), c.Universe(0)),
            c.Pi(c.Universe(0), c.Bound(1)),
            c.TypeNode(c.Bound(0)),
        ):
            with self.subTest(nested=nested):
                function = c.Application(c.Bound(1), nested)
                expanded = c.Lambda(
                    c.Universe(0), c.Application(function, c.Bound(0))
                )
                self.assertTrue(c._occurs(function, c.Work(1000)))
                self.assertEqual(
                    c._eta_normal(expanded, c.Work(1000)),
                    c._without_type_nodes(expanded, c.Work(1000)),
                )

    def test_locally_bound_reference_is_not_a_free_occurrence(self) -> None:
        local_type = c.Pi(c.Universe(0), c.Bound(0))
        function = c.Application(c.Bound(1), local_type)
        expanded = c.Lambda(c.Universe(0), c.Application(function, c.Bound(0)))
        expected = c.Application(c.Bound(0), local_type)
        self.assertTrue(self.equal(expanded, expected))

    def test_eta_requires_the_bound_variable_as_the_actual_argument(self) -> None:
        for argument in (c.Universe(0), c.Bound(1)):
            with self.subTest(argument=argument):
                expanded = c.Lambda(
                    c.Universe(0), c.Application(c.Bound(1), argument)
                )
                self.assertFalse(self.equal(expanded, c.Bound(0)))

    def test_beta_and_eta_work_together_inside_pi_types(self) -> None:
        eta = c.Lambda(c.Universe(0), c.Application(c.Bound(1), c.Bound(0)))
        identity = c.Lambda(c.Universe(1), c.Bound(0))
        left = c.Pi(c.Application(identity, c.Universe(0)), eta)
        right = c.Pi(c.Universe(0), c.Bound(0))
        self.assertTrue(self.equal(left, right))

    def test_multiple_eta_binders_are_contracted_without_capture(self) -> None:
        expanded = c.Lambda(c.Universe(0), c.Lambda(
            c.Universe(0),
            c.Application(c.Application(c.Bound(2), c.Bound(1)), c.Bound(0)),
        ))
        self.assertTrue(self.equal(expanded, c.Bound(0)))

    def test_beta_normalizer_does_not_silently_change_its_contract(self) -> None:
        eta = c.Lambda(c.Universe(0), c.Application(c.Bound(1), c.Bound(0)))
        self.assertEqual(c.normalize(eta, c.Work(1000)), eta)

    def test_equal_comparison_budget_exhaustion_is_an_error(self) -> None:
        with self.assertRaises(CheckLimitError):
            c.definitionally_equal(c.Universe(0), c.Universe(0), c.Work(1))

    def test_eta_does_not_equate_an_arbitrary_composition_with_a_function(self) -> None:
        e = Examples()
        p = e.program
        a, d, f, g, value, x = e.variables(6)
        ta = p.type_node(a)
        function_type = e.arrows(ta, ta)
        changed_f = p.lambda_(x, ta, e.apply(f, e.apply(g, x)))
        bindings = (
            (a, e.u0), (d, e.arrows(function_type, e.u0)),
            (f, function_type), (g, function_type),
            (value, p.type_node(e.apply(d, f))),
        )
        expression = e.lambdas(bindings, value)
        supplied = e.forall(bindings, p.type_node(e.apply(d, changed_f)))
        relation = p.relation("HasType", expression, supplied)
        self.assertFalse(p.commit().check(relation))

    def test_lean_eta_typing_witness(self) -> None:
        examples = Examples()
        example = examples.eta_conversion()
        relation = examples.program.relation(
            "HasType", example.expression, example.type
        )
        examples.program.commit().require(relation)

    def test_eta_equality_is_used_for_application_argument_types(self) -> None:
        e = Examples()
        p = e.program
        a, b, d, f, value, consumer, x = e.variables(7)
        ta, tb = p.type_node(a), p.type_node(b)
        function_type = e.arrows(ta, tb)
        expanded_f = p.lambda_(x, ta, e.apply(f, x))
        original_type = p.type_node(e.apply(d, f))
        expanded_type = p.type_node(e.apply(d, expanded_f))
        bindings = (
            (a, e.u0), (b, e.u0), (d, e.arrows(function_type, e.u0)),
            (f, function_type), (value, original_type),
            (consumer, e.arrows(expanded_type, ta)),
        )
        expression = e.lambdas(bindings, e.apply(consumer, value))
        relation = p.relation("HasType", expression, e.forall(bindings, ta))
        p.commit().require(relation)

    def test_beta_reduces_does_not_accept_an_eta_step(self) -> None:
        p = Program()
        u1 = p.universe(1)
        f, x = p.variable(), p.variable()
        application = p.apply(f, x)
        eta = p.lambda_(x, u1, application)
        source = p.lambda_(f, p.function_type(x, u1, u1), eta)
        target = p.lambda_(f, p.function_type(x, u1, u1), f)
        relation = p.relation("BetaReduces", source, target)
        with self.assertRaisesRegex(TypeCheckError, "Application of a Lambda"):
            p.commit().require(relation)

    def test_beta_result_cannot_be_replaced_by_an_eta_equivalent_result(self) -> None:
        p = Program()
        u0, u1 = p.universe(0), p.universe(1)
        x, y, z = (p.variable() for _ in range(3))
        function = p.lambda_(y, u1, y)
        expanded = p.lambda_(x, u1, p.apply(function, x))
        source = p.apply(p.lambda_(z, u1, expanded), u0)
        exact = p.relation("BetaReduces", source, expanded)
        contracted = p.relation("BetaReduces", source, function)
        snapshot = p.commit()
        snapshot.require(exact)
        self.assertFalse(snapshot.check(contracted))


if __name__ == "__main__":
    unittest.main()
