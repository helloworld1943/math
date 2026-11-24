"""More readiness checks, without adding case analysis or indexed inductives."""

import itertools
import unittest

from node import Node, UnknownNodeError

from . import EncodingError, TypeCheckError
from . import _calculus as c
from .lean_examples import Examples


class AdditionalCaseTests(unittest.TestCase):
    def setUp(self) -> None:
        self.examples = Examples()
        self.p = self.examples.program
        self.u0, self.u1 = self.examples.u0, self.examples.u1

    def require_type(self, expression: Node, supplied: Node) -> None:
        relation = self.p.relation("HasType", expression, supplied)
        self.p.commit().require(relation, max_steps=100_000)

    def scalar(self, name: str) -> tuple[Node, Node, Node]:
        declaration = self.p.inductive(name, self.u0)
        type_node = self.p.type_node(declaration.identity)
        value = declaration.constructor("value", type_node)
        definition = declaration.finish()
        return definition, type_node, value

    def computations_equal(self, left: Node, right: Node) -> None:
        reader = self.p.commit().view(left, right)._reader
        work = c.Work(100_000)
        self.assertEqual(
            c.normalize(reader.term(left, work), work),
            c.normalize(reader.term(right, work), work),
        )

    def test_twice_higher_order_function_and_computation(self) -> None:
        e = self.examples
        a, f, x = e.variables(3)
        ta = self.p.type_node(a)
        bindings = ((a, self.u0), (f, e.arrows(ta, ta)), (x, ta))
        twice = e.lambdas(bindings, e.apply(f, e.apply(f, x)))
        self.require_type(twice, e.forall(bindings, ta))
        a, x, y = e.variables(3)
        ta = self.p.type_node(a)
        identity = self.p.lambda_(y, ta, y)
        applied = e.lambdas(
            ((a, self.u0), (x, ta)), e.apply(twice, a, identity, x)
        )
        expected = e.lambdas(((a, self.u0), (x, ta)), x)
        self.require_type(applied, e.forall(((a, self.u0), (x, ta)), ta))
        self.computations_equal(applied, expected)

    def test_function_valued_parameter_returns_another_function(self) -> None:
        e = self.examples
        a, b, f, x, g, y = e.variables(6)
        ta, tb = self.p.type_node(a), self.p.type_node(b)
        bindings = (
            (a, self.u0), (b, self.u0), (f, e.arrows(ta, tb)),
            (x, ta), (g, e.arrows(tb, ta)),
        )
        body = self.p.lambda_(y, tb, e.apply(g, y))
        function = e.lambdas(bindings, body)
        self.require_type(function, e.forall(bindings, e.arrows(tb, ta)))

    def test_type_valued_function_accepts_computed_type_argument(self) -> None:
        p = self.p
        a, x, b = self.examples.variables(3)
        ta = p.type_node(a)
        endo = p.lambda_(a, self.u0, p.function_type(x, ta, ta))
        constant_type = p.lambda_(b, self.u0, b)
        _, t, _ = self.scalar("Ground")
        computed_type = p.type_node(p.apply(constant_type, t))
        application = p.apply(endo, computed_type)
        self.require_type(application, self.u0)
        result = p.function_type(x, t, t)
        self.computations_equal(application, result)

    def test_five_nominal_types_and_argument_matching_table(self) -> None:
        p = self.p
        types = [self.scalar("SameDisplayName") for _ in range(5)]
        functions = []
        for _, t, _ in types:
            x = p.variable()
            functions.append(p.lambda_(x, t, x))
        checks = []
        for i, function in enumerate(functions):
            for j, (_, _, value) in enumerate(types):
                application = p.apply(function, value)
                checks.append((i, j, p.relation("HasType", application, types[i][1])))
        snapshot = p.commit()
        for i, j, relation in checks:
            with self.subTest(domain=i, argument=j):
                self.assertEqual(snapshot.check(relation, max_steps=100_000), i == j)

    def test_three_constructor_fields_preserve_every_argument_position(self) -> None:
        e, p = self.examples, self.p
        _, ta, va = self.scalar("A")
        _, tb, vb = self.scalar("B")
        _, tc, vc = self.scalar("C")
        declaration = p.inductive("Triple", self.u0)
        target = p.type_node(declaration.identity)
        x, y, z = e.variables(3)
        signature = e.forall(((x, ta), (y, tb), (z, tc)), target)
        make = declaration.constructor("make", signature)
        declaration.finish()
        values = (va, vb, vc)
        checks = []
        for order in itertools.permutations(range(3)):
            application = e.apply(make, *(values[i] for i in order))
            checks.append((order, p.relation("HasType", application, target)))
        snapshot = p.commit()
        for order, relation in checks:
            with self.subTest(order=order):
                self.assertEqual(
                    snapshot.check(relation, max_steps=100_000), order == (0, 1, 2)
                )

    def evidence_declaration(self):
        e, p = self.examples, self.p
        a, family, x, evidence, index = e.variables(5)
        ta = p.type_node(a)
        family_type = p.function_type(index, ta, self.u0)
        at_x = p.type_node(e.apply(family, x))
        declaration = p.inductive(
            "EvidenceBox", self.u0,
            parameters=((a, self.u0), (family, family_type), (x, ta), (evidence, at_x)),
        )
        result = p.type_node(e.apply(declaration.identity, a, family, x, evidence))
        make = declaration.constructor("mk", result)
        return declaration.finish(), declaration.identity, make

    def test_application_typed_inductive_parameter(self) -> None:
        e, p = self.examples, self.p
        definition, identity, make = self.evidence_declaration()
        relation = p.relation("ValidInductive", definition)
        p.commit().require(relation, max_steps=100_000)
        _, ground, value = self.scalar("Ground")
        x = p.variable()
        family = p.lambda_(x, ground, ground)
        application = e.apply(make, ground, family, value, value)
        expected = p.type_node(e.apply(identity, ground, family, value, value))
        self.require_type(application, expected)

    def test_constructor_parameter_evidence_cannot_switch_witnesses(self) -> None:
        e, p = self.examples, self.p
        _, identity, make = self.evidence_declaration()
        a, family, x, y, evidence = e.variables(5)
        ta = p.type_node(a)
        bindings = (
            (a, self.u0), (family, e.arrows(ta, self.u0)),
            (x, ta), (y, ta), (evidence, p.type_node(e.apply(family, x))),
        )
        wrong = e.lambdas(bindings, e.apply(make, a, family, y, evidence))
        expected = e.forall(
            bindings, p.type_node(e.apply(identity, a, family, y, evidence))
        )
        with self.assertRaisesRegex(TypeCheckError, "argument type"):
            self.require_type(wrong, expected)

    def test_dependent_constructor_fields_are_supported_without_indices(self) -> None:
        e, p = self.examples, self.p
        a, family, index, witness, evidence = e.variables(5)
        ta = p.type_node(a)
        family_type = p.function_type(index, ta, self.u0)
        declaration = p.inductive(
            "Package", self.u0, parameters=((a, self.u0), (family, family_type))
        )
        result = p.type_node(e.apply(declaration.identity, a, family))
        signature = e.forall(
            ((witness, ta), (evidence, p.type_node(e.apply(family, witness)))), result
        )
        make = declaration.constructor("mk", signature)
        definition = declaration.finish()
        valid = p.relation("ValidInductive", definition)
        p.commit().require(valid, max_steps=100_000)
        _, ground, value = self.scalar("Ground")
        x = p.variable()
        constant_family = p.lambda_(x, ground, ground)
        application = e.apply(make, ground, constant_family, value, value)
        expected = p.type_node(e.apply(declaration.identity, ground, constant_family))
        self.require_type(application, expected)

    def test_parametric_inductive_type_remains_usable_at_higher_levels(self) -> None:
        e, p = self.examples, self.p
        a, value = e.variables(2)
        declaration = p.inductive(
            "LargeBox", self.u1, parameters=((a, self.u1),)
        )
        target = p.type_node(e.apply(declaration.identity, a))
        make = declaration.constructor(
            "mk", p.function_type(value, p.type_node(a), target)
        )
        definition = declaration.finish()
        relation = p.relation("ValidInductive", definition)
        p.commit().require(relation, max_steps=100_000)
        result = p.type_node(e.apply(declaration.identity, self.u0))
        application = e.apply(make, self.u0, self.scalar("Ground")[1])
        self.require_type(result, self.u1)
        self.require_type(application, result)

    def test_multiple_non_recursive_constructor_names_do_not_affect_type_identity(self) -> None:
        p = self.p
        declaration = p.inductive("Choices", self.u0)
        t = p.type_node(declaration.identity)
        constructors = [declaration.constructor(f"case{i}", t) for i in range(8)]
        definition = declaration.finish()
        snapshot = p.commit()
        body = snapshot.view(definition).fields(definition)["body"]
        context = snapshot.view(body).fields(body)["context"]
        for i, constructor in enumerate(constructors):
            with self.subTest(constructor=i):
                self.assertEqual(snapshot.view(constructor).name(constructor), f"case{i}")
                self.assertIs(snapshot.view(constructor).fields(constructor)["context"], context)
                self.require_type(constructor, t)

    def test_ordered_parameter_redeclaration_is_rejected_before_mutation(self) -> None:
        p = self.p
        a = p.variable()
        declaration = p.inductive("First", self.u0, parameters=((a, self.u0),))
        declaration.finish()
        before = p.commit().graph.nodes
        with self.assertRaises(EncodingError):
            p.inductive("Second", self.u0, parameters=((a, self.u0),))
        self.assertEqual(before, p.commit().graph.nodes)

    def test_mixed_primitive_and_declaration_relations_truth_table(self) -> None:
        p = self.p
        definition, t, value = self.scalar("Ground")
        good_type = p.relation("HasType", value, t)
        wrong_type = p.relation("HasType", value, self.u0)
        declaration = p.relation("ValidInductive", definition)
        for truth in itertools.product((False, True), repeat=3):
            children = (declaration, *(good_type if b else wrong_type for b in truth))
            conjunction = p.all_of(definition, t, value, self.u0, relations=children)
            disjunction = p.any_of(
                definition, t, value, self.u0, relations=children[1:]
            )
            snapshot = p.commit()
            with self.subTest(truth=truth):
                self.assertEqual(snapshot.check(conjunction, max_steps=100_000), all(truth))
                self.assertEqual(snapshot.check(disjunction, max_steps=100_000), any(truth))

    def test_all_binder_choices_reject_a_wrong_beta_result(self) -> None:
        e, p = self.examples, self.p
        for depth in range(1, 5):
            outer = p.variable()
            inner = e.variables(depth)
            for chosen in range(depth + 1):
                source_body = outer if chosen == 0 else inner[chosen - 1]
                source = p.apply(p.lambda_(
                    outer, self.u1,
                    e.lambdas(tuple((v, self.u1) for v in inner), source_body),
                ), self.u0)
                for result_index in range(depth + 1):
                    result_body = self.u0 if result_index == 0 else inner[result_index - 1]
                    result = e.lambdas(tuple((v, self.u1) for v in inner), result_body)
                    relation = p.relation("BetaReduces", source, result)
                    with self.subTest(depth=depth, chosen=chosen, result=result_index):
                        self.assertEqual(
                            p.commit().check(relation), chosen == result_index
                        )

    def test_nominal_dependency_does_not_make_an_unrelated_declaration_visible(self) -> None:
        first, t, _ = self.scalar("First")
        second, _, _ = self.scalar("Second")
        local = self.p.commit().view(t)
        self.assertIn(first, local.nodes)
        for hidden in (second, self.p.graph.root):
            self.assertNotIn(hidden, local.nodes)
            with self.assertRaises(UnknownNodeError):
                local.fields(hidden)

    def test_both_higher_order_and_dependent_example_shapes_reject_invented_type(self) -> None:
        e = self.examples
        for example in (e.compose(), e.dependent_compose(), e.computed_domain()):
            with self.subTest(example=example.name):
                self.require_type(example.expression, example.type)
                with self.assertRaises(TypeCheckError):
                    self.require_type(example.expression, self.u0)


if __name__ == "__main__":
    unittest.main()
