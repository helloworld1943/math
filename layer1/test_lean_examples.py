import unittest

from node import Node, UnknownNodeError

from . import CheckLimitError, TypeCheckError
from . import _calculus as calculus
from .lean_examples import Example, Examples


class LeanExampleTests(unittest.TestCase):
    def setUp(self) -> None:
        self.examples = Examples()
        self.program = self.examples.program

    def require_type(self, example: Example) -> None:
        relation = self.program.relation(
            "HasType", example.expression, example.type
        )
        self.program.commit().require(relation)

    def assert_normalizes_to(
        self, expression: Node, expected: Node
    ) -> calculus.Term:
        snapshot = self.program.commit()
        # Observe the actual primitive evaluator; the public reduction relation
        # intentionally checks only one beta step.
        reader = snapshot.view(expression, expected)._reader
        work = calculus.Work(100_000)
        actual_term = reader.term(expression, work)
        expected_term = reader.term(expected, work)
        actual = calculus.normalize(actual_term, work)
        self.assertEqual(actual, calculus.normalize(expected_term, work))
        return actual

    def assert_numeral(self, term: calculus.Term, expected: int) -> None:
        for _ in range(3):
            if not isinstance(term, calculus.Lambda):
                self.fail("A Church numeral must have three enclosing Lambdas")
            term = term.body
        count = 0
        while isinstance(term, calculus.Application):
            self.assertEqual(term.function, calculus.Bound(1))
            count += 1
            term = term.argument
        self.assertEqual(term, calculus.Bound(0))
        self.assertEqual(count, expected)

    def test_all_twenty_supported_examples_typecheck(self) -> None:
        examples = self.examples.supported()
        self.assertEqual(len(examples), 20)
        self.assertEqual(len({example.name for example in examples}), 20)
        for example in examples:
            with self.subTest(example=example.name):
                self.require_type(example)

    def test_compose_two_identity_functions(self) -> None:
        e, p = self.examples, self.program
        compose = e.compose()
        a, x, parameter = e.variables(3)
        ta = p.type_node(a)
        identity = p.lambda_(parameter, ta, parameter)
        expression = e.lambdas(
            ((a, e.u0), (x, ta)),
            e.apply(compose.expression, a, a, a, identity, identity, x),
        )
        expected = e.lambdas(((a, e.u0), (x, ta)), x)
        expected_type = e.forall(((a, e.u0), (x, ta)), ta)
        self.require_type(Example("compositionResult", expression, expected_type))
        self.require_type(Example("compositionExpected", expected, expected_type))
        self.assert_normalizes_to(expression, expected)

    def test_flip_constant_selects_original_first_argument(self) -> None:
        e, p = self.examples, self.program
        flipped, constant = e.flip(), e.constant()
        a, x, y = e.variables(3)
        ta = p.type_node(a)
        bindings = ((a, e.u0), (x, ta), (y, ta))
        constant_at_a = e.apply(constant.expression, a, a)
        expression = e.lambdas(
            bindings, e.apply(flipped.expression, a, a, a, constant_at_a, x, y)
        )
        expected = e.lambdas(bindings, y)
        self.require_type(Example("flippedConstant", expression, e.forall(bindings, ta)))
        self.assert_normalizes_to(expression, expected)

    def test_let_encoding_reduces_to_the_original_value(self) -> None:
        e = self.examples
        actual, expected = e.let_binding(), e.identity()
        self.require_type(actual)
        self.assert_normalizes_to(actual.expression, expected.expression)

    def test_church_boolean_selection(self) -> None:
        e, p = self.examples, self.program
        choose = e.choose()
        for value in (True, False):
            with self.subTest(value=value):
                boolean = e.boolean(value)
                a, x, y = e.variables(3)
                ta = p.type_node(a)
                bindings = ((a, e.u0), (x, ta), (y, ta))
                expression = e.lambdas(
                    bindings, e.apply(choose.expression, a, boolean.expression, x, y)
                )
                expected = e.lambdas(bindings, x if value else y)
                self.require_type(Example("selected", expression, e.forall(bindings, ta)))
                self.assert_normalizes_to(expression, expected)

    def test_church_boolean_negation(self) -> None:
        e = self.examples
        negate = e.bool_not()
        for value in (True, False):
            with self.subTest(value=value):
                application = e.apply(negate.expression, e.boolean(value).expression)
                expected = e.boolean(not value)
                self.require_type(Example("negated", application, expected.type))
                self.assert_normalizes_to(application, expected.expression)

    def test_church_numerals_zero_through_six(self) -> None:
        for value in range(7):
            with self.subTest(value=value):
                example = self.examples.numeral(value)
                self.require_type(example)
                self.assert_numeral(
                    self.assert_normalizes_to(example.expression, example.expression),
                    value,
                )

    def test_church_addition_table(self) -> None:
        e = self.examples
        add = e.arithmetic()
        for left in range(5):
            for right in range(5):
                with self.subTest(left=left, right=right):
                    expression = e.apply(
                        add.expression, e.numeral(left).expression,
                        e.numeral(right).expression,
                    )
                    expected = e.numeral(left + right)
                    self.require_type(Example("sum", expression, expected.type))
                    result = self.assert_normalizes_to(expression, expected.expression)
                    self.assert_numeral(result, left + right)

    def test_church_multiplication_table(self) -> None:
        e = self.examples
        multiply = e.arithmetic(multiply=True)
        for left in range(5):
            for right in range(5):
                with self.subTest(left=left, right=right):
                    expression = e.apply(
                        multiply.expression, e.numeral(left).expression,
                        e.numeral(right).expression,
                    )
                    expected = e.numeral(left * right)
                    self.require_type(Example("product", expression, expected.type))
                    result = self.assert_normalizes_to(expression, expected.expression)
                    self.assert_numeral(result, left * right)

    def test_church_pair_projections(self) -> None:
        e, p = self.examples, self.program
        pair = e.pair()
        for first in (True, False):
            with self.subTest(first=first):
                projection = e.projection(first)
                a, b, x, y = e.variables(4)
                ta, tb = p.type_node(a), p.type_node(b)
                bindings = ((a, e.u0), (b, e.u0), (x, ta), (y, tb))
                value = e.apply(pair.expression, a, b, x, y)
                expression = e.lambdas(
                    bindings, e.apply(projection.expression, a, b, value)
                )
                expected = e.lambdas(bindings, x if first else y)
                self.require_type(Example(
                    "projection", expression, e.forall(bindings, ta if first else tb)
                ))
                self.assert_normalizes_to(expression, expected)

    def test_wrong_function_order_in_composition_is_rejected(self) -> None:
        e, p = self.examples, self.program
        a, b, c, f, g, x = e.variables(6)
        ta, tb, tc = (p.type_node(v) for v in (a, b, c))
        bindings = (
            (a, e.u0), (b, e.u0), (c, e.u0),
            (f, e.arrows(tb, tc)), (g, e.arrows(ta, tb)), (x, ta),
        )
        expression = e.lambdas(bindings, e.apply(g, e.apply(f, x)))
        with self.assertRaisesRegex(TypeCheckError, "argument type"):
            self.require_type(Example("wrongComposition", expression, e.forall(bindings, tc)))

    def test_dependent_family_cannot_be_replaced_by_constant_result_type(self) -> None:
        e, p = self.examples, self.program
        actual = e.dependent_apply()
        reader = p.commit().view(actual.type)
        binders = []
        current = actual.type
        for _ in range(4):
            fields = reader.fields(current)
            binders.append((fields["variable"], fields["domain"]))
            current = fields["codomain"]
        wrong_type = e.forall(tuple(binders), binders[0][0])
        with self.assertRaises(TypeCheckError):
            self.require_type(Example("wrongFamily", actual.expression, wrong_type))

    def test_wrong_pair_projection_type_is_rejected(self) -> None:
        e, p = self.examples, self.program
        actual = e.projection(True)
        reader = p.commit().view(actual.type)
        binders = []
        current = actual.type
        for _ in range(3):
            fields = reader.fields(current)
            binders.append((fields["variable"], fields["domain"]))
            current = fields["codomain"]
        wrong_type = e.forall(tuple(binders), p.type_node(binders[1][0]))
        with self.assertRaises(TypeCheckError):
            self.require_type(Example("wrongProjection", actual.expression, wrong_type))

    def test_non_function_cannot_be_a_church_iteration_step(self) -> None:
        e, p = self.examples, self.program
        a, step, zero = e.variables(3)
        ta = p.type_node(a)
        bindings = ((a, e.u0), (step, e.arrows(ta, ta)), (zero, ta))
        invalid = e.lambdas(bindings, e.apply(zero, zero))
        with self.assertRaisesRegex(TypeCheckError, "function type"):
            self.require_type(Example("badNumeral", invalid, e.nat_type()))

    def test_small_church_boolean_cannot_be_instantiated_at_a_larger_universe(self) -> None:
        boolean = self.examples.boolean(True)
        invalid = self.examples.apply(boolean.expression, self.examples.u0)
        relation = self.program.relation("HasType", invalid, self.examples.u1)
        with self.assertRaisesRegex(TypeCheckError, "argument type"):
            self.program.commit().require(relation)

    def test_conversion_supports_the_matching_lean_function_eta_witness(self) -> None:
        self.require_type(self.examples.eta_conversion())

    def test_generated_substitutions_preserve_every_bound_position(self) -> None:
        e, p = self.examples, self.program
        for depth in range(6):
            for selected in range(depth + 1):
                with self.subTest(depth=depth, selected=selected):
                    outer = p.variable()
                    inner = e.variables(depth)
                    body = outer if selected == 0 else inner[selected - 1]
                    source = e.lambdas(tuple((v, e.u1) for v in inner), body)
                    function = p.lambda_(outer, e.u1, source)
                    application = p.apply(function, e.u0)
                    target_variables = e.variables(depth)
                    target_body = (
                        e.u0 if selected == 0 else target_variables[selected - 1]
                    )
                    expected = e.lambdas(
                        tuple((v, e.u1) for v in target_variables), target_body
                    )
                    relation = p.relation("BetaReduces", application, expected)
                    p.commit().require(relation)
                    self.assert_normalizes_to(application, expected)
                    expected_type = e.forall(
                        tuple((v, e.u1) for v in target_variables), e.u1
                    )
                    self.require_type(Example("substitution", application, expected_type))

    def test_alpha_renamed_large_example_still_has_the_same_type(self) -> None:
        first = self.examples.dependent_compose()
        second = self.examples.dependent_compose()
        self.require_type(Example("alphaEquivalent", first.expression, second.type))
        self.assert_normalizes_to(first.expression, second.expression)

    def test_wrong_result_is_rejected_not_merely_well_typed(self) -> None:
        true, false = self.examples.boolean(True), self.examples.boolean(False)
        self.require_type(true)
        self.require_type(false)
        snapshot = self.program.commit()
        reader = snapshot.view(true.expression, false.expression)._reader
        work = calculus.Work(10_000)
        actual = calculus.normalize(reader.term(true.expression, work), work)
        different = calculus.normalize(reader.term(false.expression, work), work)
        self.assertNotEqual(actual, different)

    def test_local_view_does_not_gain_access_to_other_examples(self) -> None:
        first, second = self.examples.identity(), self.examples.compose()
        snapshot = self.program.commit()
        local = snapshot.view(first.expression, first.type)
        for hidden in (second.expression, second.type, snapshot.root):
            with self.subTest(hidden=hidden.number):
                self.assertNotIn(hidden, local.nodes)
                with self.assertRaises(UnknownNodeError):
                    local.kind(hidden)

    def test_large_shared_expression_reports_a_budget_limit_not_false(self) -> None:
        e, p = self.examples, self.program
        a = p.variable()
        identity = p.lambda_(a, e.u1, a)
        expression = e.u0
        for _ in range(40):
            expression = p.apply(identity, expression)
        relation = p.relation("HasType", expression, e.u1)
        snapshot = p.commit()
        with self.assertRaises(CheckLimitError):
            snapshot.check(relation, max_steps=100)
        snapshot.require(relation, max_steps=100_000)

    def test_small_shared_type_dag_can_exhaust_the_default_decode_budget(self) -> None:
        e, p = self.examples, self.program
        shared = e.u0
        for _ in range(12):
            shared = p.function_type(p.variable(), shared, shared)
        relation = p.relation("HasType", shared, e.u1)
        snapshot = p.commit()
        # This is a performance limitation: decoding repeats shared subgraphs.
        self.assertLess(len(snapshot.view(shared).nodes), 150)
        with self.assertRaises(CheckLimitError):
            snapshot.view(shared)._reader.term(shared, calculus.Work(10_000))
        with self.assertRaises(CheckLimitError):
            snapshot.check(relation)

    def test_beta_result_survives_typechecking_after_substitution(self) -> None:
        e, p = self.examples, self.program
        for depth in (0, 1, 3, 5):
            with self.subTest(depth=depth):
                variable = p.variable()
                nested = e.variables(depth)
                body = e.lambdas(tuple((v, e.u1) for v in nested), variable)
                function = p.lambda_(variable, e.u1, body)
                application = p.apply(function, e.u0)
                expected = e.lambdas(tuple((v, e.u1) for v in nested), e.u0)
                relation = p.relation("BetaReduces", application, expected)
                p.commit().require(relation)
                type_node = e.forall(tuple((v, e.u1) for v in nested), e.u1)
                self.require_type(Example("beforeBeta", application, type_node))
                self.require_type(Example("afterBeta", expected, type_node))


if __name__ == "__main__":
    unittest.main()
