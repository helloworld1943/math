import unittest
from dataclasses import replace

from boolean_demo import BooleanExamples
from dependent import Proof, check
from dependent_demo import Scope, Typed
from relations import Call, DefinitionError, Node, ValidationError


class BooleanTests(unittest.TestCase):
    def setUp(self) -> None:
        self.examples = BooleanExamples()
        self.scope = self.examples.empty

    def require_type(self, value: Typed, scope: Scope | None = None) -> None:
        context = self.scope if scope is None else scope
        check(
            self.examples.graph, value.proof,
            Call("Typing", (context.name, value.term, value.type)),
        )

    def boolean_case(self, condition: Typed) -> Typed:
        examples = self.examples
        domain = examples.bool_type(self.scope)
        binder = examples.node("binder")
        child = examples.extend(self.scope, binder, domain)
        function_type = examples.pi(
            self.scope, binder, domain, child, examples.sort(child, 0)
        )
        motive = examples.lam(
            self.scope, binder, domain, child, examples.bool_type(child), function_type
        )
        yes_type = examples.app(self.scope, motive, examples.boolean(self.scope, True))
        no_type = examples.app(self.scope, motive, examples.boolean(self.scope, False))
        result_type = examples.app(self.scope, motive, condition)
        yes = examples.convert(
            self.scope, examples.boolean(self.scope, True), yes_type
        )
        no = examples.convert(
            self.scope, examples.boolean(self.scope, False), no_type
        )
        return examples.eliminate(
            self.scope, motive, condition, yes, no, yes_type, no_type, result_type
        )

    def test_boolean_type_and_constructors(self) -> None:
        self.require_type(self.examples.bool_type(self.scope))
        for value in (True, False):
            with self.subTest(value=value):
                self.require_type(self.examples.boolean(self.scope, value))

    def test_mixed_function_is_closed_and_well_typed(self) -> None:
        self.require_type(self.examples.mixed_function().function)

    def test_true_application_returns_a_type(self) -> None:
        examples = self.examples
        mixed = examples.mixed_function()
        applied = examples.app(
            self.scope, mixed.function, examples.boolean(self.scope, True)
        )
        converted = examples.convert(self.scope, applied, examples.sort(self.scope, 0))
        self.assertEqual(converted.type, "U0")
        self.require_type(converted)
        result, equality = examples.normalize(applied.term)
        self.assertEqual(result, "Bool")
        check(examples.graph, equality, Call("Equal", (applied.term, "Bool")))

    def test_false_application_returns_a_function(self) -> None:
        examples = self.examples
        mixed = examples.mixed_function()
        applied = examples.app(
            self.scope, mixed.function, examples.boolean(self.scope, False)
        )
        converted = examples.convert(self.scope, applied, mixed.identity_type)
        self.require_type(converted)
        result, equality = examples.normalize(applied.term)
        self.assertEqual(result, mixed.identity.term)
        self.assertEqual(examples.graph[result].kind, "lambda")
        check(examples.graph, equality, Call("Equal", (applied.term, result)))

    def test_returned_type_can_be_used_as_a_type(self) -> None:
        examples = self.examples
        mixed = examples.mixed_function()
        applied = examples.app(
            self.scope, mixed.function, examples.boolean(self.scope, True)
        )
        returned_type = examples.convert(
            self.scope, applied, examples.sort(self.scope, 0)
        )
        value = examples.convert(
            self.scope, examples.boolean(self.scope, True), returned_type
        )
        self.assertEqual(value.type, applied.term)
        self.require_type(value)

    def test_returned_function_can_be_called(self) -> None:
        examples = self.examples
        mixed = examples.mixed_function()
        applied = examples.app(
            self.scope, mixed.function, examples.boolean(self.scope, False)
        )
        returned_function = examples.convert(self.scope, applied, mixed.identity_type)
        specialized = examples.app(
            self.scope, returned_function, examples.bool_type(self.scope)
        )
        final = examples.app(
            self.scope, specialized, examples.boolean(self.scope, True)
        )
        self.assertEqual(final.type, "Bool")
        self.require_type(final)
        result, equality = examples.normalize(final.term)
        self.assertEqual(result, "true")
        check(examples.graph, equality, Call("Equal", (final.term, "true")))

    def test_function_value_cannot_be_used_as_a_type(self) -> None:
        examples = self.examples
        mixed = examples.mixed_function()
        applied = examples.app(
            self.scope, mixed.function, examples.boolean(self.scope, False)
        )
        returned_function = examples.convert(self.scope, applied, mixed.identity_type)
        invalid_context = examples.extend(self.scope, "invalid", returned_function)
        with self.assertRaisesRegex(ValidationError, "Sort"):
            check(
                examples.graph, invalid_context.proof,
                Call("Context", (invalid_context.name,)),
            )

    def test_unknown_boolean_keeps_result_symbolic(self) -> None:
        examples = self.examples
        mixed = examples.mixed_function()
        scope = examples.extend(self.scope, "unknown", examples.bool_type(self.scope))
        function = examples.weaken(mixed.function, self.scope, scope)
        applied = examples.app(scope, function, examples.reference(scope, "unknown"))
        self.require_type(applied, scope)
        for expression in (applied.term, applied.type):
            with self.subTest(expression=expression):
                result, equality = examples.normalize(expression)
                self.assertEqual(examples.graph[result].kind, "bool_elim")
                condition = examples.graph[result].edges["condition"]
                self.assertEqual(condition, "ref_unknown")
                check(examples.graph, equality, Call("Equal", (expression, result)))

    def test_unknown_boolean_cannot_be_assumed_true(self) -> None:
        examples = self.examples
        examples.graph["unknown"] = Node("binder")
        condition = examples.node("reference", binder="unknown")
        term = examples.node(
            "bool_elim", motive="U0", condition=condition,
            then_branch="true", else_branch="false",
        )
        proof = Proof("reduce_true", (term, "U0", condition, "true", "false"))
        with self.assertRaisesRegex(ValidationError, "True"):
            check(examples.graph, proof, Call("Equal", (term, "true")))

    def test_reject_non_boolean_function_argument(self) -> None:
        examples = self.examples
        mixed = examples.mixed_function()
        invalid = examples.app(self.scope, mixed.function, examples.sort(self.scope, 0))
        with self.assertRaisesRegex(ValidationError, "premise mismatch"):
            self.require_type(invalid)

    def test_both_literal_cases_reduce(self) -> None:
        examples = self.examples
        for argument in (True, False):
            with self.subTest(argument=argument):
                case = self.boolean_case(examples.boolean(self.scope, argument))
                self.require_type(case)
                result, equality = examples.normalize(case.term)
                expected = "true" if argument else "false"
                self.assertEqual(result, expected)
                check(examples.graph, equality, Call("Equal", (case.term, expected)))

    def test_reject_bad_dead_branch_even_when_condition_is_true(self) -> None:
        examples = self.examples
        case = self.boolean_case(examples.boolean(self.scope, True))
        original = examples.graph[case.term]
        examples.graph[case.term] = Node(
            "bool_elim", {**original.edges, "else_branch": "U0"}
        )
        arguments = list(case.proof.arguments)
        arguments[5] = "U0"
        forged = replace(
            case.proof, arguments=tuple(arguments),
            premises=(*case.proof.premises[:3], examples.sort(self.scope, 0).proof),
        )
        with self.assertRaisesRegex(ValidationError, "premise mismatch"):
            self.require_type(replace(case, proof=forged))

    def test_reject_missing_branch_proof(self) -> None:
        case = self.boolean_case(self.examples.boolean(self.scope, True))
        forged = replace(case.proof, premises=case.proof.premises[:-1])
        with self.assertRaisesRegex(DefinitionError, "premises"):
            self.require_type(replace(case, proof=forged))

    def test_reject_wrong_result_family_application(self) -> None:
        case = self.boolean_case(self.examples.boolean(self.scope, True))
        arguments = list(case.proof.arguments)
        arguments[-1] = arguments[-2]
        forged = replace(case.proof, arguments=tuple(arguments))
        invalid = replace(case, type=arguments[-1], proof=forged)
        with self.assertRaisesRegex(ValidationError, "App"):
            self.require_type(invalid)

    def test_reject_motive_with_non_boolean_domain(self) -> None:
        examples = self.examples
        case = self.boolean_case(examples.boolean(self.scope, True))
        arguments = list(case.proof.arguments)
        motive_type = arguments[6]
        original = examples.graph[motive_type]
        examples.graph[motive_type] = Node(
            "pi", {**original.edges, "domain": "U0"}
        )
        arguments[8] = "U0"
        invalid = replace(case, proof=replace(case.proof, arguments=tuple(arguments)))
        with self.assertRaisesRegex(ValidationError, "Bool"):
            self.require_type(invalid)

    def test_reject_motive_with_non_universe_codomain(self) -> None:
        examples = self.examples
        case = self.boolean_case(examples.boolean(self.scope, True))
        arguments = list(case.proof.arguments)
        motive_type = arguments[6]
        original = examples.graph[motive_type]
        examples.graph[motive_type] = Node("pi", {**original.edges, "body": "Bool"})
        arguments[9] = "Bool"
        invalid = replace(case, proof=replace(case.proof, arguments=tuple(arguments)))
        with self.assertRaisesRegex(ValidationError, "Sort"):
            self.require_type(invalid)

    def test_reject_wrong_branch_reduction(self) -> None:
        examples = self.examples
        case = self.boolean_case(examples.boolean(self.scope, False))
        node = examples.graph[case.term]
        proof = Proof(
            "reduce_true",
            (
                case.term, node.edges["motive"], "false",
                node.edges["then_branch"], node.edges["else_branch"],
            ),
        )
        with self.assertRaisesRegex(ValidationError, "True"):
            check(
                examples.graph, proof,
                Call("Equal", (case.term, node.edges["then_branch"])),
            )

    def test_condition_can_itself_compute(self) -> None:
        examples = self.examples
        domain = examples.bool_type(self.scope)
        binder = examples.node("binder")
        child = examples.extend(self.scope, binder, domain)
        function_type = examples.pi(
            self.scope, binder, domain, child, examples.bool_type(child)
        )
        identity = examples.lam(
            self.scope, binder, domain, child,
            examples.reference(child, binder), function_type,
        )
        condition = examples.app(
            self.scope, identity, examples.boolean(self.scope, True)
        )
        case = self.boolean_case(condition)
        self.require_type(case)
        result, equality = examples.normalize(case.term)
        self.assertEqual(result, "true")
        check(examples.graph, equality, Call("Equal", (case.term, "true")))

    def test_substitution_checks_all_four_children(self) -> None:
        examples = self.examples
        binder = examples.node("binder")
        reference = examples.node("reference", binder=binder)
        term = examples.node(
            "bool_elim", motive=reference, condition=reference,
            then_branch=reference, else_branch=reference,
        )
        result, proof = examples.substitute(term, binder, "true")
        self.assertEqual(set(examples.graph[result].edges.values()), {"true"})
        check(
            examples.graph, proof,
            Call("Substitute", (term, binder, "true", result)),
        )
        node = examples.graph[result]
        examples.graph[result] = Node(
            "bool_elim", {**node.edges, "else_branch": reference}
        )
        with self.assertRaises(ValidationError):
            check(
                examples.graph, proof,
                Call("Substitute", (term, binder, "true", result)),
            )

    def test_freshness_checks_all_four_children(self) -> None:
        examples = self.examples
        binder = examples.node("binder")
        reference = examples.node("reference", binder=binder)
        for label in ("motive", "condition", "then_branch", "else_branch"):
            with self.subTest(label=label):
                edges = dict(
                    motive="Bool", condition="true",
                    then_branch="true", else_branch="false",
                )
                edges[label] = reference
                term = examples.node("bool_elim", **edges)
                proof = examples.fresh(term, binder)
                with self.assertRaises(ValidationError):
                    check(examples.graph, proof, Call("Fresh", (term, binder)))

    def test_constant_substitution_and_freshness(self) -> None:
        examples = self.examples
        binder = examples.node("binder")
        for term in ("Bool", "true", "false"):
            with self.subTest(term=term):
                result, proof = examples.substitute(term, binder, "U0")
                self.assertEqual(result, term)
                check(
                    examples.graph, proof,
                    Call("Substitute", (term, binder, "U0", term)),
                )
                check(
                    examples.graph, examples.fresh(term, binder),
                    Call("Fresh", (term, binder)),
                )

    def test_weakening_rejects_binder_identity_collision(self) -> None:
        examples = self.examples
        identity = examples.identity(self.scope)
        binder = examples.graph[identity.term].edges["binder"]
        child = examples.extend(self.scope, binder, examples.bool_type(self.scope))
        invalid = examples.weaken(identity, self.scope, child)
        with self.assertRaisesRegex(ValidationError, "Different"):
            self.require_type(invalid, child)


if __name__ == "__main__":
    unittest.main()
