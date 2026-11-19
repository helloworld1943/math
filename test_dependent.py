import unittest
from dataclasses import replace

from dependent import Proof, _rule, check
from dependent_demo import Examples, Scope, Typed
from relations import Call, DefinitionError, Node, ValidationError


class DependentTests(unittest.TestCase):
    def setUp(self) -> None:
        self.examples = Examples()
        self.scope = self.examples.ambient()

    def require_type(self, value: Typed, scope: Scope | None = None) -> None:
        context = self.scope if scope is None else scope
        check(
            self.examples.graph, value.proof,
            Call("Typing", (context.name, value.term, value.type)),
        )

    def test_polymorphic_identity_type(self) -> None:
        self.require_type(self.examples.identity(self.scope))

    def test_dependent_application_substitutes_domain_and_result(self) -> None:
        examples = self.examples
        identity = examples.identity(self.scope)
        specialized = examples.app(
            self.scope, identity, examples.reference(self.scope, "N")
        )
        specialized_type = examples.graph[specialized.type]
        self.assertEqual(specialized_type.edges["domain"], "ref_N")
        self.assertEqual(specialized_type.edges["body"], "ref_N")
        applied = examples.app(
            self.scope, specialized, examples.reference(self.scope, "n")
        )
        self.assertEqual(applied.type, "ref_N")
        self.require_type(applied)

    def test_higher_universe_identity_returns_a_type(self) -> None:
        examples = self.examples
        identity = examples.identity(self.scope, level=1)
        specialized = examples.app(self.scope, identity, examples.sort(self.scope, 0))
        applied = examples.app(
            self.scope, specialized, examples.reference(self.scope, "N")
        )
        self.assertEqual(applied.type, "U0")
        self.require_type(applied)

    def test_same_function_can_return_a_type_or_an_ordinary_term(self) -> None:
        examples = self.examples
        under_large = examples.extend(
            examples.empty, "Large", examples.sort(examples.empty, 1)
        )
        binder = examples.node("binder")
        domain = examples.sort(under_large, 1)
        child = examples.extend(under_large, binder, domain)
        family_type = examples.pi(
            under_large, binder, domain, child,
            examples.reference(child, binder),
        )
        scope = examples.extend(under_large, "F", family_type)
        function = examples.reference(scope, "F")
        as_type = examples.app(scope, function, examples.sort(scope, 0))
        as_term = examples.app(scope, function, examples.reference(scope, "Large"))
        self.assertEqual(as_type.type, "U0")
        self.assertEqual(as_term.type, "ref_Large")
        self.require_type(as_type, scope)
        self.require_type(as_term, scope)

    def test_beta_equality_used_in_type_conversion(self) -> None:
        self.require_type(self.examples.converted_example(self.scope))

    def test_two_beta_steps_reduce_identity_application_to_argument(self) -> None:
        examples = self.examples
        identity = examples.identity(self.scope)
        n_type = examples.reference(self.scope, "N")
        n_value = examples.reference(self.scope, "n")
        specialized = examples.app(self.scope, identity, n_type)
        applied = examples.app(self.scope, specialized, n_value)
        outer = examples.graph[identity.term]
        reduced_fn, outer_subst = examples.substitute(
            outer.edges["body"], outer.edges["binder"], n_type.term
        )
        outer_beta = Proof(
            "beta",
            (
                specialized.term, identity.term, outer.edges["binder"],
                outer.edges["domain"], outer.edges["body"], n_type.term, reduced_fn,
            ),
            (outer_subst,),
        )
        middle = examples.node(
            "application", function=reduced_fn, argument=n_value.term
        )
        congruence = Proof(
            "equal_app",
            (
                applied.term, middle, specialized.term, n_value.term,
                reduced_fn, n_value.term,
            ),
            (outer_beta, Proof("equal_refl", (n_value.term,))),
        )
        inner = examples.graph[reduced_fn]
        result, inner_subst = examples.substitute(
            inner.edges["body"], inner.edges["binder"], n_value.term
        )
        inner_beta = Proof(
            "beta",
            (
                middle, reduced_fn, inner.edges["binder"], inner.edges["domain"],
                inner.edges["body"], n_value.term, result,
            ),
            (inner_subst,),
        )
        equality = Proof(
            "equal_trans", (applied.term, middle, result),
            (congruence, inner_beta),
        )
        self.assertEqual(result, n_value.term)
        check(examples.graph, equality, Call("Equal", (applied.term, n_value.term)))

    def test_universe_hierarchy(self) -> None:
        for level in range(4):
            with self.subTest(level=level):
                self.require_type(self.examples.sort(self.scope, level))

    def test_reject_self_typed_universe(self) -> None:
        proof = Proof(
            "type_sort", (self.scope.name, "U0", "U0"), (self.scope.proof,)
        )
        with self.assertRaisesRegex(ValidationError, "Successor"):
            check(
                self.examples.graph, proof,
                Call("Typing", (self.scope.name, "U0", "U0")),
            )

    def test_reject_wrong_pi_universe(self) -> None:
        identity = self.examples.identity(self.scope)
        type_proof = identity.proof.premises[0]
        forged = replace(
            type_proof, arguments=(*type_proof.arguments[:-1], "U0")
        )
        with self.assertRaisesRegex(ValidationError, "PiUniverse"):
            check(
                self.examples.graph, forged,
                Call("Typing", (self.scope.name, identity.type, "U0")),
            )

    def test_reject_wrong_argument_type(self) -> None:
        examples = self.examples
        wrong = examples.app(
            self.scope, examples.identity(self.scope),
            examples.reference(self.scope, "n"),
        )
        with self.assertRaisesRegex(ValidationError, "premise mismatch"):
            self.require_type(wrong)

    def test_reject_wrong_result_type(self) -> None:
        value = self.examples.reference(self.scope, "n")
        with self.assertRaisesRegex(ValidationError, "Conclusion mismatch"):
            check(
                self.examples.graph, value.proof,
                Call("Typing", (self.scope.name, value.term, "U0")),
            )

    def test_reject_forged_reference_link(self) -> None:
        value = self.examples.reference(self.scope, "N")
        self.examples.graph[value.term] = Node("reference", {"binder": "n"})
        with self.assertRaisesRegex(ValidationError, "_type_ref"):
            self.require_type(value)

    def test_reject_out_of_scope_reference(self) -> None:
        examples = self.examples
        examples.graph["orphan"] = Node("binder")
        examples.graph["ref_orphan"] = Node("reference", {"binder": "orphan"})
        lookup = Proof("lookup_here", ("empty", "empty", "orphan", "U0"))
        proof = Proof(
            "type_ref", ("empty", "ref_orphan", "orphan", "U0"),
            (examples.empty.proof, lookup),
        )
        with self.assertRaisesRegex(ValidationError, "_lookup_here"):
            check(
                examples.graph, proof,
                Call("Typing", ("empty", "ref_orphan", "U0")),
            )

    def test_reject_duplicate_binder_in_context(self) -> None:
        examples = self.examples
        duplicate = examples.extend(
            self.scope, "N", examples.sort(self.scope, 0)
        )
        with self.assertRaisesRegex(ValidationError, "Different"):
            check(examples.graph, duplicate.proof, Call("Context", (duplicate.name,)))

    def test_reject_forged_substitution(self) -> None:
        self.examples.graph["ref_N"] = Node("reference", {"binder": "N"})
        proof = Proof("subst_hit", ("ref_N", "N", "U0", "U1"))
        with self.assertRaisesRegex(ValidationError, "Same"):
            check(
                self.examples.graph, proof,
                Call("Substitute", ("ref_N", "N", "U0", "U1")),
            )

    def test_reject_capture(self) -> None:
        examples = self.examples
        examples.graph["x"] = Node("binder")
        examples.graph["y"] = Node("binder")
        ref_x = examples.node("reference", binder="x")
        ref_y = examples.node("reference", binder="y")
        term = examples.node("lambda", binder="y", domain="U0", body=ref_x)
        result, proof = examples.substitute(term, "x", ref_y)
        with self.assertRaisesRegex(ValidationError, "Different"):
            check(
                examples.graph, proof,
                Call("Substitute", (term, "x", ref_y, result)),
            )

    def test_reject_bound_identifier_collision_without_renaming(self) -> None:
        examples = self.examples
        examples.graph["x"] = Node("binder")
        examples.graph["y"] = Node("binder")
        ref_x = examples.node("reference", binder="x")
        ref_y = examples.node("reference", binder="y")
        term = examples.node("lambda", binder="y", domain="U0", body=ref_x)
        argument = examples.node("lambda", binder="y", domain="U0", body=ref_y)
        result, proof = examples.substitute(term, "x", argument)
        with self.assertRaises(ValidationError):
            check(
                examples.graph, proof,
                Call("Substitute", (term, "x", argument, result)),
            )

    def test_substitution_through_applications_and_pi(self) -> None:
        examples = self.examples
        examples.graph["x"] = Node("binder")
        examples.graph["y"] = Node("binder")
        ref_x = examples.node("reference", binder="x")
        app = examples.node("application", function=ref_x, argument="U0")
        term = examples.node("pi", binder="y", domain=ref_x, body=app)
        result, proof = examples.substitute(term, "x", "U1")
        check(
            examples.graph, proof,
            Call("Substitute", (term, "x", "U1", result)),
        )
        result_node = examples.graph[result]
        self.assertEqual(result_node.edges["domain"], "U1")
        body = examples.graph[result_node.edges["body"]]
        self.assertEqual(body.edges["function"], "U1")
        self.assertEqual(body.edges["argument"], "U0")

    def test_substitution_stops_in_body_but_not_domain(self) -> None:
        examples = self.examples
        examples.graph["x"] = Node("binder")
        ref_x = examples.node("reference", binder="x")
        term = examples.node("pi", binder="x", domain=ref_x, body=ref_x)
        result, proof = examples.substitute(term, "x", "U0")
        check(
            examples.graph, proof,
            Call("Substitute", (term, "x", "U0", result)),
        )
        self.assertEqual(examples.graph[result].edges["domain"], "U0")
        self.assertEqual(examples.graph[result].edges["body"], ref_x)

    def test_substitution_at_multiple_depths(self) -> None:
        examples = self.examples
        examples.graph["x"] = Node("binder")
        reference = examples.node("reference", binder="x")
        counts = []
        for depth in (0, 1, 5, 20, 40):
            term = reference
            for _ in range(depth):
                binder = examples.node("binder")
                term = examples.node("lambda", binder=binder, domain="U0", body=term)
            result, proof = examples.substitute(term, "x", "U1")
            checked = check(
                examples.graph, proof,
                Call("Substitute", (term, "x", "U1", result)),
            )
            counts.append(checked.explicit_objects)
            current = result
            for _ in range(depth):
                current = examples.graph[current].edges["body"]
            self.assertEqual(current, "U1")
        self.assertEqual(counts, sorted(set(counts)))

    def test_typing_nested_functions(self) -> None:
        examples = self.examples

        def nested(scope: Scope, depth: int) -> tuple[Typed, Typed]:
            if depth == 0:
                return examples.sort(scope, 0), examples.sort(scope, 1)
            binder = examples.node("binder")
            domain = examples.sort(scope, 0)
            child = examples.extend(scope, binder, domain)
            body, body_type = nested(child, depth - 1)
            function_type = examples.pi(scope, binder, domain, child, body_type)
            term = examples.lam(scope, binder, domain, child, body, function_type)
            return term, function_type

        for depth in (1, 3, 6):
            with self.subTest(depth=depth):
                term, _ = nested(self.scope, depth)
                self.require_type(term)

    def test_substitution_stops_under_lambda(self) -> None:
        examples = self.examples
        examples.graph["x"] = Node("binder")
        ref_x = examples.node("reference", binder="x")
        term = examples.node("lambda", binder="x", domain="U0", body=ref_x)
        result, proof = examples.substitute(term, "x", "U1")
        self.assertEqual(result, term)
        check(
            examples.graph, proof,
            Call("Substitute", (term, "x", "U1", term)),
        )

    def test_reject_mismatched_equality_chain(self) -> None:
        proof = Proof(
            "equal_trans", ("U0", "U1", "U0"),
            (Proof("equal_refl", ("U0",)), Proof("equal_refl", ("U0",))),
        )
        with self.assertRaisesRegex(ValidationError, "premise mismatch"):
            check(self.examples.graph, proof, Call("Equal", ("U0", "U0")))

    def test_equality_congruence_under_binders(self) -> None:
        examples = self.examples
        identity = examples.type_identity(self.scope)
        redex = examples.app(
            self.scope, identity, examples.reference(self.scope, "N")
        )
        function = examples.graph[identity.term]
        binder, domain, body = (
            function.edges[key] for key in ("binder", "domain", "body")
        )
        result, substitution = examples.substitute(body, binder, "ref_N")
        beta = Proof(
            "beta",
            (
                redex.term, identity.term, binder, domain,
                body, "ref_N", result,
            ),
            (substitution,),
        )
        outer_binder = examples.node("binder")
        for kind in ("lambda", "pi"):
            with self.subTest(kind=kind):
                left = examples.node(
                    kind, binder=outer_binder, domain="U0", body=redex.term
                )
                right = examples.node(
                    kind, binder=outer_binder, domain="U0", body=result
                )
                equality = Proof(
                    f"equal_{kind}",
                    (left, right, outer_binder, "U0", redex.term, "U0", result),
                    (Proof("equal_refl", ("U0",)), beta),
                )
                check(examples.graph, equality, Call("Equal", (left, right)))

    def test_freshness_decomposes_through_all_term_shapes(self) -> None:
        examples = self.examples
        x, y = examples.node("binder"), examples.node("binder")
        ref_x = examples.node("reference", binder=x)
        application = examples.node("application", function=ref_x, argument="U0")
        pi = examples.node("pi", binder=y, domain="U0", body=application)
        term = examples.node("lambda", binder=x, domain="U1", body=pi)
        proof = examples.fresh(term, "N")
        check(examples.graph, proof, Call("Fresh", (term, "N")))

    def test_rule_templates_reject_hidden_arguments(self) -> None:
        with self.assertRaisesRegex(DefinitionError, "Hidden rule parameters"):
            _rule("x", "Example x", ("Same x hidden",))

    def test_reject_missing_witness(self) -> None:
        with self.assertRaisesRegex(DefinitionError, "explicit arguments"):
            check(
                self.examples.graph, Proof("subst_sort", ("U0",)),
                Call("Substitute", ("U0", "N", "U1", "U0")),
            )

    def test_reject_omitted_premises(self) -> None:
        value = self.examples.sort(self.scope, 0)
        with self.assertRaisesRegex(DefinitionError, "premises"):
            self.require_type(replace(value, proof=replace(value.proof, premises=())))

    def test_reject_unknown_rule(self) -> None:
        with self.assertRaisesRegex(DefinitionError, "Unknown proof rule"):
            check(self.examples.graph, Proof("trust_me", ()), Call("Typing", ()))

    def test_reject_circular_evidence(self) -> None:
        proof = Proof("equal_symm", ("U0", "U0"))
        object.__setattr__(proof, "premises", (proof,))
        with self.assertRaisesRegex(DefinitionError, "Cyclic proof graph"):
            check(self.examples.graph, proof, Call("Equal", ("U0", "U0")))


if __name__ == "__main__":
    unittest.main()
