import unittest
from types import MappingProxyType

from node import GraphSnapshot, IncomingRootLinkError, Node, UnknownNodeError

from . import CheckLimitError, EncodingError, Program, Snapshot, TypeCheckError


class Layer1Tests(unittest.TestCase):
    def setUp(self) -> None:
        self.program = Program()
        self.u0, self.u1, self.u2 = (
            self.program.universe(n) for n in range(3)
        )

    def has_type(self, expression: Node, supplied: Node) -> None:
        relation = self.program.relation("HasType", expression, supplied)
        self.program.commit().require(relation)

    def beta(self, expression: Node, supplied: Node) -> None:
        relation = self.program.relation("BetaReduces", expression, supplied)
        self.program.commit().require(relation)

    def identity(self, domain: Node) -> tuple[Node, Node]:
        x = self.program.variable()
        return (
            self.program.lambda_(x, domain, x),
            self.program.function_type(x, domain, domain),
        )

    def test_three_distinct_expression_kinds(self) -> None:
        function, function_type = self.identity(self.u1)
        application = self.program.apply(function, self.u0)
        for node in (function, function_type, application):
            self.assertIsInstance(node, Node)
        view = self.program.commit().view(function, function_type, application)
        self.assertEqual(view.kind(function), "Lambda")
        self.assertEqual(view.kind(function_type), "TypeNode")
        self.assertEqual(view.form(function_type), "function")
        self.assertEqual(view.kind(application), "Application")
        self.assertEqual(
            dict(view.fields(application)),
            {"function": function, "argument": self.u0},
        )

    def test_universe_hierarchy_without_context(self) -> None:
        self.has_type(self.u0, self.u1)
        self.has_type(self.u1, self.u2)

    def test_universe_levels_have_no_fixed_ceiling(self) -> None:
        for n in (0, 1, 2, 3, 16, 255, 256, 2**128):
            with self.subTest(n=n):
                node = self.program.universe(n)
                self.assertEqual(self.program.commit().view(node).level(node), n)
                self.has_type(node, self.program.universe(n + 1))

    def test_invalid_universe_levels_do_not_change_graph(self) -> None:
        before = self.program.commit().graph.nodes
        for level in (-1, True, 1.5, "1"):
            with self.subTest(level=level):
                with self.assertRaises(ValueError):
                    self.program.universe(level)  # type: ignore[arg-type]
        self.assertEqual(before, self.program.commit().graph.nodes)

    def test_repeated_universe_request_reuses_node(self) -> None:
        self.assertIs(self.program.universe(0), self.u0)

    def test_reject_self_typing_and_skipped_universe_level(self) -> None:
        for supplied in (self.u0, self.u2):
            with self.subTest(supplied=supplied):
                relation = self.program.relation("HasType", self.u0, supplied)
                snapshot = self.program.commit()
                self.assertFalse(snapshot.check(relation))
                with self.assertRaises(TypeCheckError):
                    snapshot.require(relation)

    def test_identity_function_type_and_application(self) -> None:
        function, function_type = self.identity(self.u1)
        self.has_type(function, function_type)
        application = self.program.apply(function, self.u0)
        self.has_type(application, self.u1)
        self.beta(application, self.u0)

    def test_function_type_has_universe_maximum(self) -> None:
        x = self.program.variable()
        function_type = self.program.function_type(x, self.u0, self.u1)
        self.has_type(function_type, self.u2)
        with self.assertRaises(TypeCheckError):
            self.has_type(function_type, self.u1)

    def test_universe_and_function_type_level_tables(self) -> None:
        p = self.program
        universes = [p.universe(n) for n in range(5)]
        checks: list[tuple[Node, bool]] = []
        for i in range(4):
            for j in range(5):
                checks.append((p.relation("HasType", universes[i], universes[j]), j == i + 1))
            for j in range(4):
                variable = p.variable()
                function_type = p.function_type(variable, universes[i], universes[j])
                for k in range(5):
                    checks.append((
                        p.relation("HasType", function_type, universes[k]),
                        k == max(i + 1, j + 1),
                    ))
        snapshot = p.commit()
        for relation, expected in checks:
            with self.subTest(relation=relation.number, expected=expected):
                self.assertEqual(snapshot.check(relation), expected)

    def test_lambda_and_its_type_can_use_different_binder_identities(self) -> None:
        function, _ = self.identity(self.u1)
        y = self.program.variable()
        supplied = self.program.function_type(y, self.u1, self.u1)
        self.has_type(function, supplied)

    def test_dependent_identity_and_specialization(self) -> None:
        p = self.program
        a, x = p.variable(), p.variable()
        inner = p.lambda_(x, a, x)
        inner_type = p.function_type(x, a, a)
        function = p.lambda_(a, self.u1, inner)
        function_type = p.function_type(a, self.u1, inner_type)
        self.has_type(function, function_type)
        application = p.apply(function, self.u0)
        supplied = p.function_type(x, self.u0, self.u0)
        self.has_type(application, supplied)
        self.beta(application, p.lambda_(x, self.u0, x))

    def test_application_function_may_itself_be_an_application(self) -> None:
        p = self.program
        a, x = p.variable(), p.variable()
        inner = p.lambda_(x, a, x)
        polymorphic = p.lambda_(a, self.u2, inner)
        specialized = p.apply(polymorphic, self.u1)
        application = p.apply(specialized, self.u0)
        self.has_type(application, self.u1)

    def test_reject_wrong_argument_type(self) -> None:
        function, _ = self.identity(self.u0)
        with self.assertRaisesRegex(TypeCheckError, "argument type"):
            self.has_type(self.program.apply(function, self.u0), self.u0)

    def test_reject_wrong_application_result_type(self) -> None:
        function, _ = self.identity(self.u1)
        with self.assertRaisesRegex(TypeCheckError, "supplied type"):
            self.has_type(self.program.apply(function, self.u0), self.u2)

    def test_reject_applying_a_non_function(self) -> None:
        with self.assertRaisesRegex(TypeCheckError, "function type"):
            self.has_type(self.program.apply(self.u0, self.u0), self.u1)

    def test_reject_free_variable(self) -> None:
        variable = self.program.variable()
        with self.assertRaisesRegex(TypeCheckError, "not bound"):
            self.has_type(variable, self.u0)

    def test_reject_variable_from_a_different_function(self) -> None:
        p = self.program
        x, y = p.variable(), p.variable()
        p.lambda_(x, self.u1, x)
        invalid = p.lambda_(y, self.u1, x)
        supplied = p.function_type(y, self.u1, self.u1)
        with self.assertRaisesRegex(TypeCheckError, "not bound"):
            self.has_type(invalid, supplied)

    def test_reject_parameter_in_its_own_domain(self) -> None:
        x = self.program.variable()
        invalid = self.program.lambda_(x, x, x)
        with self.assertRaisesRegex(TypeCheckError, "not bound"):
            self.has_type(invalid, self.u0)

    def test_reject_non_type_domain(self) -> None:
        p = self.program
        function, _ = self.identity(self.u1)
        x = p.variable()
        invalid = p.lambda_(x, function, x)
        with self.assertRaisesRegex(TypeCheckError, "domain"):
            self.has_type(invalid, self.u1)

    def test_reject_non_type_codomain(self) -> None:
        p = self.program
        function, _ = self.identity(self.u1)
        x = p.variable()
        invalid = p.function_type(x, self.u1, function)
        with self.assertRaisesRegex(TypeCheckError, "codomain"):
            self.has_type(invalid, self.u1)

    def test_reject_function_value_supplied_as_a_type(self) -> None:
        function, _ = self.identity(self.u1)
        with self.assertRaisesRegex(TypeCheckError, "supplied type"):
            self.has_type(self.u0, function)

    def test_beta_result_is_not_a_new_node_type(self) -> None:
        function, _ = self.identity(self.u1)
        application = self.program.apply(function, self.u0)
        self.beta(application, self.u0)
        self.assertEqual(
            self.program.commit().view(self.u0).kind(self.u0), "Universe"
        )

    def test_beta_reduction_substitutes_beneath_another_binder(self) -> None:
        p = self.program
        x, y = p.variable(), p.variable()
        function = p.lambda_(x, self.u1, p.lambda_(y, self.u1, x))
        application = p.apply(function, self.u0)
        self.beta(application, p.lambda_(y, self.u1, self.u0))
        with self.assertRaisesRegex(TypeCheckError, "single beta"):
            self.beta(application, p.lambda_(y, self.u1, y))

    def test_beta_can_return_a_dependent_function_type(self) -> None:
        p = self.program
        a, x = p.variable(), p.variable()
        function = p.lambda_(a, self.u1, p.function_type(x, a, a))
        application = p.apply(function, self.u0)
        supplied = p.function_type(x, self.u0, self.u0)
        self.beta(application, supplied)
        self.has_type(application, self.u1)

    def test_substitution_preserves_multiple_dependent_binders(self) -> None:
        p = self.program
        a, b, x, y = (p.variable() for _ in range(4))
        body = p.lambda_(b, self.u1, p.lambda_(x, a, p.lambda_(y, b, x)))
        function = p.lambda_(a, self.u1, body)
        application = p.apply(function, self.u0)
        expected = p.lambda_(b, self.u1, p.lambda_(x, self.u0, p.lambda_(y, b, x)))
        expected_type = p.function_type(
            b, self.u1, p.function_type(x, self.u0, p.function_type(y, b, self.u0))
        )
        self.beta(application, expected)
        self.has_type(application, expected_type)
        self.has_type(expected, expected_type)

    def test_substitution_renaming_does_not_capture_shared_binder_identity(self) -> None:
        p = self.program
        x, y = p.variable(), p.variable()
        argument = p.lambda_(y, self.u1, y)
        argument_type = p.function_type(y, self.u1, self.u1)
        function = p.lambda_(x, argument_type, p.lambda_(y, self.u1, x))
        application = p.apply(function, argument)
        outer, inner = p.variable(), p.variable()
        expected = p.lambda_(outer, self.u1, p.lambda_(inner, self.u1, inner))
        self.beta(application, expected)
        supplied_type = p.function_type(outer, self.u1, argument_type)
        self.has_type(application, supplied_type)
        wrong = p.lambda_(outer, self.u1, p.lambda_(inner, self.u1, outer))
        with self.assertRaises(TypeCheckError):
            self.beta(application, wrong)

    def test_type_conversion_reduces_under_a_binder(self) -> None:
        p = self.program
        identity, _ = self.identity(self.u1)
        a, x = p.variable(), p.variable()
        function = p.lambda_(a, self.u1, p.lambda_(x, a, x))
        computed_a = p.apply(identity, a)
        supplied_inner = p.function_type(x, computed_a, computed_a)
        supplied = p.function_type(a, self.u1, supplied_inner)
        self.has_type(function, supplied)

    def test_beta_is_one_step_not_full_evaluation(self) -> None:
        p = self.program
        identity, _ = self.identity(self.u1)
        inner = p.apply(identity, self.u0)
        outer = p.apply(identity, inner)
        self.beta(outer, inner)
        with self.assertRaises(TypeCheckError):
            self.beta(outer, self.u0)

    def test_beta_does_not_silently_assert_typing(self) -> None:
        function, _ = self.identity(self.u0)
        invalid_application = self.program.apply(function, self.u0)
        self.beta(invalid_application, self.u0)
        with self.assertRaises(TypeCheckError):
            self.has_type(invalid_application, self.u0)

    def test_beta_rejects_non_redex(self) -> None:
        with self.assertRaisesRegex(TypeCheckError, "Application of a Lambda"):
            self.beta(self.u0, self.u0)

    def test_argument_order_and_repetition_survive_plain_links(self) -> None:
        p = self.program
        first = p.relation("HasType", self.u0, self.u1)
        reversed_relation = p.relation("HasType", self.u1, self.u0)
        repeated = p.relation("HasType", self.u0, self.u0)
        snapshot = p.commit()
        self.assertTrue(snapshot.check(first))
        self.assertFalse(snapshot.check(reversed_relation))
        self.assertFalse(snapshot.check(repeated))
        fields = snapshot.view(repeated).fields(repeated)
        self.assertIs(fields["first"], self.u0)
        self.assertIs(fields["second"], self.u0)
        self.assertIsInstance(fields, MappingProxyType)

    def test_local_view_cannot_read_root_or_unrelated_node(self) -> None:
        p = self.program
        function, _ = self.identity(self.u1)
        application = p.apply(function, self.u0)
        snapshot = p.commit()
        local = snapshot.view(application)
        self.assertIn(function, local.nodes)
        self.assertNotIn(self.u2, local.nodes)
        self.assertNotIn(snapshot.root, local.nodes)
        for hidden in (self.u2, snapshot.root):
            with self.subTest(hidden=hidden):
                with self.assertRaises(UnknownNodeError):
                    local.kind(hidden)
                with self.assertRaises(UnknownNodeError):
                    local.children(hidden)
                with self.assertRaises(UnknownNodeError):
                    local.view(hidden)

    def test_arguments_do_not_see_their_incoming_relation_node(self) -> None:
        relation = self.program.relation("HasType", self.u0, self.u1)
        snapshot = self.program.commit()
        view = snapshot.view(self.u0, self.u1)
        self.assertNotIn(relation, view.nodes)
        self.assertTrue(snapshot.view(relation).check(relation))
        with self.assertRaises(UnknownNodeError):
            view.check(relation)

    def test_checks_do_not_create_or_change_program_nodes(self) -> None:
        p = self.program
        function, function_type = self.identity(self.u1)
        relation = p.relation("HasType", function, function_type)
        snapshot = p.commit()
        before = {node: snapshot.graph.children(node) for node in snapshot.graph.nodes}
        snapshot.require(relation)
        self.assertEqual(
            before, {node: snapshot.graph.children(node) for node in snapshot.graph.nodes}
        )
        self.assertEqual(snapshot.graph.nodes, p.commit().graph.nodes)

    def test_old_snapshot_survives_later_builder_changes(self) -> None:
        relation = self.program.relation("HasType", self.u0, self.u1)
        first = self.program.commit()
        unrelated = self.program.universe(10)
        second = self.program.commit()
        self.assertNotIn(unrelated, first.graph.nodes)
        self.assertIn(unrelated, second.graph.nodes)
        first.require(relation)
        second.require(relation)

    def test_unrelated_malformed_node_does_not_affect_local_check(self) -> None:
        p = self.program
        valid = p.relation("HasType", self.u0, self.u1)
        unrelated = p.apply(self.u0, self.u1)
        p.graph.add_link(unrelated, self.u2)
        bad = p.relation("HasType", unrelated, self.u1)
        snapshot = p.commit()
        self.assertTrue(snapshot.check(valid))
        with self.assertRaises(EncodingError):
            snapshot.check(bad)

    def test_unknown_kinds_and_wrong_arity_do_not_allocate_nodes(self) -> None:
        before = self.program.commit().graph.nodes
        with self.assertRaisesRegex(EncodingError, "Unknown relation"):
            self.program.relation("UserDefined", self.u0, self.u1)
        for arguments in ((), (self.u0,), (self.u0, self.u1, self.u2)):
            with self.subTest(arguments=arguments):
                with self.assertRaisesRegex(EncodingError, "two arguments"):
                    self.program.relation("HasType", *arguments)
        self.assertEqual(before, self.program.commit().graph.nodes)

    def test_cross_program_nodes_are_rejected(self) -> None:
        foreign = Program().universe(0)
        before = self.program.commit().graph.nodes
        with self.assertRaises(UnknownNodeError):
            self.program.apply(self.u0, foreign)
        with self.assertRaises(UnknownNodeError):
            self.program.relation("HasType", foreign, self.u1)
        self.assertEqual(before, self.program.commit().graph.nodes)

    def test_binder_must_be_a_variable_node(self) -> None:
        before = self.program.commit().graph.nodes
        with self.assertRaisesRegex(EncodingError, "Variable"):
            self.program.lambda_(self.u0, self.u1, self.u0)
        self.assertEqual(before, self.program.commit().graph.nodes)

    def test_reusing_a_nested_binder_identity_is_rejected(self) -> None:
        p = self.program
        x = p.variable()
        nested = p.lambda_(x, self.u1, p.lambda_(x, self.u1, x))
        with self.assertRaisesRegex(EncodingError, "distinct identities"):
            self.has_type(nested, self.u1)

    def test_malformed_structure_is_not_a_false_result(self) -> None:
        p = self.program
        function, _ = self.identity(self.u1)
        relation = p.relation("HasType", function, self.u1)
        p.graph.add_link(function, self.u2)
        with self.assertRaises(EncodingError):
            p.commit().check(relation)

    def test_duplicate_field_is_rejected(self) -> None:
        p = self.program
        function, _ = self.identity(self.u1)
        application = p.apply(function, self.u0)
        valid = p.commit()
        argument_slot = next(
            slot for slot in valid.graph.children(application)
            if self.u0 in valid.graph.children(slot)
        )
        duplicate = p.graph.create_node()
        p.graph.add_link(application, duplicate)
        for target in valid.graph.children(argument_slot):
            p.graph.add_link(duplicate, target)
        with self.assertRaisesRegex(EncodingError, "Duplicate"):
            p.commit().view(application).fields(application)

    def test_structural_expression_cycles_are_rejected(self) -> None:
        p = self.program
        function, _ = self.identity(self.u1)
        application = p.apply(function, self.u0)
        relation = p.relation("HasType", application, self.u1)
        valid = p.commit()
        function_slot = next(
            slot for slot in valid.graph.children(application)
            if function in valid.graph.children(slot)
        )
        role = next(iter(valid.graph.children(function_slot) - {function}))
        links = {
            node: valid.graph.children(node) for node in valid.graph.nodes
        }
        links[function_slot] = frozenset((role, application))
        cyclic = Snapshot(GraphSnapshot(links, valid.root), valid._vocabulary)
        with self.assertRaisesRegex(EncodingError, "cycle"):
            cyclic.require(relation)

    def test_primitive_metadata_cannot_be_modified_to_grant_access(self) -> None:
        p = self.program
        relation = p.relation("HasType", self.u0, self.u1)
        snapshot = p.commit()
        marker = next(
            node for node in snapshot.graph.children(self.u0)
            if not snapshot.graph.children(node)
        )
        p.graph.add_link(marker, self.u2)
        with self.assertRaisesRegex(EncodingError, "marker"):
            p.commit().check(relation)
        snapshot.require(relation)

    def test_check_budget_errors_are_not_false(self) -> None:
        relation = self.program.relation("HasType", self.u0, self.u1)
        snapshot = self.program.commit()
        for method in (snapshot.require, snapshot.check):
            with self.subTest(method=method.__name__):
                with self.assertRaises(CheckLimitError):
                    method(relation, max_steps=1)
        with self.assertRaises(ValueError):
            snapshot.check(relation, max_steps=0)

    def test_root_cannot_be_a_graph_stored_argument(self) -> None:
        with self.assertRaises(UnknownNodeError):
            self.program.relation("HasType", self.program.graph.root, self.u0)
        with self.assertRaises(IncomingRootLinkError):
            self.program.graph.add_link(self.u0, self.program.graph.root)

if __name__ == "__main__":
    unittest.main()
