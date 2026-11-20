import unittest

from layer0 import GraphSnapshot, Node, UnknownNodeError

from . import CheckLimitError, EncodingError, Program, Snapshot, TypeCheckError


class TypeNodeTests(unittest.TestCase):
    def setUp(self) -> None:
        self.program = Program()
        self.u0, self.u1, self.u2 = (
            self.program.universe(n) for n in range(3)
        )
        self.t0 = self.program.type_node(self.u0)
        self.t1 = self.program.type_node(self.u1)

    def has_type(self, expression: Node, supplied: Node) -> None:
        relation = self.program.relation("HasType", expression, supplied)
        self.program.commit().require(relation)

    def beta(self, application: Node, supplied: Node) -> None:
        relation = self.program.relation("BetaReduces", application, supplied)
        self.program.commit().require(relation)

    def identity(self, domain: Node) -> tuple[Node, Node]:
        p = self.program
        x = p.variable()
        return p.lambda_(x, domain, x), p.function_type(x, domain, domain)

    def value_application(self) -> tuple[Node, Node]:
        p = self.program
        value, value_type = self.identity(self.u1)
        variable = p.variable()
        identity = p.lambda_(variable, value_type, variable)
        return p.apply(identity, value), value_type

    def changed_field(self, node: Node, role: str, value: Node) -> Snapshot:
        original = self.program.commit()
        marker = original._vocabulary.roles[role]
        slot = next(
            child for child in original.graph.children(node)
            if marker in original.graph.children(child)
        )
        links = {
            entry: original.graph.children(entry) for entry in original.graph.nodes
        }
        links[slot] = frozenset((marker, value))
        return Snapshot(
            GraphSnapshot(links, original.root), original._vocabulary
        )

    def test_type_node_is_an_explicit_layer0_node(self) -> None:
        _, function_type = self.identity(self.u1)
        snapshot = self.program.commit()
        local = snapshot.view(function_type)
        self.assertIsInstance(function_type, Node)
        self.assertEqual(local.kind(function_type), "TypeNode")
        self.assertEqual(local.form(function_type), "function")
        self.assertEqual(
            set(local.fields(function_type)), {"form", "variable", "domain", "codomain"}
        )
        self.assertEqual(local.kind(self.u1), "Universe")

    def test_universe_type_handles_can_be_checked(self) -> None:
        self.has_type(self.u0, self.t1)
        self.has_type(self.t0, self.u1)
        self.has_type(self.t0, self.t1)
        with self.assertRaises(TypeCheckError):
            self.has_type(self.t0, self.t0)

    def test_existing_types_are_reused_without_generic_wrappers(self) -> None:
        p = self.program
        _, function_type = self.identity(self.u1)
        before = p.commit().graph.nodes
        self.assertIs(p.type_node(self.u0), self.u0)
        self.assertIs(p.type_node(function_type), function_type)
        self.assertEqual(p.commit().graph.nodes, before)
        self.has_type(self.u0, p.type_node(self.u1))

    def test_shared_type_handle_is_reused_by_multiple_functions(self) -> None:
        f, ft = self.identity(self.t1)
        g, gt = self.identity(self.t1)
        snapshot = self.program.commit()
        for expression in (f, ft, g, gt):
            self.assertIs(snapshot.view(expression).fields(expression)["domain"], self.t1)
        self.has_type(f, self.program.type_node(ft))
        self.has_type(g, self.program.type_node(gt))

    def test_function_type_already_is_a_type_node_without_an_application_type_field(self) -> None:
        function, function_type = self.identity(self.t1)
        handle = self.program.type_node(function_type)
        self.assertIs(handle, function_type)
        self.assertNotIn("FunctionType", self.program._vocabulary.kinds)
        self.has_type(function, handle)
        self.has_type(handle, self.u2)
        application = self.program.apply(function, self.t0)
        fields = self.program.commit().view(application).fields(application)
        self.assertEqual(set(fields), {"function", "argument"})
        self.has_type(application, self.t1)

    def test_type_handle_can_be_passed_as_an_argument_and_returned(self) -> None:
        function, _ = self.identity(self.t1)
        application = self.program.apply(function, self.t0)
        self.has_type(application, self.t1)
        self.beta(application, self.t0)
        self.beta(application, self.u0)

    def test_function_form_can_itself_be_passed_and_returned_as_a_type(self) -> None:
        p = self.program
        _, function_type = self.identity(self.u1)
        variable = p.variable()
        identity = p.lambda_(variable, self.u2, variable)
        application = p.apply(identity, function_type)
        self.has_type(application, self.u2)
        self.beta(application, function_type)
        self.has_type(p.type_node(application), self.u2)

    def test_type_described_by_an_application_is_not_eagerly_evaluated(self) -> None:
        p = self.program
        function, _ = self.identity(self.u1)
        application = p.apply(function, self.u0)
        type_handle = p.type_node(application)
        view = p.commit().view(type_handle)
        self.assertEqual(view.form(type_handle), "application")
        self.assertEqual(view.kind(view.fields(type_handle)["expression"]), "Application")
        self.has_type(type_handle, self.u1)
        y = p.variable()
        other_function = p.lambda_(y, type_handle, y)
        other_type = p.function_type(y, self.u0, self.u0)
        self.has_type(other_function, p.type_node(other_type))
        self.assertIs(p.commit().view(type_handle).fields(type_handle)["expression"], application)

    def test_type_node_does_not_certify_an_invalid_type(self) -> None:
        p = self.program
        value, value_type = self.value_application()
        invalid = p.type_node(value)
        snapshot = p.commit()
        self.assertEqual(snapshot.view(invalid).kind(invalid), "TypeNode")
        for expression, supplied in (
            (invalid, value_type),
            (self.u0, invalid),
        ):
            relation = p.relation("HasType", expression, supplied)
            snapshot = p.commit()
            self.assertFalse(snapshot.check(relation))
            with self.assertRaisesRegex(TypeCheckError, "TypeNode expression"):
                snapshot.require(relation)

    def test_invalid_type_handle_is_rejected_as_a_function_domain(self) -> None:
        value, _ = self.value_application()
        invalid = self.program.type_node(value)
        function, function_type = self.identity(invalid)
        with self.assertRaises(TypeCheckError):
            self.has_type(function, function_type)

    def test_invalid_type_handle_is_rejected_as_an_argument(self) -> None:
        p = self.program
        value, value_type = self.value_application()
        invalid = p.type_node(value)
        function, _ = self.identity(value_type)
        application = p.apply(function, invalid)
        with self.assertRaisesRegex(TypeCheckError, "TypeNode expression"):
            self.has_type(application, value_type)

    def test_invalid_type_handle_in_discarded_argument_still_fails_typing(self) -> None:
        p = self.program
        value, value_type = self.value_application()
        invalid = p.type_node(value)
        x = p.variable()
        constant = p.lambda_(x, value_type, self.u0)
        application = p.apply(constant, invalid)
        with self.assertRaisesRegex(TypeCheckError, "TypeNode expression"):
            self.has_type(application, self.u1)

    def test_value_cannot_be_promoted_to_a_function_by_wrapping(self) -> None:
        p = self.program
        value, _ = self.value_application()
        invalid = p.apply(p.type_node(value), self.u0)
        with self.assertRaisesRegex(TypeCheckError, "TypeNode expression"):
            self.has_type(invalid, self.u1)

    def test_scope_is_still_checked_inside_a_type_node(self) -> None:
        variable = self.program.variable()
        type_handle = self.program.type_node(variable)
        with self.assertRaisesRegex(TypeCheckError, "not bound"):
            self.has_type(type_handle, self.u0)

    def test_type_node_can_describe_a_bound_type_variable(self) -> None:
        p = self.program
        a, x = p.variable(), p.variable()
        a_type = p.type_node(a)
        inner = p.lambda_(x, a_type, x)
        inner_type = p.function_type(x, a_type, a_type)
        function = p.lambda_(a, self.t1, inner)
        function_type = p.type_node(p.function_type(a, self.t1, inner_type))
        view = p.commit().view(a_type)
        self.assertEqual(view.form(a_type), "variable")
        self.assertEqual(set(view.fields(a_type)), {"form", "variable"})
        self.assertIs(view.fields(a_type)["variable"], a)
        self.has_type(function, function_type)
        application = p.apply(function, self.t0)
        result_type = p.type_node(p.function_type(x, self.t0, self.t0))
        self.has_type(application, result_type)
        self.beta(application, p.lambda_(x, self.t0, x))

    def test_type_node_bound_variable_must_really_be_a_type(self) -> None:
        p = self.program
        a, x, f = p.variable(), p.variable(), p.variable()
        function_domain = p.function_type(x, self.u1, self.u1)
        invalid = p.lambda_(f, function_domain, p.type_node(f))
        with self.assertRaisesRegex(TypeCheckError, "TypeNode expression"):
            self.has_type(invalid, p.function_type(a, function_domain, function_domain))

    def test_substitution_preserves_binding_inside_wrapped_dependent_types(self) -> None:
        p = self.program
        a, b, x, y = (p.variable() for _ in range(4))
        ta, tb = p.type_node(a), p.type_node(b)
        body = p.lambda_(b, self.t1, p.lambda_(x, ta, p.lambda_(y, tb, x)))
        function = p.lambda_(a, self.t1, body)
        application = p.apply(function, self.t0)
        expected = p.lambda_(
            b, self.t1, p.lambda_(x, self.t0, p.lambda_(y, tb, x))
        )
        supplied = p.type_node(p.function_type(
            b, self.t1,
            p.function_type(x, self.t0, p.function_type(y, tb, self.t0)),
        ))
        self.beta(application, expected)
        self.has_type(application, supplied)
        self.has_type(expected, supplied)

    def test_beta_does_not_normalize_away_additional_applications(self) -> None:
        p = self.program
        function, _ = self.identity(self.t1)
        computed_type = p.type_node(p.apply(function, self.t0))
        outer = p.apply(function, computed_type)
        self.beta(outer, computed_type)
        with self.assertRaises(TypeCheckError):
            self.beta(outer, self.t0)

    def test_local_view_can_follow_a_type_handle_but_not_its_users(self) -> None:
        p = self.program
        function, _ = self.identity(self.t1)
        application = p.apply(function, self.u0)
        handle = p.type_node(application)
        relation = p.relation("HasType", handle, self.u1)
        snapshot = p.commit()
        view = snapshot.view(handle)
        self.assertIn(self.u1, view.nodes)
        self.assertIn(function, view.nodes)
        self.assertIn(application, view.nodes)
        for hidden in (relation, snapshot.root, self.u2):
            with self.subTest(hidden=hidden.number):
                self.assertNotIn(hidden, view.nodes)
                with self.assertRaises(UnknownNodeError):
                    view.kind(hidden)

    def test_same_expression_remains_valid_with_raw_or_application_type_descriptions(self) -> None:
        function, function_type = self.identity(self.u1)
        self.has_type(function, function_type)
        self.has_type(function, self.program.type_node(function_type))
        self.has_type(self.u0, self.u1)
        self.has_type(self.u0, self.t1)
        variable = self.program.variable()
        type_identity = self.program.lambda_(variable, self.u2, variable)
        described_type = self.program.type_node(
            self.program.apply(type_identity, self.u1)
        )
        self.has_type(self.u0, described_type)

    def test_checking_does_not_allocate_a_type_object_or_mutate_a_handle(self) -> None:
        p = self.program
        function, function_type = self.identity(self.t1)
        handle = p.type_node(function_type)
        relation = p.relation("HasType", function, handle)
        snapshot = p.commit()
        before = {
            node: snapshot.graph.children(node) for node in snapshot.graph.nodes
        }
        snapshot.require(relation)
        self.assertEqual(before, {
            node: snapshot.graph.children(node) for node in snapshot.graph.nodes
        })
        self.assertEqual(p.commit().graph.nodes, snapshot.graph.nodes)

    def test_a_later_type_node_does_not_change_an_earlier_snapshot(self) -> None:
        p = self.program
        relation = p.relation("HasType", self.u0, self.t1)
        first = p.commit()
        variable = p.variable()
        later = p.type_node(variable)
        second = p.commit()
        first.require(relation)
        second.require(relation)
        self.assertNotIn(later, first.graph.nodes)
        self.assertIn(later, second.graph.nodes)

    def test_type_node_rejects_non_expressions_and_foreign_nodes_before_allocation(self) -> None:
        p = self.program
        relation = p.relation("HasType", self.u0, self.t1)
        before = p.commit().graph.nodes
        with self.assertRaises(EncodingError):
            p.type_node(relation)
        for foreign in (Program().universe(0), p.graph.root):
            with self.subTest(foreign=foreign.number):
                with self.assertRaises(UnknownNodeError):
                    p.type_node(foreign)
        self.assertEqual(before, p.commit().graph.nodes)

    def test_type_node_cycle_is_an_encoding_error_not_false(self) -> None:
        p = self.program
        function, _ = self.identity(self.u1)
        application = p.apply(function, self.u0)
        handle = p.type_node(application)
        relation = p.relation("HasType", handle, self.u1)
        snapshot = p.commit()
        slot = next(
            child for child in snapshot.graph.children(application)
            if self.u0 in snapshot.graph.children(child)
        )
        role = next(iter(snapshot.graph.children(slot) - {self.u0}))
        links = {
            node: snapshot.graph.children(node) for node in snapshot.graph.nodes
        }
        links[slot] = frozenset((role, handle))
        cyclic = Snapshot(GraphSnapshot(links, snapshot.root), snapshot._vocabulary)
        with self.assertRaisesRegex(EncodingError, "cycle"):
            cyclic.check(relation)

    def test_type_node_rejects_extra_fields(self) -> None:
        p = self.program
        function, _ = self.identity(self.u1)
        handle = p.type_node(p.apply(function, self.u0))
        relation = p.relation("HasType", handle, self.u1)
        p.graph.add_link(handle, self.u2)
        with self.assertRaises(EncodingError):
            p.commit().check(relation)

    def test_work_budget_exhaustion_is_not_false(self) -> None:
        p = self.program
        function, _ = self.identity(self.u1)
        handle = self.u0
        for _ in range(20):
            handle = p.type_node(p.apply(function, handle))
        relation = p.relation("HasType", handle, self.u1)
        with self.assertRaises(CheckLimitError):
            p.commit().check(relation, max_steps=10)

    def test_lambda_cannot_be_used_as_a_type_form(self) -> None:
        p = self.program
        function, _ = self.identity(self.u1)
        before = p.commit().graph.nodes
        with self.assertRaisesRegex(EncodingError, "Lambda"):
            p.type_node(function)
        self.assertEqual(before, p.commit().graph.nodes)

    def test_function_form_is_not_a_function_value(self) -> None:
        p = self.program
        _, function_type = self.identity(self.u1)
        application = p.apply(function_type, self.u0)
        with self.assertRaisesRegex(TypeCheckError, "function type"):
            self.has_type(application, self.u1)

    def test_only_type_nodes_have_a_form(self) -> None:
        p = self.program
        function, _ = self.identity(self.u1)
        snapshot = p.commit()
        for node in (self.u0, function):
            with self.subTest(node=node.number):
                with self.assertRaisesRegex(EncodingError, "Only a TypeNode"):
                    snapshot.view(node).form(node)
        with self.assertRaises(UnknownNodeError):
            snapshot.view(self.u0).form(function)

    def test_unknown_form_marker_is_an_encoding_error_not_false(self) -> None:
        p = self.program
        _, function_type = self.identity(self.u1)
        relation = p.relation("HasType", function_type, self.u2)
        invalid = self.changed_field(function_type, "form", self.u0)
        with self.assertRaisesRegex(EncodingError, "recognized form"):
            invalid.check(relation)

    def test_changing_form_cannot_reinterpret_incompatible_fields(self) -> None:
        p = self.program
        _, function_type = self.identity(self.u1)
        relation = p.relation("HasType", function_type, self.u2)
        invalid = self.changed_field(
            function_type, "form", p._vocabulary.type_forms["variable"]
        )
        with self.assertRaisesRegex(EncodingError, "requires fields"):
            invalid.check(relation)

    def test_function_form_requires_a_codomain(self) -> None:
        p = self.program
        _, function_type = self.identity(self.u1)
        relation = p.relation("HasType", function_type, self.u2)
        original = p.commit()
        role = original._vocabulary.roles["codomain"]
        slot = next(
            child for child in original.graph.children(function_type)
            if role in original.graph.children(child)
        )
        links = {
            node: original.graph.children(node) for node in original.graph.nodes
        }
        links[function_type] -= {slot}
        invalid = Snapshot(
            GraphSnapshot(links, original.root), original._vocabulary
        )
        with self.assertRaisesRegex(EncodingError, "requires fields"):
            invalid.check(relation)

    def test_variable_form_must_point_to_a_variable(self) -> None:
        p = self.program
        variable = p.variable()
        handle = p.type_node(variable)
        relation = p.relation("HasType", handle, self.u1)
        invalid = self.changed_field(handle, "variable", self.u0)
        with self.assertRaisesRegex(EncodingError, "must point to Variable"):
            invalid.check(relation)

    def test_application_form_must_point_to_an_application(self) -> None:
        p = self.program
        function, _ = self.identity(self.u1)
        handle = p.type_node(p.apply(function, self.u0))
        relation = p.relation("HasType", handle, self.u1)
        invalid = self.changed_field(handle, "expression", function)
        with self.assertRaisesRegex(EncodingError, "must point to Application"):
            invalid.check(relation)

    def test_form_markers_must_not_grant_extra_visibility(self) -> None:
        p = self.program
        _, function_type = self.identity(self.u1)
        relation = p.relation("HasType", function_type, self.u2)
        p.graph.add_link(p._vocabulary.type_forms["function"], self.u0)
        with self.assertRaisesRegex(EncodingError, "marker"):
            p.commit().check(relation)


if __name__ == "__main__":
    unittest.main()
