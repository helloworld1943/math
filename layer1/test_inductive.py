import unittest

from layer0 import GraphSnapshot, Node, UnknownNodeError

from . import (
    CheckLimitError,
    EncodingError,
    Program,
    Snapshot,
    TypeCheckError,
    UnsupportedInductiveError,
)
from ._calculus import Work


class InductiveTests(unittest.TestCase):
    def setUp(self) -> None:
        self.p = Program()
        self.u0, self.u1, self.u2 = (self.p.universe(n) for n in range(3))

    def valid(self, definition: Node) -> None:
        relation = self.p.relation("ValidInductive", definition)
        self.p.commit().require(relation, max_steps=100_000)

    def typed(self, expression: Node, type_node: Node) -> None:
        relation = self.p.relation("HasType", expression, type_node)
        self.p.commit().require(relation, max_steps=100_000)

    def nat(self):
        d = self.p.inductive("Nat", self.u0)
        t = self.p.type_node(d.identity)
        zero = d.constructor("zero", t)
        n = self.p.variable()
        succ_type = self.p.function_type(n, t, t)
        succ = d.constructor("succ", succ_type)
        return d.finish(), d.identity, t, zero, succ, succ_type

    def boolean(self):
        d = self.p.inductive("Bool", self.u0)
        t = self.p.type_node(d.identity)
        yes = d.constructor("true", t)
        no = d.constructor("false", t)
        return d.finish(), d.identity, t, yes, no

    def changed_field(self, node: Node, role: str, target: Node) -> Snapshot:
        original = self.p.commit()
        marker = original._vocabulary.roles[role]
        slot = next(
            entry for entry in original.graph.children(node)
            if marker in original.graph.children(entry)
        )
        links = {
            entry: original.graph.children(entry) for entry in original.graph.nodes
        }
        links[slot] = frozenset((marker, target))
        return Snapshot(GraphSnapshot(links, original.root), original._vocabulary)

    def test_bool_declaration_and_constructor_typing(self) -> None:
        definition, identity, t, yes, no = self.boolean()
        self.valid(definition)
        self.typed(identity, self.u0)
        self.typed(yes, t)
        self.typed(no, t)

    def test_valid_inductive_has_one_explicit_argument(self) -> None:
        definition, *_ = self.nat()
        relation = self.p.relation("ValidInductive", definition)
        snapshot = self.p.commit()
        self.assertEqual(snapshot.view(relation).arguments(relation), (definition,))
        for arguments in ((), (definition, self.u0)):
            with self.subTest(arguments=arguments):
                with self.assertRaises(EncodingError):
                    self.p.relation("ValidInductive", *arguments)
        with self.assertRaises(EncodingError):
            self.p.relation("ValidInductive", self.u0)

    def test_nat_declaration_and_repeated_constructor_applications(self) -> None:
        definition, identity, t, zero, succ, succ_type = self.nat()
        self.valid(definition)
        self.typed(identity, self.u0)
        self.typed(succ, succ_type)
        value = zero
        for _ in range(8):
            self.typed(value, t)
            value = self.p.apply(succ, value)

    def test_context_owns_constructors_with_names_and_typing_relations(self) -> None:
        definition, _, t, zero, succ, _ = self.nat()
        snapshot = self.p.commit()
        view = snapshot.view(definition)
        body = view.fields(definition)["body"]
        context = view.fields(body)["context"]
        self.assertEqual(view.kind(body), "InductiveBody")
        self.assertEqual(view.kind(context), "Context")
        self.assertEqual(view.kind(zero), "Variable")
        self.assertEqual(view.kind(succ), "Variable")
        self.assertEqual(view.name(zero), "zero")
        self.assertEqual(view.name(succ), "succ")
        self.assertIs(view.fields(zero)["context"], context)
        typing = view.fields(zero)["typing"]
        self.assertEqual(view.arguments(typing), (zero, t))
        snapshot.require(typing, max_steps=100_000)
        self.assertNotIn("Constructor", snapshot._vocabulary.kinds)

    def test_positive_reference_cycle_is_visible_and_finite(self) -> None:
        definition, identity, t, zero, _, _ = self.nat()
        view = self.p.commit().view(identity)
        self.assertIn(definition, view.nodes)
        self.assertIn(zero, view.nodes)
        self.assertIn(t, view.nodes)
        self.assertNotIn(self.p.graph.root, view.nodes)
        self.typed(zero, t)

    def test_inductive_constants_remain_nominal_even_with_equal_names(self) -> None:
        _, first, first_type, first_value, _ = self.boolean()
        _, second, second_type, second_value, _ = self.boolean()
        self.assertIsNot(first, second)
        self.typed(first_value, first_type)
        self.typed(second_value, second_type)
        with self.assertRaises(TypeCheckError):
            self.typed(first_value, second_type)

    def test_constructor_arity_and_argument_type_are_checked(self) -> None:
        _, _, nat_type, zero, succ, _ = self.nat()
        _, _, _, yes, _ = self.boolean()
        with self.assertRaisesRegex(TypeCheckError, "argument type"):
            self.typed(self.p.apply(succ, yes), nat_type)
        with self.assertRaisesRegex(TypeCheckError, "function type"):
            self.typed(self.p.apply(zero, zero), nat_type)

    def test_constructor_is_not_a_lambda_and_does_not_beta_reduce(self) -> None:
        _, _, _, zero, succ, _ = self.nat()
        source = self.p.apply(succ, zero)
        relation = self.p.relation("BetaReduces", source, zero)
        with self.assertRaisesRegex(TypeCheckError, "Application of a Lambda"):
            self.p.commit().require(relation, max_steps=100_000)

    def test_lambda_can_consume_a_constructor_value(self) -> None:
        _, _, t, zero, _, _ = self.nat()
        x = self.p.variable()
        identity = self.p.lambda_(x, t, x)
        application = self.p.apply(identity, zero)
        self.typed(application, t)
        relation = self.p.relation("BetaReduces", application, zero)
        self.p.commit().require(relation, max_steps=100_000)

    def test_inductive_type_itself_can_be_passed_as_a_type_argument(self) -> None:
        _, identity, t, _, _, _ = self.nat()
        a, x = self.p.variable(), self.p.variable()
        ta = self.p.type_node(a)
        polymorphic = self.p.lambda_(a, self.u0, self.p.lambda_(x, ta, x))
        application = self.p.apply(polymorphic, identity)
        supplied = self.p.function_type(x, t, t)
        self.typed(application, supplied)

    def test_constructor_signature_can_be_a_computed_function_type(self) -> None:
        d = self.p.inductive("Computed", self.u0)
        t = self.p.type_node(d.identity)
        type_parameter, field = self.p.variable(), self.p.variable()
        signature_function = self.p.lambda_(
            type_parameter, self.u0,
            self.p.function_type(field, self.p.type_node(type_parameter), t),
        )
        signature = self.p.type_node(self.p.apply(signature_function, t))
        constructor = d.constructor("mk", signature)
        self.valid(d.finish())
        self.typed(constructor, signature)

    def test_inductive_identity_cannot_be_rebound_as_a_lambda_parameter(self) -> None:
        _, identity, t, _, _, _ = self.nat()
        bad = self.p.lambda_(identity, self.u0, identity)
        with self.assertRaisesRegex(EncodingError, "cannot be a function binder"):
            self.typed(bad, self.p.function_type(self.p.variable(), self.u0, t))

    def test_box_parameter_type_and_constructor_application(self) -> None:
        _, _, bt, yes, _ = self.boolean()
        a = self.p.variable()
        d = self.p.inductive("Box", self.u0, parameters=((a, self.u0),))
        result = self.p.type_node(self.p.apply(d.identity, a))
        value = self.p.variable()
        mk = d.constructor("mk", self.p.function_type(value, self.p.type_node(a), result))
        definition = d.finish()
        self.valid(definition)
        box_bool = self.p.type_node(self.p.apply(d.identity, bt))
        self.typed(box_bool, self.u0)
        self.typed(self.p.apply(self.p.apply(mk, bt), yes), box_bool)
        view = self.p.commit().view(definition)
        parameters = view.fields(definition)["parameters"]
        self.assertEqual(view.kind(parameters), "Parameters")
        self.assertEqual(view.kind(view.fields(a)["context"]), "Context")
        self.assertIsNot(view.fields(a)["context"], view.fields(mk)["context"])

    def test_generic_recursive_list_uses_unchanged_parameters(self) -> None:
        _, _, bt, yes, _ = self.boolean()
        a = self.p.variable()
        d = self.p.inductive("List", self.u0, parameters=((a, self.u0),))
        list_a = self.p.type_node(self.p.apply(d.identity, a))
        nil = d.constructor("nil", list_a)
        head, tail = self.p.variable(), self.p.variable()
        signature = self.p.function_type(
            head, self.p.type_node(a), self.p.function_type(tail, list_a, list_a)
        )
        cons = d.constructor("cons", signature)
        definition = d.finish()
        self.valid(definition)
        list_bool = self.p.type_node(self.p.apply(d.identity, bt))
        empty = self.p.apply(nil, bt)
        value = self.p.apply(self.p.apply(self.p.apply(cons, bt), yes), empty)
        self.typed(empty, list_bool)
        self.typed(value, list_bool)

    def test_dependent_parameter_types_are_checked_in_order(self) -> None:
        _, _, bt, yes, _ = self.boolean()
        a, x = self.p.variable(), self.p.variable()
        ta = self.p.type_node(a)
        d = self.p.inductive("Stored", self.u0, parameters=((a, self.u0), (x, ta)))
        result = self.p.apply(self.p.apply(d.identity, a), x)
        mk = d.constructor("mk", self.p.type_node(result))
        definition = d.finish()
        self.valid(definition)
        stored = self.p.type_node(self.p.apply(self.p.apply(d.identity, bt), yes))
        self.typed(self.p.apply(self.p.apply(mk, bt), yes), stored)

    def test_function_valued_inductive_parameter(self) -> None:
        a, h, x = self.p.variable(), self.p.variable(), self.p.variable()
        ta = self.p.type_node(a)
        function_type = self.p.function_type(x, ta, ta)
        d = self.p.inductive("FunctionHolder", self.u0, parameters=(
            (a, self.u0), (h, function_type),
        ))
        result = self.p.type_node(self.p.apply(self.p.apply(d.identity, a), h))
        d.constructor("mk", result)
        self.valid(d.finish())

    def test_higher_universe_allows_large_fields_without_prop_special_cases(self) -> None:
        _, bool_identity, _, _, _ = self.boolean()
        d = self.p.inductive("Large", self.u1)
        x = self.p.variable()
        t = self.p.type_node(d.identity)
        constructor = d.constructor("mk", self.p.function_type(x, self.u0, t))
        self.valid(d.finish())
        self.typed(self.p.apply(constructor, bool_identity), t)

    def test_empty_inductive_is_a_type_not_an_inhabitant(self) -> None:
        d = self.p.inductive("Empty", self.u0)
        self.valid(d.finish())
        self.typed(d.identity, self.u0)
        with self.assertRaises(TypeCheckError):
            self.typed(d.identity, self.p.type_node(d.identity))

    def test_constructor_result_must_be_the_introduced_type(self) -> None:
        d = self.p.inductive("Bad", self.u0)
        d.constructor("mk", self.u0)
        with self.assertRaisesRegex(TypeCheckError, "must return this inductive"):
            self.valid(d.finish())

    def test_wrong_constructor_in_one_context_invalidates_other_constructors(self) -> None:
        d = self.p.inductive("Bad", self.u0)
        t = self.p.type_node(d.identity)
        otherwise_valid = d.constructor("good", t)
        d.constructor("bad", self.u0)
        d.finish()
        with self.assertRaisesRegex(TypeCheckError, "must return this inductive"):
            self.typed(otherwise_valid, t)

    def test_too_large_constructor_field_is_rejected(self) -> None:
        d = self.p.inductive("Small", self.u0)
        x = self.p.variable()
        d.constructor("mk", self.p.function_type(x, self.u0, self.p.type_node(d.identity)))
        with self.assertRaisesRegex(TypeCheckError, "exceeds the result universe"):
            self.valid(d.finish())

    def test_constructor_field_universe_thresholds(self) -> None:
        for result_level in range(4):
            for field_level in range(4):
                with self.subTest(result=result_level, field=field_level):
                    d = self.p.inductive("Sized", self.p.universe(result_level))
                    x = self.p.variable()
                    t = self.p.type_node(d.identity)
                    d.constructor("mk", self.p.function_type(
                        x, self.p.universe(field_level), t
                    ))
                    definition = d.finish()
                    if field_level + 1 <= result_level:
                        self.valid(definition)
                    else:
                        with self.assertRaisesRegex(TypeCheckError, "exceeds"):
                            self.valid(definition)

    def test_recursive_field_in_a_function_domain_is_rejected(self) -> None:
        d = self.p.inductive("Bad", self.u0)
        t = self.p.type_node(d.identity)
        x, f = self.p.variable(), self.p.variable()
        negative = self.p.function_type(x, t, self.u0)
        d.constructor("mk", self.p.function_type(f, negative, t))
        with self.assertRaisesRegex(TypeCheckError, "strictly positive"):
            self.valid(d.finish())

    def test_positive_function_recursive_fields_are_explicitly_unsupported(self) -> None:
        d = self.p.inductive("Tree", self.u0)
        t = self.p.type_node(d.identity)
        x, f = self.p.variable(), self.p.variable()
        _, _, bt, _, _ = self.boolean()
        positive = self.p.function_type(x, bt, t)
        d.constructor("mk", self.p.function_type(f, positive, t))
        with self.assertRaises(UnsupportedInductiveError):
            self.valid(d.finish())

    def test_constructor_parameters_cannot_change_in_the_result(self) -> None:
        a, b = self.p.variable(), self.p.variable()
        d = self.p.inductive("Wrong", self.u0, parameters=((a, self.u0), (b, self.u0)))
        other = self.p.type_node(self.p.apply(self.p.apply(d.identity, b), a))
        d.constructor("mk", other)
        with self.assertRaisesRegex(TypeCheckError, "unchanged parameters"):
            self.valid(d.finish())

    def test_later_parameter_cannot_be_used_in_earlier_parameter_type(self) -> None:
        a, x = self.p.variable(), self.p.variable()
        d = self.p.inductive("Bad", self.u0, parameters=(
            (x, self.p.type_node(a)), (a, self.u0),
        ))
        with self.assertRaisesRegex(TypeCheckError, "not bound"):
            self.valid(d.finish())

    def test_constructor_signature_cannot_justify_itself(self) -> None:
        d = self.p.inductive("Bad", self.u0)
        t = self.p.type_node(d.identity)
        x = self.p.variable()
        ctor = d.constructor("mk", t)
        # Another signature using the constructor as a type cannot be trusted.
        d.constructor("bad", self.p.function_type(x, self.p.type_node(ctor), t))
        with self.assertRaisesRegex(TypeCheckError, "Circular declaration"):
            self.valid(d.finish())

    def test_unfinished_inductive_is_a_structural_error_not_false(self) -> None:
        d = self.p.inductive("Incomplete", self.u0)
        relation = self.p.relation("ValidInductive", d.node)
        with self.assertRaises(EncodingError):
            self.p.commit().check(relation)

    def test_finish_and_constructor_operations_are_explicitly_staged(self) -> None:
        d = self.p.inductive("Done", self.u0)
        d.finish()
        with self.assertRaises(ValueError):
            d.finish()
        with self.assertRaises(ValueError):
            d.constructor("mk", self.u0)

    def test_invalid_names_and_duplicate_constructors_are_rejected_without_allocation(self) -> None:
        d = self.p.inductive("Name", self.u0)
        d.constructor("mk", self.p.type_node(d.identity))
        before = self.p.commit().graph.nodes
        with self.assertRaises(ValueError):
            d.constructor("mk", self.u0)
        with self.assertRaises(ValueError):
            d.constructor("not a name", self.u0)
        with self.assertRaises(ValueError):
            self.p.inductive("", self.u0)
        self.assertEqual(before, self.p.commit().graph.nodes)

    def test_foreign_signature_nodes_and_invalid_result_kind_are_rejected(self) -> None:
        d = self.p.inductive("Named", self.u0)
        with self.assertRaises(UnknownNodeError):
            d.constructor("mk", Program().universe(0))
        with self.assertRaises(EncodingError):
            self.p.inductive("WrongKind", self.p.type_node(d.identity))

    def test_parameters_need_fresh_unique_variable_identities(self) -> None:
        a = self.p.variable()
        with self.assertRaises(EncodingError):
            self.p.inductive("Dup", self.u0, parameters=((a, self.u0), (a, self.u0)))
        first = self.p.inductive("First", self.u0, parameters=((a, self.u0),))
        second = self.p.inductive("Second", self.u0, parameters=((a, self.u0),))
        first.finish()
        before = self.p.commit().graph.nodes
        with self.assertRaises(EncodingError):
            second.finish()
        self.assertEqual(before, self.p.commit().graph.nodes)

    def test_constructor_type_relation_must_refer_to_its_own_identity(self) -> None:
        definition, _, _, zero, succ, _ = self.nat()
        relation = self.p.relation("ValidInductive", definition)
        typing = self.p.commit().view(zero).fields(zero)["typing"]
        invalid = self.changed_field(typing, "first", succ)
        with self.assertRaisesRegex(EncodingError, "that identity"):
            invalid.check(relation)

    def test_context_ownership_must_match_constructor_membership(self) -> None:
        definition, identity, _, zero, _, _ = self.nat()
        relation = self.p.relation("ValidInductive", definition)
        type_context = self.p.commit().view(identity).fields(identity)["context"]
        invalid = self.changed_field(zero, "context", type_context)
        with self.assertRaisesRegex(EncodingError, "owned by its Context"):
            invalid.check(relation)

    def test_inductive_body_must_use_its_own_context(self) -> None:
        first, *_ = self.nat()
        second, *_ = self.boolean()
        relation = self.p.relation("ValidInductive", first)
        snapshot = self.p.commit()
        body = snapshot.view(first).fields(first)["body"]
        other_body = snapshot.view(second).fields(second)["body"]
        other_context = snapshot.view(second).fields(other_body)["context"]
        invalid = self.changed_field(body, "context", other_context)
        with self.assertRaisesRegex(EncodingError, "body Context"):
            invalid.check(relation)

    def test_constructor_names_are_checked_from_the_graph(self) -> None:
        definition, _, _, zero, succ, _ = self.nat()
        relation = self.p.relation("ValidInductive", definition)
        zero_name = self.p.commit().view(zero).fields(zero)["name"]
        invalid = self.changed_field(succ, "name", zero_name)
        with self.assertRaisesRegex(EncodingError, "names must be unique"):
            invalid.check(relation)

    def test_foreign_constructor_is_not_accepted_by_changing_its_context(self) -> None:
        first, _, _, _, _, _ = self.nat()
        second, _, _, yes, _ = self.boolean()
        relation = self.p.relation("ValidInductive", first)
        view = self.p.commit().view(first, second)
        body = view.fields(first)["body"]
        context = view.fields(body)["context"]
        declarations = view.fields(context)["declarations"]
        invalid = self.changed_field(declarations, "value", yes)
        with self.assertRaisesRegex(EncodingError, "owned by its Context"):
            invalid.check(relation)

    def test_validation_errors_leave_no_provisional_constants(self) -> None:
        d = self.p.inductive("Bad", self.u0)
        d.constructor("mk", self.u0)
        d.finish()
        reader = self.p.commit().view(d.node)._reader
        with self.assertRaises(TypeCheckError):
            reader.validate_inductive(d.node, Work(100_000))
        self.assertEqual(reader._constants, {})
        self.assertEqual(reader._validating_inductives, set())
        self.assertEqual(reader._validated_inductives, set())

    def test_validation_does_not_mutate_or_allocate_graph_nodes(self) -> None:
        definition, *_ = self.nat()
        relation = self.p.relation("ValidInductive", definition)
        snapshot = self.p.commit()
        before = {node: snapshot.graph.children(node) for node in snapshot.graph.nodes}
        snapshot.require(relation, max_steps=100_000)
        self.assertEqual(before, {
            node: snapshot.graph.children(node) for node in snapshot.graph.nodes
        })
        self.assertEqual(snapshot.graph.nodes, self.p.commit().graph.nodes)

    def test_snapshot_and_visibility_boundaries_remain_intact(self) -> None:
        definition, identity, t, zero, _, _ = self.nat()
        old = self.p.commit()
        relation = self.p.relation("HasType", zero, t)
        new = self.p.commit()
        self.assertNotIn(relation, old.graph.nodes)
        old_reader = old.view(zero)
        self.assertIn(definition, old_reader.nodes)
        self.assertIn(identity, old_reader.nodes)
        for hidden in (old.root, relation):
            with self.assertRaises(UnknownNodeError):
                old_reader.kind(hidden)
        new.require(relation, max_steps=100_000)

    def test_valid_inductive_can_be_combined_with_other_relations(self) -> None:
        definition, _, t, zero, _, _ = self.nat()
        valid = self.p.relation("ValidInductive", definition)
        typed = self.p.relation("HasType", zero, t)
        combined = self.p.all_of(definition, zero, t, relations=(valid, typed))
        self.p.commit().require(combined, max_steps=100_000)

    def test_invalid_declaration_is_not_a_false_budget_result(self) -> None:
        definition, *_ = self.nat()
        relation = self.p.relation("ValidInductive", definition)
        with self.assertRaises(CheckLimitError):
            self.p.commit().check(relation, max_steps=1)

    def test_legacy_universe_indexing_is_not_silently_migrated(self) -> None:
        self.typed(self.u0, self.u1)
        self.assertEqual(self.p.commit().view(self.u0).kind(self.u0), "Universe")


if __name__ == "__main__":
    unittest.main()
