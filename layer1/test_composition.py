import itertools
import unittest
from unittest.mock import patch

from layer0 import GraphSnapshot, Node, UnknownNodeError

from . import CheckLimitError, EncodingError, Program, Snapshot, TypeCheckError
from . import _calculus as calculus


class CompositionTests(unittest.TestCase):
    def setUp(self) -> None:
        self.program = Program()
        p = self.program
        self.u0, self.u1, self.u2 = (p.universe(i) for i in range(3))
        self.inputs = (self.u0, self.u1, self.u2)
        self.yes = p.relation("HasType", self.u0, self.u1)
        self.no = p.relation("HasType", self.u0, self.u2)

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
        return Snapshot(GraphSnapshot(links, original.root), original._vocabulary)

    def group(self, parent: Node) -> Node:
        snapshot = self.program.commit()
        return snapshot.view(parent).fields(parent)["decomposition"]

    def test_graph_alternates_relations_and_combination_nodes(self) -> None:
        p = self.program
        choice = p.any_of(*self.inputs, relations=(self.no, self.yes))
        parent = p.all_of(*self.inputs, relations=(self.yes, choice))
        snapshot = p.commit()
        local = snapshot.view(parent)
        self.assertEqual(local.kind(parent), "Relation")
        self.assertEqual(local.kind(self.group(parent)), "RelationAnd")
        self.assertEqual(local.kind(self.group(choice)), "RelationOr")
        self.assertEqual(local.operands(self.group(parent)), (self.yes, choice))
        self.assertEqual(local.operands(self.group(choice)), (self.no, self.yes))
        self.assertEqual(local.arguments(parent), self.inputs)
        self.assertEqual(set(local.fields(parent)), {"inputs", "decomposition"})
        self.assertEqual(set(local.fields(choice)), {"inputs", "decomposition"})
        self.assertEqual(
            set(snapshot._vocabulary.relations), {"HasType", "BetaReduces", "ValidInductive"}
        )
        self.assertNotIn("All", snapshot._vocabulary.kinds)
        self.assertNotIn("Any", snapshot._vocabulary.kinds)
        snapshot.require(parent)

    def test_all_and_any_truth_tables(self) -> None:
        p = self.program
        for size in range(1, 5):
            for values in itertools.product((False, True), repeat=size):
                children = tuple(self.yes if value else self.no for value in values)
                with self.subTest(values=values):
                    conjunction = p.all_of(*self.inputs, relations=children)
                    disjunction = p.any_of(*self.inputs, relations=children)
                    snapshot = p.commit()
                    self.assertEqual(snapshot.check(conjunction), all(values))
                    self.assertEqual(snapshot.check(disjunction), any(values))

    def test_nested_truth_tables(self) -> None:
        p = self.program
        for a, b, c in itertools.product((False, True), repeat=3):
            children = tuple(self.yes if value else self.no for value in (a, b, c))
            choice = p.any_of(*self.inputs, relations=children[1:])
            parent = p.all_of(*self.inputs, relations=(children[0], choice))
            with self.subTest(values=(a, b, c)):
                self.assertEqual(p.commit().check(parent), a and (b or c))

    def test_multiple_kinds_of_primitive_can_be_combined(self) -> None:
        p = self.program
        x = p.variable()
        identity = p.lambda_(x, self.u1, x)
        application = p.apply(identity, self.u0)
        typed = p.relation("HasType", application, self.u1)
        computed = p.relation("BetaReduces", application, self.u0)
        parent = p.all_of(
            application, self.u0, self.u1, relations=(typed, computed)
        )
        p.commit().require(parent)

    def test_empty_groups_are_rejected_before_allocation(self) -> None:
        p = self.program
        before = p.commit().graph.nodes
        for constructor in (p.all_of, p.any_of):
            with self.subTest(constructor=constructor.__name__):
                with self.assertRaisesRegex(EncodingError, "nonempty"):
                    constructor(*self.inputs, relations=())
        self.assertEqual(before, p.commit().graph.nodes)

    def test_all_child_inputs_must_appear_in_parent_interface(self) -> None:
        p = self.program
        before = p.commit().graph.nodes
        for constructor in (p.all_of, p.any_of):
            with self.subTest(constructor=constructor.__name__):
                with self.assertRaisesRegex(EncodingError, "inputs missing"):
                    constructor(self.u0, self.u1, relations=(self.no,))
        self.assertEqual(before, p.commit().graph.nodes)

    def test_repeated_inputs_and_operand_positions_are_preserved(self) -> None:
        p = self.program
        parent = p.all_of(
            self.u0, self.u1, self.u0, relations=(self.yes, self.yes)
        )
        snapshot = p.commit()
        view = snapshot.view(parent)
        self.assertEqual(view.arguments(parent), (self.u0, self.u1, self.u0))
        self.assertEqual(view.operands(self.group(parent)), (self.yes, self.yes))
        snapshot.require(parent)

    def test_expressions_and_combination_nodes_cannot_be_operands(self) -> None:
        p = self.program
        valid = p.all_of(*self.inputs, relations=(self.yes,))
        group = self.group(valid)
        before = p.commit().graph.nodes
        for bad in (self.u0, group, p.graph.root, Program().universe(0)):
            with self.subTest(bad=bad.number):
                with self.assertRaisesRegex(EncodingError, "operands"):
                    p.any_of(*self.inputs, relations=(bad,))
        self.assertEqual(before, p.commit().graph.nodes)

    def test_combination_cannot_be_checked_without_its_parent(self) -> None:
        parent = self.program.all_of(*self.inputs, relations=(self.yes,))
        group = self.group(parent)
        with self.assertRaisesRegex(EncodingError, "Only a Relation"):
            self.program.commit().check(group)

    def test_removed_kind_names_are_not_primitive_relations(self) -> None:
        for kind in ("All", "Any", "MyOwnRelation"):
            with self.subTest(kind=kind):
                with self.assertRaises(EncodingError):
                    self.program.relation(kind, *self.inputs)

    def test_has_type_cannot_be_bypassed_by_a_true_child(self) -> None:
        p = self.program
        parent = p.all_of(*self.inputs, relations=(self.yes,))
        group = self.group(parent)
        marker = p.commit()._vocabulary.roles["decomposition"]
        slot = p.graph.create_node()
        p.graph.add_link(self.no, slot)
        p.graph.add_link(slot, marker)
        p.graph.add_link(slot, group)
        with self.assertRaisesRegex(EncodingError, "requires fields"):
            p.commit().check(self.no)

    def test_errors_in_diagnostics_identify_parent_and_primitive(self) -> None:
        for constructor, prefix in (
            (self.program.all_of, "RelationAnd"), (self.program.any_of, "RelationOr"),
        ):
            parent = constructor(*self.inputs, relations=(self.no,))
            with self.subTest(prefix=prefix):
                with self.assertRaisesRegex(TypeCheckError, f"{prefix}.*HasType|no alternative"):
                    self.program.commit().require(parent)

    def test_or_can_try_another_well_formed_false_relation(self) -> None:
        p = self.program
        variable = p.variable()
        unbound = p.relation("HasType", variable, self.u0)
        parent = p.any_of(
            *self.inputs, variable, relations=(unbound, self.yes)
        )
        p.commit().require(parent)

    def test_left_to_right_short_circuit(self) -> None:
        p = self.program
        for constructor, first in ((p.any_of, self.yes), (p.all_of, self.no)):
            parent = constructor(*self.inputs, relations=(first, self.no, self.yes))
            snapshot = p.commit()
            with self.subTest(constructor=constructor.__name__):
                with patch.object(calculus, "has_type", wraps=calculus.has_type) as check:
                    snapshot.check(parent)
                    self.assertEqual(check.call_count, 1)

    def test_shared_relation_is_evaluated_once_per_request(self) -> None:
        p = self.program
        parent = p.all_of(*self.inputs, relations=(self.yes, self.yes))
        snapshot = p.commit()
        with patch.object(calculus, "has_type", wraps=calculus.has_type) as check:
            snapshot.require(parent)
            self.assertEqual(check.call_count, 1)
            snapshot.require(parent)
            self.assertEqual(check.call_count, 2)

    def test_primitive_errors_are_not_false_alternatives(self) -> None:
        p = self.program
        parent = p.any_of(*self.inputs, relations=(self.no, self.yes))
        snapshot = p.commit()
        for error in (RuntimeError("bug"), CheckLimitError("budget"), EncodingError("bad")):
            with self.subTest(error=type(error).__name__):
                with patch.object(calculus, "has_type", side_effect=error):
                    with self.assertRaises(type(error)):
                        snapshot.check(parent)

    def test_malformed_relation_topology_is_checked_even_in_skipped_branches(self) -> None:
        p = self.program
        parent = p.any_of(*self.inputs, relations=(self.yes, self.no))
        p.graph.add_link(self.no, self.u0)
        with self.assertRaises(EncodingError):
            p.commit().check(parent)

    def test_a_child_cannot_secretly_gain_an_unlisted_input(self) -> None:
        p = self.program
        parent = p.any_of(self.u0, self.u1, relations=(self.yes,))
        invalid = self.changed_field(self.yes, "second", self.u2)
        with self.assertRaisesRegex(EncodingError, "inputs missing"):
            invalid.check(parent)

    def test_combination_node_alone_decides_the_operation(self) -> None:
        p = self.program
        all_parent = p.all_of(*self.inputs, relations=(self.no, self.yes))
        any_parent = p.any_of(*self.inputs, relations=(self.no, self.yes))
        original = p.commit()
        self.assertFalse(original.check(all_parent))
        self.assertTrue(original.check(any_parent))
        changed = self.changed_field(all_parent, "decomposition", self.group(any_parent))
        self.assertTrue(changed.check(all_parent))
        self.assertEqual(set(changed.view(all_parent).fields(all_parent)), {
            "inputs", "decomposition"
        })

    def test_relation_cannot_decompose_directly_to_an_expression_or_relation(self) -> None:
        p = self.program
        parent = p.all_of(*self.inputs, relations=(self.yes,))
        for target in (self.u0, self.yes):
            invalid = self.changed_field(parent, "decomposition", target)
            with self.subTest(target=target.number):
                with self.assertRaisesRegex(EncodingError, "requires RelationAnd or RelationOr"):
                    invalid.check(parent)

    def test_primitive_kind_cannot_be_added_to_a_composite_parent(self) -> None:
        p = self.program
        parent = p.all_of(*self.inputs, relations=(self.yes,))
        original = p.commit()
        role = original._vocabulary.roles["kind"]
        marker = original._vocabulary.relations["HasType"]
        slot = p.graph.create_node()
        p.graph.add_link(parent, slot)
        p.graph.add_link(slot, role)
        p.graph.add_link(slot, marker)
        with self.assertRaisesRegex(EncodingError, "requires fields"):
            p.commit().check(parent)

    def test_combination_has_only_relation_operands(self) -> None:
        p = self.program
        parent = p.all_of(*self.inputs, relations=(self.yes,))
        group = self.group(parent)
        snapshot = p.commit()
        first = snapshot.view(group).fields(group)["operands"]
        for invalid_child in (group, self.u0):
            with self.subTest(invalid_child=invalid_child.number):
                invalid = self.changed_field(first, "value", invalid_child)
                with self.assertRaisesRegex(EncodingError, "Only a Relation"):
                    invalid.check(parent)

    def test_decoded_empty_combination_is_rejected(self) -> None:
        p = self.program
        parent = p.all_of(*self.inputs, relations=(self.yes,))
        group = self.group(parent)
        snapshot = p.commit()
        first = snapshot.view(group).fields(group)["operands"]
        end = snapshot.view(first).fields(first)["next"]
        invalid = self.changed_field(group, "operands", end)
        with self.assertRaisesRegex(EncodingError, "nonempty"):
            invalid.check(parent)

    def test_cycles_in_decomposition_and_in_lists_are_rejected(self) -> None:
        p = self.program
        parent = p.any_of(*self.inputs, relations=(self.yes, self.no))
        group = self.group(parent)
        first = p.commit().view(group).fields(group)["operands"]
        invalid_proof = self.changed_field(first, "value", parent)
        with self.assertRaisesRegex(EncodingError, "decomposition contains a cycle"):
            invalid_proof.check(parent)
        invalid_list = self.changed_field(first, "next", first)
        with self.assertRaisesRegex(EncodingError, "list contains a cycle"):
            invalid_list.check(parent)

    def test_combination_cannot_have_two_owners_in_one_checked_graph(self) -> None:
        p = self.program
        first = p.all_of(*self.inputs, relations=(self.yes,))
        second = p.all_of(*self.inputs, relations=(self.yes,))
        outer = p.any_of(*self.inputs, relations=(first, second))
        invalid = self.changed_field(second, "decomposition", self.group(first))
        with self.assertRaisesRegex(EncodingError, "one Relation owner"):
            invalid.check(outer)

    def test_many_inputs_and_many_operands(self) -> None:
        p = self.program
        parent = p.all_of(*(self.inputs * 50), relations=(self.yes,) * 100)
        snapshot = p.commit()
        self.assertEqual(len(snapshot.view(parent).arguments(parent)), 150)
        snapshot.require(parent)

    def test_nested_decomposition_uses_iterative_traversal(self) -> None:
        p = self.program
        parent = self.yes
        for _ in range(1050):
            parent = p.all_of(self.u0, self.u1, relations=(parent,))
        p.commit().require(parent, max_steps=100_000)

    def test_local_view_and_snapshot_isolation(self) -> None:
        p = self.program
        parent = p.all_of(*self.inputs, relations=(self.yes,))
        snapshot = p.commit()
        group = snapshot.view(parent).fields(parent)["decomposition"]
        local = snapshot.view(self.u0, self.u1)
        for hidden in (parent, group, snapshot.root, self.u2):
            with self.subTest(hidden=hidden.number):
                self.assertNotIn(hidden, local.nodes)
                with self.assertRaises(UnknownNodeError):
                    local.check(hidden)
        new = p.any_of(*self.inputs, relations=(self.no, self.yes))
        self.assertNotIn(new, snapshot.graph.nodes)
        snapshot.require(parent)
        p.commit().require(new)

    def test_composition_never_mutates_or_creates_graph_nodes_during_checking(self) -> None:
        p = self.program
        parent = p.any_of(*self.inputs, relations=(self.no, self.yes))
        snapshot = p.commit()
        links = {node: snapshot.graph.children(node) for node in snapshot.graph.nodes}
        snapshot.require(parent)
        self.assertEqual(links, {
            node: snapshot.graph.children(node) for node in snapshot.graph.nodes
        })
        self.assertEqual(snapshot.graph.nodes, p.commit().graph.nodes)

    def test_work_budget_is_shared_by_the_whole_check(self) -> None:
        parent = self.program.all_of(*self.inputs, relations=(self.yes,))
        with self.assertRaises(CheckLimitError):
            self.program.commit().check(parent, max_steps=1)


if __name__ == "__main__":
    unittest.main()
