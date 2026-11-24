import unittest
from dataclasses import FrozenInstanceError, asdict
from itertools import product

import node as node_package
from node import (
    DuplicateLinkError,
    Graph,
    GraphSnapshot,
    InputLink,
    InvalidLinkOrderError,
    InvalidNodePositionError,
    InvalidOutputCountError,
    Node,
    RootDeletionError,
    RootOutputLinkError,
    UnboundOutputError,
    UnknownLinkError,
    UnknownNodeError,
)


class Layer0Tests(unittest.TestCase):
    def _example(self) -> tuple[Graph, Node, Node, Node]:
        graph = Graph()
        a = graph.create_node()
        b = graph.create_node(2)
        c = graph.create_node()
        graph.edit_link(a, 0, graph.root)
        graph.edit_link(b, 0, graph.root)
        graph.edit_link(b, 1, a)
        graph.edit_link(c, 0, b)
        return graph, a, b, c

    def _outputs(
        self, reader: Graph | GraphSnapshot, source: Node
    ) -> tuple[Node | None, ...]:
        return tuple(
            reader.get_output(source, n)
            for n in range(reader.get_output_count(source))
        )

    def test_graph_starts_with_root_zero_and_no_outputs(self) -> None:
        graph = Graph()
        snapshot = graph.commit()
        self.assertEqual(graph.root.number, 0)
        for reader in (graph, snapshot):
            self.assertEqual(reader.node_order, (graph.root,))
            self.assertEqual(reader.nodes, frozenset((graph.root,)))
            self.assertEqual(reader.position(graph.root), 0)
            self.assertEqual(reader.get_output_count(graph.root), 0)
            self.assertEqual(reader.inputs(graph.root), [])
            with self.assertRaises(UnknownLinkError):
                reader.get_output(graph.root, 0)

    def test_non_root_nodes_start_with_fixed_empty_slots(self) -> None:
        graph = Graph()
        a = graph.create_node()
        b = graph.create_node(3)
        self.assertEqual(graph.get_output_count(a), 1)
        self.assertEqual(graph.get_output_count(b), 3)
        self.assertEqual(self._outputs(graph, b), (None, None, None))
        self.assertIsNone(graph.get_output(a, 0))

    def test_empty_targets_are_valid_in_committed_snapshots(self) -> None:
        graph = Graph()
        a = graph.create_node(3)
        graph.edit_link(a, 0, graph.root)
        snapshot = graph.commit()
        self.assertIs(graph.snapshot, snapshot)
        self.assertEqual(snapshot.get_output_count(a), 3)
        self.assertEqual(self._outputs(snapshot, a), (graph.root, None, None))
        self.assertEqual(snapshot.inputs(graph.root), [InputLink(a.number, 0)])

    def test_commit_requires_output_zero_on_every_non_root_node(self) -> None:
        graph = Graph()
        a = graph.create_node()
        b = graph.create_node(2)
        with self.assertRaises(UnboundOutputError) as raised:
            graph.commit()
        self.assertEqual(raised.exception.nodes, frozenset((a, b)))
        self.assertIn("[1, 2]", str(raised.exception))
        self.assertIsNone(graph.snapshot)
        graph.edit_link(a, 0, graph.root)
        graph.edit_link(b, 1, a)
        with self.assertRaises(UnboundOutputError) as raised:
            graph.commit()
        self.assertEqual(raised.exception.nodes, frozenset((b,)))
        self.assertIsNone(graph.get_output(b, 0))
        self.assertIs(graph.get_output(b, 1), a)
        graph.edit_link(b, 0, graph.root)
        self.assertEqual(graph.commit().node_order, (graph.root, a, b))

    def test_direct_snapshot_construction_also_requires_output_zero(self) -> None:
        root, a = Node(0), Node(1)
        with self.assertRaises(UnboundOutputError) as raised:
            GraphSnapshot({root: (), a: (None, root)}, root)
        self.assertEqual(raised.exception.nodes, frozenset((a,)))
        snapshot = GraphSnapshot({root: (), a: (root, None, None)}, root)
        self.assertIs(snapshot.get_output(a, 0), root)
        self.assertIsNone(snapshot.get_output(a, 2))

    def test_empty_and_nonexistent_slots_have_different_results(self) -> None:
        graph = Graph()
        a = graph.create_node(2)
        self.assertIsNone(graph.get_output(a, 0))
        graph.edit_link(a, 0, graph.root)
        for reader in (graph, graph.commit()):
            self.assertIs(reader.get_output(a, 0), graph.root)
            self.assertIsNone(reader.get_output(a, 1))
            with self.assertRaises(UnknownLinkError):
                reader.get_output(a, 2)

    def test_getters_enumerate_later_slots_after_an_empty_target(self) -> None:
        graph = Graph()
        a = graph.create_node()
        b = graph.create_node(3)
        graph.edit_link(a, 0, graph.root)
        graph.edit_link(b, 0, graph.root)
        graph.edit_link(b, 2, a)
        for reader in (graph, graph.commit()):
            self.assertEqual(reader.get_output_count(b), 3)
            self.assertIsNone(reader.get_output(b, 1))
            self.assertIs(reader.get_output(b, 2), a)

    def test_clearing_does_not_change_output_count_or_other_slot_numbers(self) -> None:
        graph, a, b, c = self._example()
        graph.edit_link(b, 0, None)
        self.assertEqual(graph.get_output_count(b), 2)
        self.assertIs(graph.get_output(b, 1), a)
        with self.assertRaises(UnboundOutputError) as raised:
            graph.commit()
        self.assertEqual(raised.exception.nodes, frozenset((b,)))
        graph.edit_link(b, 0, graph.root)
        self.assertEqual(self._outputs(graph, b), (graph.root, a))
        self.assertIs(graph.get_output(c, 0), b)

    def test_multiple_empty_slots_are_not_duplicate_targets(self) -> None:
        graph = Graph()
        a = graph.create_node(4)
        graph.edit_link(a, 0, graph.root)
        graph.edit_link(a, 3, None)
        self.assertEqual(self._outputs(graph.commit(), a), (graph.root, None, None, None))

    def test_inputs_return_permanent_source_ids_and_output_numbers(self) -> None:
        graph, a, b, c = self._example()
        for reader in (graph, graph.commit()):
            self.assertIsInstance(reader.inputs(graph.root), list)
            self.assertEqual(reader.inputs(graph.root), [InputLink(1, 0), InputLink(2, 0)])
            self.assertEqual(reader.inputs(a), [InputLink(2, 1)])
            self.assertEqual(reader.inputs(b), [InputLink(3, 0)])
            self.assertEqual(reader.inputs(c), [])
        self.assertEqual(
            asdict(graph.inputs(a)[0]),
            {"source_node_id": b.number, "output_link_number": 1},
        )

    def test_inputs_are_sorted_by_source_id_not_array_position(self) -> None:
        graph, a, b, c = self._example()
        inserted = graph.create_node(position=1)
        graph.edit_link(inserted, 0, graph.root)
        self.assertEqual(graph.position(inserted), 1)
        self.assertEqual(inserted.number, 4)
        self.assertEqual(
            graph.inputs(graph.root),
            [InputLink(a.number, 0), InputLink(b.number, 0), InputLink(4, 0)],
        )
        self.assertEqual(graph.inputs(c), [])

    def test_inputs_only_report_immediate_connections(self) -> None:
        graph, a, b, c = self._example()
        graph.edit_link(b, 1, None)
        graph.edit_link(b, 0, a)
        for reader in (graph, graph.commit()):
            self.assertEqual(reader.inputs(graph.root), [InputLink(a.number, 0)])
            self.assertEqual(reader.inputs(a), [InputLink(b.number, 0)])
            self.assertEqual(reader.inputs(b), [InputLink(c.number, 0)])

    def test_input_results_cannot_mutate_the_graph(self) -> None:
        graph, a, _, _ = self._example()
        records = graph.inputs(a)
        with self.assertRaises(FrozenInstanceError):
            setattr(records[0], "source_node_id", 99)
        records.clear()
        self.assertEqual(graph.inputs(a), [InputLink(2, 1)])

    def test_inputs_update_after_retargeting_clearing_and_deletion(self) -> None:
        graph, a, b, c = self._example()
        graph.edit_link(c, 0, a)
        self.assertEqual(graph.inputs(b), [])
        self.assertEqual(graph.inputs(a), [InputLink(b.number, 1), InputLink(c.number, 0)])
        graph.edit_link(b, 1, None)
        self.assertEqual(graph.inputs(a), [InputLink(c.number, 0)])
        graph.delete_node(c)
        self.assertEqual(graph.inputs(a), [])

    def test_duplicate_targets_are_rejected_immediately_without_mutation(self) -> None:
        graph, a, b, _ = self._example()
        snapshot = graph.commit()
        for number, target in ((0, a), (1, graph.root)):
            with self.subTest(slot=number):
                with self.assertRaises(DuplicateLinkError):
                    graph.edit_link(b, number, target)
                self.assertEqual(self._outputs(graph, b), (graph.root, a))
                self.assertIs(graph.snapshot, snapshot)
        self.assertEqual(graph.inputs(a), [InputLink(b.number, 1)])

    def test_same_target_in_the_same_slot_is_a_no_op(self) -> None:
        graph, a, b, _ = self._example()
        graph.edit_link(b, 1, a)
        self.assertEqual(self._outputs(graph.commit(), b), (graph.root, a))

    def test_swap_clears_one_slot_before_retargeting(self) -> None:
        graph, a, b, _ = self._example()
        before = graph.commit()
        with self.assertRaises(DuplicateLinkError):
            graph.edit_link(b, 1, graph.root)
        graph.edit_link(b, 0, None)
        with self.assertRaises(UnboundOutputError):
            graph.commit()
        self.assertIs(graph.snapshot, before)
        self.assertEqual(self._outputs(graph, b), (None, a))
        graph.edit_link(b, 1, graph.root)
        graph.edit_link(b, 0, a)
        after = graph.commit()
        self.assertEqual(self._outputs(after, b), (a, graph.root))
        self.assertEqual(self._outputs(before, b), (graph.root, a))

    def test_swap_can_clear_a_later_slot_and_commit_each_stage(self) -> None:
        graph, a, b, _ = self._example()
        graph.edit_link(b, 1, None)
        self.assertEqual(self._outputs(graph.commit(), b), (graph.root, None))
        graph.edit_link(b, 0, a)
        self.assertEqual(self._outputs(graph.commit(), b), (a, None))
        graph.edit_link(b, 1, graph.root)
        self.assertEqual(self._outputs(graph.commit(), b), (a, graph.root))

    def test_different_sources_and_distinct_targets_may_share_dependencies(self) -> None:
        graph, a, b, _ = self._example()
        snapshot = graph.commit()
        self.assertIs(snapshot.get_output(a, 0), graph.root)
        self.assertIs(snapshot.get_output(b, 0), graph.root)
        self.assertIs(snapshot.get_output(b, 1), a)

    def test_deletion_leaves_output_zero_empty_until_reconnected(self) -> None:
        graph, a, b, c = self._example()
        before = graph.commit()
        graph.delete_node(b)
        with self.assertRaises(UnboundOutputError) as raised:
            graph.commit()
        self.assertEqual(raised.exception.nodes, frozenset((c,)))
        self.assertEqual(graph.node_order, (graph.root, a, c))
        self.assertEqual(graph.get_output_count(c), 1)
        self.assertIsNone(graph.get_output(c, 0))
        self.assertIs(graph.snapshot, before)
        graph.edit_link(c, 0, graph.root)
        self.assertIs(graph.commit().get_output(c, 0), graph.root)
        self.assertIs(before.get_output(c, 0), b)

    def test_deletion_never_compacts_output_slots_or_recursively_deletes_nodes(self) -> None:
        graph, a, b, c = self._example()
        d = graph.create_node(3)
        graph.edit_link(d, 0, graph.root)
        graph.edit_link(d, 1, a)
        graph.edit_link(d, 2, b)
        graph.delete_node(a)
        snapshot = graph.commit()
        self.assertEqual(self._outputs(snapshot, d), (graph.root, None, b))
        self.assertEqual(self._outputs(snapshot, b), (graph.root, None))
        self.assertIs(snapshot.get_output(c, 0), b)
        self.assertEqual(snapshot.get_output_count(d), 3)

    def test_deleting_a_user_keeps_its_dependencies(self) -> None:
        graph, a, b, c = self._example()
        graph.delete_node(c)
        self.assertEqual(graph.commit().nodes, frozenset((graph.root, a, b)))
        self.assertEqual(graph.inputs(b), [])

    def test_root_cannot_be_deleted_or_given_an_output(self) -> None:
        graph = Graph()
        with self.assertRaises(RootDeletionError):
            graph.delete_node(graph.root)
        for target in (None, graph.root):
            with self.assertRaises(UnknownLinkError):
                graph.edit_link(graph.root, 0, target)
        self.assertEqual(graph.commit().get_output_count(graph.root), 0)

    def test_fixed_slots_and_relative_order_cannot_be_edited_independently(self) -> None:
        graph, _, b, _ = self._example()
        for method in ("move_node", "delete_link", "add_link"):
            self.assertFalse(hasattr(graph, method))
        with self.assertRaises(AttributeError):
            setattr(graph, "node_order", tuple(reversed(graph.node_order)))
        graph.edit_link(b, 0, None)
        self.assertEqual(graph.get_output_count(b), 2)

    def test_removed_navigation_apis_are_not_kept_as_aliases(self) -> None:
        graph = Graph()
        for reader in (graph, graph.commit()):
            for method in (
                "view", "direct_outputs", "direct_inputs", "all_outputs",
                "all_inputs", "outlinks", "children", "link", "outputs",
            ):
                with self.subTest(method=method):
                    self.assertFalse(hasattr(reader, method))
        for name in ("GraphView", "DraftView", "UnboundLinksError"):
            self.assertFalse(hasattr(node_package, name))

    def test_creation_appends_or_inserts_without_changing_existing_relative_order(self) -> None:
        graph, a, b, c = self._example()
        inserted = graph.create_node(2, position=2)
        self.assertEqual(graph.node_order, (graph.root, a, inserted, b, c))
        self.assertEqual(inserted.number, 4)
        self.assertEqual(graph.position(inserted), 2)
        self.assertEqual(graph.position(b), 3)
        self.assertEqual(self._outputs(graph, b), (graph.root, a))
        self.assertEqual(self._outputs(graph, inserted), (None, None))
        self.assertIs(graph.get_output(c, 0), b)

    def test_insertion_and_deletion_shift_indexes_not_ids_targets_or_slot_numbers(self) -> None:
        graph, a, b, c = self._example()
        before = graph.commit()
        inserted = graph.create_node(position=2)
        graph.edit_link(inserted, 0, a)
        graph.edit_link(b, 1, inserted)
        middle = graph.commit()
        self.assertEqual(middle.node_order, (graph.root, a, inserted, b, c))
        self.assertEqual(before.position(b), 2)
        self.assertEqual(middle.position(b), 3)
        graph.delete_node(inserted)
        after = graph.commit()
        self.assertEqual(after.node_order, (graph.root, a, b, c))
        self.assertEqual(after.position(b), 2)
        self.assertEqual(self._outputs(after, b), (graph.root, None))
        self.assertIs(before.get_output(b, 1), a)

    def test_root_stays_first_when_inserting_at_first_and_last_allowed_positions(self) -> None:
        graph, a, b, c = self._example()
        first = graph.create_node(position=1)
        last = graph.create_node(position=len(graph.node_order))
        self.assertEqual(graph.node_order, (graph.root, first, a, b, c, last))
        graph.edit_link(first, 0, graph.root)
        graph.edit_link(last, 0, graph.root)
        self.assertEqual(graph.commit().position(graph.root), 0)

    def test_invalid_creation_does_not_consume_ids(self) -> None:
        graph = Graph()
        for count in (0, -1, True, False, 1.5, "1"):
            self.assertRaises(InvalidOutputCountError, graph.create_node, count)
        for position in (0, -1, 2, True, False, 1.5, "1"):
            self.assertRaises(
                InvalidNodePositionError, graph.create_node, position=position
            )
        self.assertEqual(graph.node_order, (graph.root,))
        self.assertEqual(graph.create_node().number, 1)

    def test_node_ids_never_change_or_get_reused(self) -> None:
        graph, a, b, c = self._example()
        graph.delete_node(b)
        with self.assertRaises(UnboundOutputError):
            graph.commit()
        d = graph.create_node()
        self.assertEqual((a.number, c.number, d.number), (1, 3, 4))
        with self.assertRaises(FrozenInstanceError):
            setattr(d, "number", 2)
        for node in (a, c, d):
            graph.delete_node(node)
        self.assertEqual(graph.create_node().number, 5)

    def test_output_order_compares_positions_not_ids(self) -> None:
        graph, a, b, _ = self._example()
        d = graph.create_node(position=2)
        graph.edit_link(d, 0, a)
        graph.edit_link(b, 1, d)
        self.assertIs(graph.commit().get_output(b, 1), d)
        with self.assertRaises(InvalidLinkOrderError) as raised:
            graph.edit_link(d, 0, b)
        self.assertIs(raised.exception.source, d)
        self.assertIs(raised.exception.target, b)
        self.assertEqual(raised.exception.number, 0)
        self.assertEqual(raised.exception.source_position, 2)
        self.assertEqual(raised.exception.target_position, 3)
        self.assertIs(graph.get_output(d, 0), a)

    def test_same_or_later_target_is_rejected_by_one_position_rule(self) -> None:
        graph, a, b, c = self._example()
        for target in (a, b, c):
            with self.assertRaises(InvalidLinkOrderError):
                graph.edit_link(a, 0, target)
            self.assertIs(graph.get_output(a, 0), graph.root)

    def test_invalid_output_numbers_are_errors_not_empty_targets(self) -> None:
        graph, _, b, _ = self._example()
        for reader in (graph, graph.commit()):
            for n in (-1, 2, 99, True, False, 1.5, "0"):
                self.assertRaises(UnknownLinkError, reader.get_output, b, n)
        for n in (-1, 2, True, False, 1.5):
            self.assertRaises(UnknownLinkError, graph.edit_link, b, n, None)
        self.assertEqual(graph.get_output_count(b), 2)

    def test_foreign_forged_and_deleted_handles_are_rejected(self) -> None:
        graph, a, b, c = self._example()
        snapshot = graph.commit()
        for unknown in (Graph().root, Node(a.number)):
            for reader in (graph, snapshot):
                for action in (
                    lambda: reader.get_output(unknown, 0),
                    lambda: reader.get_output_count(unknown),
                    lambda: reader.inputs(unknown),
                    lambda: reader.position(unknown),
                ):
                    with self.assertRaises(UnknownNodeError):
                        action()
            with self.assertRaises(UnknownNodeError):
                graph.edit_link(c, 0, unknown)
        graph.delete_node(b)
        for action in (
            lambda: graph.get_output(b, 0),
            lambda: graph.get_output_count(b),
            lambda: graph.inputs(b),
            lambda: graph.position(b),
            lambda: graph.edit_link(b, 0, graph.root),
            lambda: graph.delete_node(b),
        ):
            with self.assertRaises(UnknownNodeError):
                action()
        self.assertEqual(snapshot.get_output_count(b), 2)
        self.assertIsNone(graph.get_output(c, 0))

    def test_snapshots_are_fixed_and_queries_on_the_draft_are_current(self) -> None:
        graph, a, b, c = self._example()
        snapshot = graph.commit()
        graph.edit_link(c, 0, a)
        self.assertIs(graph.get_output(c, 0), a)
        self.assertIs(snapshot.get_output(c, 0), b)
        self.assertEqual(graph.inputs(a), [InputLink(2, 1), InputLink(3, 0)])
        self.assertEqual(snapshot.inputs(a), [InputLink(2, 1)])
        with self.assertRaises(FrozenInstanceError):
            setattr(snapshot, "root", Node(99))
        self.assertFalse(hasattr(snapshot, "edit_link"))

    def test_only_the_latest_successful_snapshot_is_retained(self) -> None:
        graph, _, b, _ = self._example()
        self.assertIsNone(graph.snapshot)
        first = graph.commit()
        self.assertIs(graph.snapshot, first)
        with self.assertRaises(DuplicateLinkError):
            graph.edit_link(b, 1, graph.root)
        self.assertIs(graph.snapshot, first)
        graph.edit_link(b, 1, None)
        latest = graph.commit()
        self.assertIs(graph.snapshot, latest)
        self.assertIsNot(latest, first)
        self.assertEqual(
            [value for value in vars(graph).values() if isinstance(value, GraphSnapshot)],
            [latest],
        )

    def test_snapshot_constructor_copies_nullable_slot_data_and_mapping_order(self) -> None:
        root, a, b = Node(0), Node(7), Node(2)
        links = {root: [], a: [root, None], b: [a]}
        snapshot = GraphSnapshot(links, root)
        links[a].clear()
        links.clear()
        self.assertEqual(snapshot.node_order, (root, a, b))
        self.assertEqual(self._outputs(snapshot, a), (root, None))
        self.assertEqual(snapshot.inputs(a), [InputLink(b.number, 0)])

    def test_snapshot_constructor_rejects_invalid_structure(self) -> None:
        root, a, b = Node(0), Node(1), Node(2)
        with self.assertRaises(RootOutputLinkError):
            GraphSnapshot({root: (a,), a: (None,)}, root)
        with self.assertRaises(InvalidOutputCountError):
            GraphSnapshot({root: (), a: ()}, root)
        with self.assertRaises(DuplicateLinkError):
            GraphSnapshot({root: (), a: (root, root, None)}, root)
        with self.assertRaises(UnknownNodeError):
            GraphSnapshot({root: (), a: (b,)}, root)
        with self.assertRaises(InvalidLinkOrderError):
            GraphSnapshot({root: (), a: (b,), b: (root,)}, root)
        with self.assertRaises(InvalidNodePositionError):
            GraphSnapshot({a: (root,), root: ()}, root)
        with self.assertRaises(UnknownNodeError):
            GraphSnapshot({root: ()}, b)
        with self.assertRaisesRegex(ValueError, "number 0"):
            GraphSnapshot({a: ()}, a)
        forged = Node(a.number)
        with self.assertRaisesRegex(ValueError, "unique"):
            GraphSnapshot({root: (), a: (None,), forged: (None,)}, root)
        self.assertRaises(TypeError, GraphSnapshot, {root: frozenset()}, root)

    def test_node_numbers_must_be_non_negative_integers(self) -> None:
        for value in (-1, True, False, 1.5, "1"):
            self.assertRaises(ValueError, Node, value)

    def test_every_creation_time_insertion_order_obeys_the_position_rule(self) -> None:
        for second, third in product(range(1, 3), range(1, 4)):
            graph = Graph()
            graph.create_node()
            graph.create_node(position=second)
            graph.create_node(position=third)
            order = graph.node_order
            for source_position, source in enumerate(order[1:], 1):
                for target_position, target in enumerate(order):
                    if target_position < source_position:
                        graph.edit_link(source, 0, target)
                        self.assertIs(graph.get_output(source, 0), target)
                    else:
                        before = graph.get_output(source, 0)
                        with self.assertRaises(InvalidLinkOrderError):
                            graph.edit_link(source, 0, target)
                        self.assertIs(graph.get_output(source, 0), before)
            self.assertEqual(graph.commit().node_order, order)
            graph.delete_node(order[2])
            for source in graph.node_order[1:]:
                if graph.get_output(source, 0) is None:
                    graph.edit_link(source, 0, graph.root)
            self.assertEqual(graph.commit().node_order, order[:2] + order[3:])

    def test_all_nullable_two_slot_three_node_candidates(self) -> None:
        accepted = 0
        for choices in product(range(4), repeat=4):
            with self.subTest(targets=choices):
                root, a, b = nodes = (Node(0), Node(1), Node(2))
                possible = (None, *nodes)
                links = {
                    root: (),
                    a: tuple(possible[index] for index in choices[:2]),
                    b: tuple(possible[index] for index in choices[2:]),
                }
                expected_error: type[ValueError] | None = None
                if links[a][0] is None or links[b][0] is None:
                    expected_error = UnboundOutputError
                else:
                    for source in (a, b):
                        bound = [target for target in links[source] if target is not None]
                        if len(set(bound)) != len(bound):
                            expected_error = DuplicateLinkError
                            break
                        if any(target.number >= source.number for target in bound):
                            expected_error = InvalidLinkOrderError
                            break
                if expected_error is not None:
                    with self.assertRaises(expected_error):
                        GraphSnapshot(links, root)
                    continue
                accepted += 1
                snapshot = GraphSnapshot(links, root)
                for source in nodes:
                    self.assertEqual(self._outputs(snapshot, source), links[source])
                    self.assertEqual(
                        snapshot.inputs(source),
                        [
                            InputLink(user.number, n)
                            for user in nodes
                            for n, target in enumerate(links[user])
                            if target is source
                        ],
                    )
                    current = source
                    while current is not root:
                        target = snapshot.get_output(current, 0)
                        if target is None:
                            raise AssertionError("Every committed output-0 chain must reach root")
                        self.assertLess(snapshot.position(target), snapshot.position(current))
                        current = target
        self.assertEqual(accepted, 4)

    def test_all_512_nonempty_arrow_candidate_shapes(self) -> None:
        accepted = 0
        for mask in range(512):
            root, a, b = nodes = (Node(0), Node(1), Node(2))
            links = {
                nodes[i]: tuple(
                    nodes[j] for j in range(3) if mask & (1 << (3 * i + j))
                )
                for i in range(3)
            }
            if mask & 7:
                self.assertRaises(RootOutputLinkError, GraphSnapshot, links, root)
            elif any(not links[node] for node in (a, b)):
                self.assertRaises(InvalidOutputCountError, GraphSnapshot, links, root)
            elif any(target.number >= source.number for source in nodes for target in links[source]):
                self.assertRaises(InvalidLinkOrderError, GraphSnapshot, links, root)
            else:
                accepted += 1
                self.assertEqual(GraphSnapshot(links, root).node_order, nodes)
        self.assertEqual(accepted, 3)

    def test_large_ordered_graph_needs_no_traversal_or_recursion(self) -> None:
        graph = Graph()
        previous = graph.root
        for _ in range(5000):
            node = graph.create_node()
            graph.edit_link(node, 0, previous)
            previous = node
        snapshot = graph.commit()
        self.assertEqual(len(snapshot.nodes), 5001)
        self.assertEqual(snapshot.get_output_count(previous), 1)
        self.assertIs(snapshot.get_output(previous, 0), graph.node_order[-2])
        self.assertEqual(snapshot.inputs(graph.root), [InputLink(1, 0)])


if __name__ == "__main__":
    unittest.main()
