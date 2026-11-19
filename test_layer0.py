import unittest
from dataclasses import FrozenInstanceError

from layer0 import (
    Graph,
    GraphSnapshot,
    GraphView,
    IncomingRootLinkError,
    Node,
    UnknownNodeError,
    UnreachableNodesError,
)


class Layer0Tests(unittest.TestCase):
    def test_root_cannot_receive_a_link(self) -> None:
        graph = Graph()
        child = graph.create_node()
        graph.add_link(graph.root, child)
        with self.assertRaisesRegex(IncomingRootLinkError, "root"):
            graph.add_link(child, graph.root)
        snapshot = graph.commit()
        self.assertEqual(snapshot.children(child), frozenset())
        self.assertEqual(snapshot.view(child).nodes, frozenset((child,)))

    def test_graph_starts_with_only_a_root(self) -> None:
        graph = Graph()
        snapshot = graph.commit()
        self.assertIs(snapshot.root, graph.root)
        self.assertEqual(snapshot.nodes, frozenset((graph.root,)))
        self.assertEqual(snapshot.children(graph.root), frozenset())

    def test_detached_nodes_are_allowed_until_commit(self) -> None:
        graph = Graph()
        detached = graph.create_node()
        with self.assertRaises(UnreachableNodesError) as raised:
            graph.commit()
        self.assertEqual(raised.exception.nodes, frozenset((detached,)))
        graph.add_link(graph.root, detached)
        self.assertIn(detached, graph.commit().nodes)

    def test_disconnected_cycle_is_not_enough(self) -> None:
        graph = Graph()
        a, b = graph.create_node(), graph.create_node()
        graph.add_link(a, b)
        graph.add_link(b, a)
        with self.assertRaises(UnreachableNodesError) as raised:
            graph.commit()
        self.assertEqual(raised.exception.nodes, frozenset((a, b)))
        graph.add_link(graph.root, a)
        self.assertEqual(len(graph.commit().nodes), 3)

    def test_shared_children_are_allowed(self) -> None:
        graph = Graph()
        a, b, child = (graph.create_node() for _ in range(3))
        graph.add_link(graph.root, a)
        graph.add_link(graph.root, b)
        graph.add_link(a, child)
        graph.add_link(b, child)
        snapshot = graph.commit()
        self.assertEqual(snapshot.view(a).nodes, frozenset((a, child)))
        self.assertEqual(snapshot.view(b).nodes, frozenset((b, child)))

    def test_duplicate_links_are_idempotent(self) -> None:
        graph = Graph()
        child = graph.create_node()
        graph.add_link(graph.root, child)
        graph.add_link(graph.root, child)
        self.assertEqual(graph.commit().children(graph.root), frozenset((child,)))

    def test_self_loop_is_allowed(self) -> None:
        graph = Graph()
        child = graph.create_node()
        graph.add_link(graph.root, child)
        graph.add_link(child, child)
        snapshot = graph.commit()
        self.assertEqual(snapshot.children(child), frozenset((child,)))
        self.assertEqual(snapshot.view(child).nodes, frozenset((child,)))

    def test_root_self_loop_is_rejected(self) -> None:
        graph = Graph()
        with self.assertRaises(IncomingRootLinkError):
            graph.add_link(graph.root, graph.root)
        self.assertEqual(graph.commit().children(graph.root), frozenset())

    def test_cycles_between_non_root_nodes_are_allowed(self) -> None:
        graph = Graph()
        a, b = graph.create_node(), graph.create_node()
        graph.add_link(graph.root, a)
        graph.add_link(a, b)
        graph.add_link(b, a)
        snapshot = graph.commit()
        self.assertEqual(snapshot.view(a).nodes, frozenset((a, b)))
        self.assertNotIn(graph.root, snapshot.view(a).nodes)

    def test_visibility_follows_all_outgoing_descendants(self) -> None:
        graph = Graph()
        a, b, c = (graph.create_node() for _ in range(3))
        graph.add_link(graph.root, a)
        graph.add_link(a, b)
        graph.add_link(b, c)
        snapshot = graph.commit()
        self.assertEqual(snapshot.view(a).nodes, frozenset((a, b, c)))
        self.assertEqual(snapshot.view(b).nodes, frozenset((b, c)))
        self.assertEqual(snapshot.view(c).nodes, frozenset((c,)))

    def test_incoming_links_do_not_grant_visibility(self) -> None:
        graph = Graph()
        child = graph.create_node()
        graph.add_link(graph.root, child)
        local = graph.commit().view(child)
        self.assertNotIn(graph.root, local.nodes)
        with self.assertRaises(UnknownNodeError):
            local.children(graph.root)

    def test_multiple_arguments_give_union_of_visibility(self) -> None:
        graph = Graph()
        a, b = graph.create_node(), graph.create_node()
        graph.add_link(graph.root, a)
        graph.add_link(graph.root, b)
        snapshot = graph.commit()
        self.assertEqual(snapshot.view(a, b, a).nodes, frozenset((a, b)))

    def test_root_argument_gives_global_visibility(self) -> None:
        graph = Graph()
        a, b = graph.create_node(), graph.create_node()
        graph.add_link(graph.root, a)
        graph.add_link(a, b)
        snapshot = graph.commit()
        self.assertEqual(snapshot.view(graph.root).nodes, snapshot.nodes)

    def test_local_view_does_not_expose_a_root_property(self) -> None:
        snapshot = Graph().commit()
        local = snapshot.view(snapshot.root)
        self.assertIs(type(local), GraphView)
        self.assertFalse(hasattr(local, "root"))
        self.assertFalse(hasattr(local, "graph"))

    def test_nested_views_cannot_expand_access(self) -> None:
        graph = Graph()
        a, b = graph.create_node(), graph.create_node()
        graph.add_link(graph.root, a)
        graph.add_link(a, b)
        local = graph.commit().view(a)
        self.assertEqual(local.view(b).nodes, frozenset((b,)))
        with self.assertRaises(UnknownNodeError):
            local.view(graph.root)

    def test_view_requires_explicit_arguments(self) -> None:
        with self.assertRaisesRegex(ValueError, "at least one"):
            Graph().commit().view()

    def test_nodes_from_other_graphs_are_rejected(self) -> None:
        graph, other = Graph(), Graph()
        for source, target in (
            (other.root, graph.root), (graph.root, other.root),
        ):
            with self.subTest(source=source, target=target):
                with self.assertRaises(UnknownNodeError):
                    graph.add_link(source, target)
        snapshot = graph.commit()
        with self.assertRaises(UnknownNodeError):
            snapshot.view(other.root)
        with self.assertRaises(UnknownNodeError):
            snapshot.children(other.root)
        self.assertEqual(snapshot.children(graph.root), frozenset())

    def test_same_display_number_does_not_forge_identity(self) -> None:
        graph = Graph()
        forged = Node(graph.root.number)
        self.assertIsNot(forged, graph.root)
        self.assertNotEqual(forged, graph.root)
        with self.assertRaises(UnknownNodeError):
            graph.add_link(graph.root, forged)

    def test_snapshot_and_view_are_immutable(self) -> None:
        graph = Graph()
        snapshot = graph.commit()
        view = snapshot.view(graph.root)
        self.assertIsInstance(view.nodes, frozenset)
        self.assertIsInstance(view.children(graph.root), frozenset)
        with self.assertRaises(FrozenInstanceError):
            setattr(view, "_links", {})
        with self.assertRaises(FrozenInstanceError):
            setattr(snapshot, "root", Node(99))
        with self.assertRaises(FrozenInstanceError):
            setattr(graph.root, "number", 99)

    def test_later_draft_edits_do_not_change_snapshots(self) -> None:
        graph = Graph()
        a = graph.create_node()
        graph.add_link(graph.root, a)
        first = graph.commit()
        local = first.view(a)
        b = graph.create_node()
        graph.add_link(a, b)
        second = graph.commit()
        self.assertEqual(local.nodes, frozenset((a,)))
        self.assertEqual(first.children(a), frozenset())
        self.assertNotIn(b, first.nodes)
        self.assertEqual(second.view(a).nodes, frozenset((a, b)))

    def test_failed_commit_does_not_change_existing_snapshot(self) -> None:
        graph = Graph()
        first = graph.commit()
        detached = graph.create_node()
        with self.assertRaises(UnreachableNodesError):
            graph.commit()
        self.assertEqual(first.nodes, frozenset((graph.root,)))
        graph.add_link(graph.root, detached)
        self.assertEqual(len(graph.commit().nodes), 2)

    def test_new_non_root_link_expands_new_view_only(self) -> None:
        graph = Graph()
        a, other = graph.create_node(), graph.create_node()
        graph.add_link(graph.root, a)
        graph.add_link(graph.root, other)
        old_local = graph.commit().view(a)
        graph.add_link(a, other)
        updated = graph.commit()
        self.assertEqual(old_local.nodes, frozenset((a,)))
        self.assertEqual(updated.view(a).nodes, frozenset((a, other)))
        self.assertNotIn(graph.root, updated.view(a).nodes)

    def test_view_constructor_rejects_dangling_links(self) -> None:
        a, b = Node(0), Node(1)
        with self.assertRaises(UnknownNodeError):
            GraphView({a: frozenset((b,))})

    def test_view_defensively_copies_input_mapping(self) -> None:
        a = Node(0)
        links = {a: frozenset[Node]()}
        view = GraphView(links)
        links.clear()
        self.assertEqual(view.nodes, frozenset((a,)))

    def test_snapshot_constructor_checks_root_reachability(self) -> None:
        a, b = Node(0), Node(1)
        with self.assertRaises(UnreachableNodesError):
            GraphSnapshot({a: frozenset(), b: frozenset()}, a)
        with self.assertRaises(UnknownNodeError):
            GraphSnapshot({a: frozenset()}, b)

    def test_snapshot_constructor_rejects_incoming_root_links(self) -> None:
        a, b = Node(0), Node(1)
        with self.assertRaises(IncomingRootLinkError):
            GraphSnapshot({a: frozenset((b,)), b: frozenset((a,))}, a)
        with self.assertRaises(IncomingRootLinkError):
            GraphSnapshot({a: frozenset((a,))}, a)

    def test_deep_graph_uses_iterative_traversal(self) -> None:
        graph = Graph()
        parent = graph.root
        for _ in range(5000):
            child = graph.create_node()
            graph.add_link(parent, child)
            parent = child
        snapshot = graph.commit()
        self.assertEqual(len(snapshot.view(graph.root).nodes), 5001)
        self.assertEqual(snapshot.view(parent).nodes, frozenset((parent,)))

    def test_all_directed_graphs_on_three_nodes(self) -> None:
        for mask in range(1 << 9):
            graph = Graph()
            nodes = (graph.root, graph.create_node(), graph.create_node())
            direct = [
                [bool(mask & (1 << (3 * i + j))) for j in range(3)]
                for i in range(3)
            ]
            links = {
                nodes[i]: frozenset(nodes[j] for j in range(3) if direct[i][j])
                for i in range(3)
            }
            paths = [[i == j or direct[i][j] for j in range(3)] for i in range(3)]
            for k in range(3):
                for i in range(3):
                    for j in range(3):
                        paths[i][j] = paths[i][j] or (paths[i][k] and paths[k][j])
            with self.subTest(edge_mask=mask):
                if any(direct[i][0] for i in range(3)):
                    with self.assertRaises(IncomingRootLinkError):
                        GraphSnapshot(links, graph.root)
                elif not all(paths[0]):
                    with self.assertRaises(UnreachableNodesError) as raised:
                        GraphSnapshot(links, graph.root)
                    self.assertEqual(
                        raised.exception.nodes,
                        frozenset(nodes[j] for j in range(3) if not paths[0][j]),
                    )
                else:
                    for source, targets in links.items():
                        for target in targets:
                            graph.add_link(source, target)
                    snapshot = graph.commit()
                    self.assertEqual(
                        GraphSnapshot(links, graph.root).nodes, snapshot.nodes
                    )
                    for i in range(3):
                        self.assertEqual(
                            snapshot.view(nodes[i]).nodes,
                            frozenset(nodes[j] for j in range(3) if paths[i][j]),
                        )


if __name__ == "__main__":
    unittest.main()
