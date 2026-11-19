"""Run with python3 layer0_demo.py."""

from layer0 import Graph, IncomingRootLinkError, UnknownNodeError, UnreachableNodesError


def main() -> None:
    graph = Graph()
    x = graph.create_node()
    child = graph.create_node()
    other = graph.create_node()
    graph.add_link(graph.root, x)
    graph.add_link(x, child)
    graph.add_link(child, x)

    try:
        graph.commit()
    except UnreachableNodesError as error:
        print(f"EXPECTED REJECTION: {error}")
    else:
        raise AssertionError("A detached node should prevent committing")

    graph.add_link(graph.root, other)
    snapshot = graph.commit()
    local = snapshot.view(x)
    assert local.nodes == frozenset((x, child))
    print("LOCAL: x sees itself and child, even though they form a cycle.")

    try:
        local.children(snapshot.root)
    except UnknownNodeError as error:
        print(f"EXPECTED VISIBILITY ERROR: {error}")
    else:
        raise AssertionError("A local view must not expose the root")

    global_view = snapshot.view(snapshot.root)
    assert global_view.nodes == snapshot.nodes
    print("GLOBAL: explicitly passing the root exposes every node.")

    try:
        graph.add_link(child, graph.root)
    except IncomingRootLinkError as error:
        print(f"EXPECTED ROOT-LINK REJECTION: {error}")
    else:
        raise AssertionError("The root must never receive a link")

    graph.add_link(child, other)
    updated = graph.commit()
    assert updated.view(x).nodes == frozenset((x, child, other))
    assert graph.root not in updated.view(x).nodes
    assert local.nodes == frozenset((x, child))
    print("NEW LINK: child -> other expands the new local view, but not to the root.")
    print("SNAPSHOT: the earlier local view remains unchanged.")


if __name__ == "__main__":
    main()
