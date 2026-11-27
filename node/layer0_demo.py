"""Run from the repository root with python3 -m node.layer0_demo."""

from node import (
    DuplicateLinkError,
    Graph,
    InputLink,
    InvalidLinkOrderError,
    UnboundOutputError,
)


def main() -> None:
    graph = Graph()
    node1 = graph.create_node()
    node2 = graph.create_node(2)
    graph.edit_link(node1, 0, graph.root)
    graph.edit_link(node2, 0, graph.root)
    graph.edit_link(node2, 1, node1)
    snapshot = graph.commit()

    assert graph.get_output_count(node2) == 2
    assert graph.get_output(node2, 0) is graph.root
    assert graph.get_output(node2, 1) is node1
    assert graph.inputs(graph.root) == [InputLink(1, 0), InputLink(2, 0)]
    assert graph.inputs(node1) == [InputLink(2, 1)]
    print("READ: node 2 has two slots; every committed slot is connected.")
    print("INPUTS TO ROOT:", graph.inputs(graph.root))

    try:
        graph.edit_link(node2, 1, graph.root)
    except DuplicateLinkError as error:
        print(f"EXPECTED EDIT REJECTION: {error}")
    else:
        raise AssertionError("A duplicate nonempty target must be rejected immediately")
    graph.edit_link(node2, 0, None)
    try:
        graph.commit()
    except UnboundOutputError as error:
        assert error.nodes == frozenset((node2,))
        print(f"EXPECTED OUTPUT-0 COMMIT REJECTION: {error}")
    else:
        raise AssertionError("Output 0 must be connected before commit")
    graph.edit_link(node2, 1, graph.root)
    graph.edit_link(node2, 0, node1)
    snapshot = graph.commit()
    assert snapshot.get_output(node2, 0) is node1
    assert snapshot.get_output(node2, 1) is graph.root
    print("SWAP: clear output 0 first; then retarget the two fixed slots.")

    graph.delete_node(node1)
    assert graph.get_output_count(node2) == 2
    assert graph.get_output(node2, 0) is None
    try:
        graph.commit()
    except UnboundOutputError as error:
        assert error.nodes == frozenset((node2,))
        print(f"EXPECTED DELETION COMMIT REJECTION: {error}")
    else:
        raise AssertionError("Deleting output 0's target must block commit")
    print("DELETE: the owned slots remain; output 0 needs a new target.")

    node3 = graph.create_node(position=1)
    graph.edit_link(node3, 0, graph.root)
    graph.edit_link(node2, 0, node3)
    assert [node.number for node in graph.node_order] == [0, 3, 2]
    assert graph.position(node3) == 1
    assert graph.inputs(node3) == [InputLink(2, 0)]
    try:
        graph.edit_link(node3, 0, node2)
    except InvalidLinkOrderError as error:
        print(f"EXPECTED POSITION REJECTION: {error}")
    else:
        raise AssertionError("The target must have an earlier array position")
    snapshot = graph.commit()
    assert graph.snapshot is snapshot
    assert snapshot.inputs(node3) == [InputLink(2, 0)]
    graph.edit_link(node2, 1, None)
    try:
        graph.commit()
    except UnboundOutputError as error:
        print(f"EXPECTED LATER-SLOT REJECTION: {error}")
    else:
        raise AssertionError("Later slots must also be bound")
    graph.edit_link(node2, 1, graph.root)
    graph.commit()
    print("LATEST COMMIT: order [0, 3, 2], no views, traversal API, or snapshot history.")


if __name__ == "__main__":
    main()
