# Nod: information described by ordered node outputs

Nod starts from the [node rules and examples](../node/readme.md).
Layers 1, 2, and 3 are paused.
No language types, parameters, or function execution rules are built in yet.

## The foundation

- Root 0 is first in the array, has no outputs, and cannot be deleted.
- Other nodes receive increasing permanent IDs and fixed positive output counts.
- New nodes append or choose an insertion position at creation.
- Existing nodes cannot be moved. Insertion/deletion shifts indexes, not IDs.
- Every nonempty output points to an earlier array position.
- Every non-root output 0 must be connected before commit.
- Later outputs may remain empty after commit; output 0 may be empty while editing.
- Two outputs of one source cannot target the same nonempty node.

A directed link means:

> The source node is based on the target node's information.

Positions decrease along links, so no cycle can be created.
Following output 0 from any committed non-root node eventually reaches root.
Nod may later give that output a context-like meaning; the graph foundation
only requires the connection.

## Fixed slots and deletion

```text
Array: [0, 1, 2, 3]

1[0] -> root 0
2[0] -> root 0
2[1] -> node 1
3[0] -> node 2

Delete node 2:
Array: [0, 1, 3]

1[0] -> root 0
3[0] -> nothing
```

Commit is blocked because node 3's required output 0 is empty.
Reconnect it to root, then commit succeeds. No other node is automatically
deleted. Deleting a target of a later output leaves an optional empty slot
that can still be committed.

To swap targets without creating a duplicate, clear one output first.
The slots themselves are never removed or renumbered.

## Reading the graph

The draft and snapshot expose the same three connection queries:

| API | Result |
|---|---|
| `get_output(node, n)` | Slot n's target node, or `None`. |
| `get_output_count(node)` | Fixed output count, including empty slots. |
| `inputs(node)` | `InputLink(source_node_id, output_link_number)` records. |

Source IDs are permanent IDs, not array positions. Incoming output numbers
may overlap when their sources differ. There is no separate input numbering.

There is no restricted view, path query, distance bound, or automatic
traversal. The caller can inspect the chosen graph object using these
basic queries.

`node_order` and `position(node)` expose the node array.
`commit()` creates a fixed snapshot and replaces `graph.snapshot`; the
graph does not maintain a snapshot history.

## Proposed Nod labels

```text
1[0] -> root 0    # parameters context
2[0] -> node 1    # parameter
3[0] -> node 1    # parameter
4[0] -> root 0    # function
4[1] -> node 1    # supplied input context
```

These are proposed labels, not built-in node kinds. `inputs(node1)` can
find the users of the context, but identifying actual parameters requires
a future Nod rule.

Run the [demo](../node/layer0_demo.py) with
`python3 -m node.layer0_demo`, or inspect the
[animation](../node/layer0_animation.html).
