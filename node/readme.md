# Node graph

This is the graph foundation for Nod. It has nodes, an ordered node array,
and numbered output slots. Types, variables, functions, and execution
rules are not built in. The language and its checker are implemented in
[Nod](../nod/nod.md).

## 1. A link means "based on this information"

Each node also has an optional immutable `value: bytes | None`. Set it at
creation with `graph.create_node(value=b"...")`. A `bytearray` is copied into
immutable bytes; `None` (vacant) differs from `b""` (an empty byte value).
The root's value is `None`. Values do not affect identity, link validation,
or ordering. The Node layer assigns no encoding or type to these bytes.
Published values cannot be reassigned; construct a new node for a new value.
Snapshots and retained node handles preserve their values after deletion.

```text
b[1] -> a
```

This means b's output 1 points to a. The source b is based on information
from the target a. The link does not execute or copy a.

The names a and b are code names used in examples. Each node also has a
permanent numeric ID.

## 2. Root 0 is the starting information

Every graph starts with root node 0.

- Root is always at array position 0.
- Root has no outputs, not even output 0.
- Root cannot be deleted.
- Other nodes may point to root.

Root does not point to the rest of the program. The other nodes depend on it.

## 3. Node IDs and array positions are different

New node IDs increase from 1. An ID never changes and is never reused
after deletion.

New nodes append to the array by default. A new node may instead choose
an insertion position when it is created.

```text
Before:
position    0    1    2    3
node ID    [0,   1,   2,   3]

Insert new node 4 at position 2:
position    0    1    2    3    4
node ID    [0,   1,   4,   2,   3]
```

Node 2 shifts from position 2 to 3, but its ID stays 2.
Existing nodes keep their order relative to one another. There is no
operation to move an existing node.

Deletion shifts later positions down. It does not rename nodes or change
their connections to different targets.

## 4. Bound outputs can point only to earlier nodes

The only link-order condition is:

```text
position(target) < position(source)
```

For order `[0, 1, 4, 2, 3]`:

```text
2[1] -> 4     allowed: node 4 is earlier
4[0] -> 2     rejected: node 2 is later
4[0] -> 4     rejected: the positions are equal
```

Any earlier node is permitted, not only the immediate neighbor.
The condition uses array positions, not node IDs.

This is checked during editing. Following links strictly decreases the
position, so a cycle cannot be created. No separate cycle search is needed.

## 5. Output slots stay fixed

Choose a positive output count when creating a non-root node.
Its slots are numbered `0, 1, 2, ...` and initially have no targets.

The count and slot numbers stay fixed for that node's lifetime.
We cannot add, remove, or renumber individual slots.
We can retarget a slot or set its target to `None`.

```text
b has three output slots:

b[0] -> root
b[1] -> None
b[2] -> a
```

Output 1 still exists. Output 2 does not shift down to fill the gap.
Deleting b removes all slots owned by b.

## 6. Every output is required at commit

Every output slot must target an existing earlier node before commit.
Root has zero slots, so it meets this rule without any targets.

Any slot may be empty while editing. Commit then raises `UnboundOutputError`
whose `.nodes` reports all nodes with at least one empty slot.

This is a valid draft, but not a committed snapshot:

```text
a[0] -> root
b[0] -> a
b[1] -> None       blocks commit
c[0] -> b
```

Following output 0 from any non-root node eventually reaches root:

```text
c --[0]--> b --[0]--> a --[0]--> root
```

Every step goes to a smaller position, and no non-root output 0 can be
empty after commit. This connects every committed node to root without
a separate connectivity traversal.

Later, Nod may interpret output 0 as a node's context.
The Node layer requires every connection; it does not implement context types.

## 7. One source cannot have duplicate targets

Two outputs of one node cannot point to the same nonempty target,
even while editing. That edit raises `DuplicateLinkError` without
changing any connection.

Several slots may be empty while drafting. `None` is not a node and is not a
duplicate target. Every empty slot must be repaired before commit.

Different sources may share a target. Distinct targets may also share
their own dependencies.

To swap targets, clear one slot first:

```text
Initially: b[0] -> root, b[1] -> a
Clear 0:   b[0] -> None, b[1] -> a       editing allowed; commit blocked
Edit 1:    b[0] -> None, b[1] -> root    editing allowed; commit blocked
Fill 0:    b[0] -> a,    b[1] -> root    commit succeeds
```

You may instead clear output 1 first. Then output 0 can stay connected
throughout the swap, but intermediate commits are still blocked.

## 8. Deleting a target leaves its users' slots in place

```text
Array: [0, 1, 2, 3]

1[0] -> root 0
2[0] -> root 0
2[1] -> node 1
3[0] -> node 2
```

Delete node 2:

```text
Array: [0, 1, 3]

1[0] -> root 0
3[0] -> None
```

Node 2 and its owned slots are gone. Node 3 keeps output 0 with an
empty target. Nothing is renumbered.

Commit fails because node 3's output 0 is empty.
Set `3[0] -> root 0`, and commit succeeds.

If deletion empties a later output, commit is blocked in exactly the same way.
Dependencies and users are not deleted automatically.

## 9. Three connection queries

Both the current graph and its snapshot provide:

| Method | Result |
|---|---|
| `get_output(node, n)` | The target node in slot n, or `None`. |
| `get_output_count(node)` | The fixed number of slots, including empty ones. |
| `inputs(node)` | Incoming source-ID/output-number records. |

An empty slot and a nonexistent slot are different:

```text
b has: [root, None, a]

get_output_count(b) -> 3
get_output(b, 1)    -> None
get_output(b, 2)    -> a
get_output(b, 3)    -> UnknownLinkError
```

Use the output count when enumerating slots. Do not stop at `None`;
there may be a connected slot after it.

Each incoming result has two fields:

```text
InputLink(source_node_id=2, output_link_number=1)
```

The source ID is permanent, not an array position.
The output number belongs to that source, not to the receiving node.
Incoming numbers may overlap:

```text
1[0] -> root
2[0] -> root

inputs(root) -> [
    InputLink(source_node_id=1, output_link_number=0),
    InputLink(source_node_id=2, output_link_number=0)
]
```

Inputs are ordered by source ID, then output number.
No incoming connections means `[]`.

The queries read the whole selected graph object. There is no `View`,
output-list alias, recursive traversal, distance bound, or path query.
The caller can build a deeper traversal if needed.

## 10. A small Python example

Run from the repository root:

```python
from node import Graph, InputLink

graph = Graph()
a = graph.create_node()
b = graph.create_node(2)
c = graph.create_node()

graph.edit_link(a, 0, graph.root)
graph.edit_link(b, 0, graph.root)
graph.edit_link(b, 1, a)
graph.edit_link(c, 0, b)
snapshot = graph.commit()

assert graph.position(b) == 2
assert graph.get_output_count(b) == 2
assert graph.get_output(b, 1) is a
assert snapshot.get_output(b, 1) is a
assert graph.inputs(a) == [InputLink(2, 1)]
```

Every slot is connected. Empty slots are permitted in drafts only.
The code names a, b, and c are shown in the animation next to their IDs.

Continue the example to delete b and reconnect c:

```python
from node import UnboundOutputError

graph.delete_node(b)
assert graph.get_output_count(c) == 1
assert graph.get_output(c, 0) is None

try:
    graph.commit()
except UnboundOutputError as error:
    assert error.nodes == frozenset((c,))
else:
    raise AssertionError("An empty output 0 must prevent commit")

graph.edit_link(c, 0, graph.root)
snapshot = graph.commit()
assert snapshot.get_output(c, 0) is graph.root
```

## 11. The current graph and its snapshot

Queries on `graph` read current edits immediately.

`graph.snapshot` is `None` before the first successful commit.
Commit creates a fixed `GraphSnapshot` and replaces that property.
The graph retains one latest successful snapshot, not a history.

Queries on a snapshot read fixed committed data with all slots connected.
Later edits do not change it. Callers may retain an older returned
snapshot if they choose; the graph does not keep an old-snapshot list.

A failed commit leaves the draft editable and the latest successful
snapshot unchanged. It does not roll back the draft.
An invalid edit also reports an error without changing data.

`node_order` returns the ordered node handles.
`position(node)` returns their current zero-based array index.
Root always has position 0.

Foreign, forged, deleted, or missing node handles raise `UnknownNodeError`.
Invalid output numbers raise `UnknownLinkError`.
Invalid creation counts or positions raise `InvalidOutputCountError` or
`InvalidNodePositionError`.
Order violations raise `InvalidLinkOrderError`.
Duplicate targets raise `DuplicateLinkError`.
Any empty output at commit raises `UnboundOutputError`.
Root cannot be deleted or given output slots.

Direct snapshot construction checks the same rules and copies its input
data. Mapping key order supplies node order; target sequences supply slots.

## 12. Run and inspect

Python 3.10 or newer is sufficient. No third-party packages are needed.

```sh
python3 -m node.layer0_demo
python3 -m unittest -v node.test_layer0 node.test_animation
```

Open [layer0_animation.html](./layer0_animation.html) for the diagrams,
array display, indexed reads, and commit errors.
The implementation is [layer0.py](./layer0.py); the runnable example is
[layer0_demo.py](./layer0_demo.py).

Commit is in memory. It does not save a graph file or create a Git commit.
This layer does not check program types, proofs, execution, or language
scope. Those meanings belong to Nod later.
