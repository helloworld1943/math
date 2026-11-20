# Layer 0: nodes, directed links, and a root

Layer 0 is the ground of our graph system. It does not know what a function,
type, variable, containment, or proof means. Those meanings belong to the
next layer, which we now call [Layer 1](../layer1/nodetype.md).

From the view of Layer 0, writing a program means creating nodes and links.
The result is a graph.

The library is [layer0.py](./layer0.py). A runnable example is
[layer0_demo.py](./layer0_demo.py), and the tests are in
[test_layer0.py](./test_layer0.py).

The design notes about visibility, the root, and cycles are in
[extra_idea.md](./extra_idea.md).

For a visual walkthrough, open [layer0_animation.html](./layer0_animation.html)
in a browser. The roughly 30-second animation has play/pause, back/next, and
step controls. It illustrates the Python library without running Python in
the browser and needs no server, packages, or network access. Reduced-motion
preferences are respected and disable autoplay.

## 1. Basic rules

1. A graph starts with a designated root node. The root has no incoming links.
2. We can create nodes and directed links.
3. Every node in a committed graph must be reachable from the root.
4. Cycles and self-links between non-root nodes, and shared children, are allowed.
5. A computation's view includes its explicit argument nodes and all their
   outgoing descendants.
6. A view is read-only. Incoming links do not grant reverse access.
7. Passing the root explicitly gives access to the whole committed graph.

There are no built-in node kinds or link labels. Meanings can be built using
more nodes and links in the next layer.

The root is entry-only: no node, including the root itself, may point to it.
Whole-graph access is requested by passing the root explicitly.

## 2. Staged construction

We chose to allow detached nodes while editing:

```python
from layer0 import Graph

graph = Graph()
x = graph.create_node()
y = graph.create_node()

graph.add_link(graph.root, x)
graph.add_link(x, y)

snapshot = graph.commit()
```

`create_node()` does not add a link automatically. Before committing, the
graph is a draft and may contain unreachable nodes.

`commit()` checks that the root reaches every node. If not, it raises
`UnreachableNodesError`, whose `nodes` field identifies the unreachable nodes.
The draft is left available for repair.

`add_link(source, graph.root)` immediately raises `IncomingRootLinkError`
without adding a link. Unlike temporary detached nodes, incoming root links
are not allowed even in a draft. Directly constructing a `GraphSnapshot`
also checks that no link targets its root.

A disconnected cycle is not enough:

```text
root

x --> y
^     |
|-----|
```

Both `x` and `y` have incoming links, but neither is reachable from the root.
Committing this draft fails.

## 3. Commit gives a fixed snapshot

Each successful commit returns an immutable `GraphSnapshot`. Later draft
edits do not change that snapshot or any views made from it.

There is no implicit current snapshot or rollback operation. Keep the
snapshot returned by the commit you want to use.

The library provides creation and link addition only in this first version.
Deletion, persistence, and concurrent editing are not implemented.

## 4. Visibility

```text
root --> x --> child
  |
  |----> other
```

```python
local = snapshot.view(x)
visible_nodes = local.nodes
direct_children = local.children(x)

global_view = snapshot.view(snapshot.root)
combined = snapshot.view(x, y)
```

In the picture, `view(x)` includes `x` and `child`, not `root` or `other`.
`view(root)` includes every node.

Multiple arguments give the union of their outgoing descendants. Arguments
themselves are always included, even if they have no children.

`view()` without arguments raises `ValueError`. It does not silently supply
the root.

A local `GraphView` has no root property, graph-builder reference, mutation
method, or incoming-link query. Its `nodes` property lists only its visible
nodes. Calling `children()` for a node outside the view raises
`UnknownNodeError`, even if the caller happens to hold that node's handle.

You can take another view from an existing view, but it can only keep or
reduce access:

```python
narrower = local.view(y)
```

This works only if `y` is already visible in `local`.

## 5. Cycles

```text
root --> x --> child
         ^      |
         |------|
```

`view(x)` sees `x` and `child`. Traversal remembers visited nodes and finishes
without repeatedly following the cycle.

Trying to add `child --> root` raises `IncomingRootLinkError`. The existing
cycle between `x` and `child` remains valid.

Non-root nodes can still be widely connected. For example, adding a permitted
`child --> other` link makes `other` visible from `x` in a new snapshot. The
rule protects the root; it does not prevent broad access to other nodes.

Layer 0 does not impose acyclic containment or proof rules. A language or
checker built on top may impose its own rules for those relationships.

## 6. Node identity and links

A `Node` is an identity. Its `number` is only a graph-local aid for displaying
examples and errors. Two nodes with the same number are not necessarily the
same node. Nodes from different graphs cannot be mixed.

A node does not store a parent pointer, graph pointer, value, or language
type. Links belong to the graph, not to the node handle.

Links are directed and have no built-in meaning. Adding `x --> y` does not
add `y --> x`. Adding an existing link again has no additional effect; this
version is not a multigraph.

Unknown link endpoints are rejected before the draft is changed.

## 7. Computations use a view

The caller supplies the visible graph information to a host-language function:

```python
from layer0 import GraphView, Node

def directly_linked(view: GraphView, x: Node, y: Node) -> bool:
    return y in view.children(x)

answer = directly_linked(snapshot.view(x, y), x, y)
```

Layer 0 supplies the view. It does not define relation meanings, enforce that
an answer is true, or run the next layer's proof rules.

The view protects graph access through the normal API and holds fixed data.
It is not a security sandbox for arbitrary Python: a function could use
separately captured globals, inspect internals, perform I/O, or loop forever.
Trusted checking code must not use outside information. Termination and
language-specific validation still need their own rules.

## 8. Run the example and tests

Python 3.10 or newer is sufficient. No third-party packages are needed.

Run these commands from the repository root. The package keeps imports such
as `from layer0 import Graph` working.

```sh
python3 -m layer0.layer0_demo
python3 -m unittest -v layer0.test_layer0
python3 -m unittest -v
```

The example shows a failed commit, a repaired graph, local and global
visibility, rejection of a link into the root, and how a permitted new link
changes a new view but not an old snapshot.

The tests cover detached nodes and cycles, directed visibility, multiple
arguments, unknown nodes, immutable snapshots, and a chain of 5,000 links.
They also check all 512 possible directed graphs on three nodes, rejecting
incoming root links and comparing the remaining cases against an independently
computed reachability table.

This library is separate from the earlier typed-graph prototype. That
prototype still passes its entire graph to primitive checks; it has not yet
been moved onto this Layer 0 API.
