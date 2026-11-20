# Extra ideas: computation, visibility, the root, and cycles

These are the rules we agreed on after building the first examples in
[idea.md](../idea.md). Some are design choices that the Python prototype does
not enforce yet.

## 1. Computation behind a relation

We can define a relation in two ways:

1. Decompose it into simpler relations, using AND and OR.
2. Supply a checking computation in a host language, such as Python.

"Primitive" means we choose not to decompose the relation further in our
description. It does not mean the computation has no smaller steps.

A primitive relation check returns true or false. When we require the
relation, we mean that its result must be true. The result is not another
Boolean value in the target program.

An idealized Python program has the same computational power as a Turing
machine, given enough time and memory. We do not need to implement a Turing
machine: we can use Python to run these checks.

That does not guarantee that a check finishes. A timeout, an execution error,
or a computation that runs forever is not the same as a false result.

## 2. Visibility: arguments and all their children

Our choice is:

> A relation's computation may read its argument nodes and all nodes reachable
> from them by following outgoing links, through any number of steps.

Here "children" means targets of outgoing links. It does not mean only
syntax-tree children. A link to a declaration, type, or context also gives
access to that node and its outgoing descendants.

```text
R(x, y)

x --> a --> b
y --> c

p --> x
```

In this example, `x`, `y`, `a`, `b`, and `c` are visible. `p` is not visible
unless some outgoing path from the arguments also reaches it.

The computation may not follow an incoming link backward just because that
link exists. An explicit reverse link would make access possible.

The visible part includes all outgoing links of its nodes and their targets.
It does not include unrelated graph nodes, incoming-link lists, or a hidden
list of every node in the graph.

## 3. Why we choose this instead of whole-graph access

If every check could read the whole graph, changing an unrelated declaration
could change the result of `R(x, y)`.

With our rule:

> If a change leaves the visible part unchanged, it cannot change the result
> of a check that depends only on that part.

This makes dependencies easier to understand and control.

If a relation needs more information, we supply another argument or add an
appropriate link. For example:

```text
HasType(expression, suppliedType, context)
```

The context makes the needed declarations reachable.

Every variable in a composite definition must still be an outer parameter.
Reading a linked node inside a primitive does not introduce a new logical
variable in that composite definition. If the decomposition itself needs
another argument `d`, its outer interface must include `d`.

For predictable checking, the computation must not change the graph or use
unrelated external information such as the clock or randomness. We check
against a fixed graph, not one being changed during the check.

## 4. A root node for global checks

We designate a program-root node and require:

> The root has no incoming links. Every other node must be reachable from it
> through directed links.

These are ordinary graph links. The basic rule does not require a special
containment link or a particular node type along the path.

```text
programRoot
    |--> declaration A --> ...
    |--> declaration B --> ...
    |--> declaration C --> ...
```

Then local and global checks use the same visibility rule:

```text
R(x, y)
    reads the outgoing descendants of x and y

ValidProgram(programRoot)
    reads everything reachable from programRoot
```

Having a standard root does not mean every computation receives it silently.
The root must be an explicit argument for a computation to inspect it.

No node, including the root itself, may link to the root. This prevents a
local computation from gaining whole-program access by following a back-link
to the root.

An unreachable node violates this rule. Merely requiring every non-root node
to have an incoming link is not enough: a disconnected cycle could satisfy
that condition without being reachable from the root.

The root is a designated, entry-only starting point. Root reachability and
the ban on incoming root links are separate requirements.

Having an incoming link does not give a node access to its source. We do not
add reverse links automatically.

## 5. Visibility is not the target language's variable scope

Visibility controls what a checking computation can read.

The target language still needs rules deciding which declarations a variable
reference is allowed to use. Being able to inspect a declaration does not
automatically make a reference to it legal.

## 6. Cycles: do not ban them everywhere

Our goal is not only to express programs, but also to make it convenient to
convert real programs into graphs.

A program can have an acyclic description and still run a loop:

```text
While
    |--> condition
    |--> body
```

So cycles in the graph are not necessary for general computational power.
However, some program relationships are easier to represent with cycles.

For example, mutually recursive functions naturally give:

```text
even declaration
    --> body
    --> call
    --> refersTo odd declaration
                    --> body
                    --> call
                    --> refersTo even declaration
```

We could replace direct references with stored names or IDs to avoid the
cycle. But then we would need another way to resolve them. A stored name
does not itself grant visibility to its declaration.

For convenience, we allow direct reference links even when they create a
cycle.

## 7. Keep language-specific cycle rules outside the basic graph rules

The basic graph rules do not give links built-in meanings such as containment
or reference. They are directed links, and cycles between non-root nodes are
allowed.

Containment can instead be described by a node of type `Containment`, with
links to the objects it relates. Its meaning and checks belong to the language
we define on top of the graph, not to the basic graph structure.

A language may require its containment relationships to be acyclic while
allowing recursive references. Our current proof checker also requires finite,
acyclic proof dependencies: a proof step cannot justify itself by pointing
back to itself.

These are additional checks for those particular relationships. They do not
mean that every graph link must have one of those special kinds, or that the
whole graph must be acyclic.

## 8. Visibility through a cycle

```text
A --> B --> C --> A
```

Starting from any of these nodes makes all three visible, along with all their
outgoing descendants.

A traversal remembers which nodes it has visited. A cycle does not make the
visible set infinite in a finite graph.

But it does affect the visibility boundary: nodes in the same directed cycle
can all reach one another. We cannot isolate them from each other using only
this visibility rule.

Links into the global root are forbidden, so no cycle can include the root.
Other well-connected nodes may still give broad access to non-root information;
the root rule is not a general guarantee of narrow visibility.

Allowing a reference cycle does not mean accepting unrestricted recursion in
the target language. A Lean-like language still needs separate checks for
which recursive definitions are allowed and whether they terminate.

## 9. Dynamic programs

This graph describes the program; it does not predict every step of its
execution.

A loop can be represented by a loop node. A dynamically chosen function call
can contain the expression that computes its target. We do not need to know
every runtime target before execution.

This is why a blanket no-cycle rule is unnecessary, but allowing cycles is
not enough to model or validate every dynamic behavior either. The language
still needs typing and computation rules.

## 10. What the current prototype actually enforces

- Primitive checks currently receive the whole graph in
  [relations.py](../relations.py). All-children visibility is not enforced yet.
- The prototype expects primitives not to mutate the graph or depend on
  external state, but it does not sandbox arbitrary Python code.
- The new requirement that every node be reachable from a designated root is
  not enforced yet.
- The validator rejects cyclic relation-definition dependencies.
- The dependent checker in [dependent.py](../dependent.py) also rejects cyclic
  proof graphs before expanding them into finite relation checks.

To enforce the new visibility rule, primitives would need a graph-access
interface that exposes only their arguments and outgoing descendants.
Restricting that interface would control normal graph access; it would not
by itself make arbitrary untrusted Python code safe to execute.

The separate [Layer 0 library](./layer0.md) now provides staged construction,
rejection of incoming root links, root-reachability checks on commit, and
read-only outgoing-descendant views.
The earlier relation checker has not yet been migrated to use those views.