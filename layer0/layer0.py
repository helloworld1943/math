"""Rooted directed graphs, staged construction, and read-only visibility."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from types import MappingProxyType


@dataclass(frozen=True, eq=False, slots=True)
class Node:
    """An identity only; its number is a graph-local display aid."""

    number: int


class UnknownNodeError(ValueError):
    """A node does not belong to this graph or visible view."""


class IncomingRootLinkError(ValueError):
    """A directed link targets the designated root."""


class UnreachableNodesError(ValueError):
    """A candidate graph contains nodes unreachable from its root."""

    def __init__(self, nodes: frozenset[Node]) -> None:
        self.nodes = nodes
        numbers = sorted(node.number for node in nodes)
        super().__init__(f"Nodes unreachable from the root: {numbers}")


def _reachable(
    links: Mapping[Node, frozenset[Node]], starts: tuple[Node, ...]
) -> frozenset[Node]:
    for node in starts:
        if node not in links:
            raise UnknownNodeError(f"Node {node.number} is not in this graph or view")
    visited: set[Node] = set()
    pending = list(starts)
    while pending:
        node = pending.pop()
        if node not in visited:
            visited.add(node)
            pending.extend(links[node] - visited)
    return frozenset(visited)


@dataclass(frozen=True, slots=True)
class GraphView:
    """Only the supplied nodes and their outgoing links are exposed."""

    _links: Mapping[Node, frozenset[Node]]

    def __post_init__(self) -> None:
        frozen = {node: frozenset(children) for node, children in self._links.items()}
        nodes = frozenset(frozen)
        for children in frozen.values():
            if not children <= nodes:
                raise UnknownNodeError("An outgoing link targets a node outside the view")
        object.__setattr__(self, "_links", MappingProxyType(frozen))

    @property
    def nodes(self) -> frozenset[Node]:
        return frozenset(self._links)

    def children(self, node: Node) -> frozenset[Node]:
        if node not in self._links:
            raise UnknownNodeError(f"Node {node.number} is not visible in this view")
        return self._links[node]

    def view(self, *arguments: Node) -> GraphView:
        """Take an equal or narrower view; no root is supplied implicitly."""
        if not arguments:
            raise ValueError("A view requires at least one explicit argument node")
        visible = _reachable(self._links, arguments)
        return GraphView({node: self._links[node] for node in visible})


@dataclass(frozen=True, slots=True)
class GraphSnapshot(GraphView):
    """An immutable graph whose entry-only root reaches every node."""

    root: Node

    def __post_init__(self) -> None:
        GraphView.__post_init__(self)
        if any(self.root in children for children in self._links.values()):
            raise IncomingRootLinkError("The root cannot have incoming links")
        reachable = _reachable(self._links, (self.root,))
        missing = self.nodes - reachable
        if missing:
            raise UnreachableNodesError(missing)


class Graph:
    """A mutable draft. Call commit to validate and publish a snapshot."""

    def __init__(self) -> None:
        self._root = Node(0)
        self._links: dict[Node, set[Node]] = {self._root: set()}
        self._next_number = 1

    @property
    def root(self) -> Node:
        return self._root

    def create_node(self) -> Node:
        """Create a detached node; connect it before committing."""
        node = Node(self._next_number)
        self._next_number += 1
        self._links[node] = set()
        return node

    def add_link(self, source: Node, target: Node) -> None:
        """Add a directed link, never into the root. Duplicate links do nothing."""
        for node in (source, target):
            if node not in self._links:
                raise UnknownNodeError(f"Node {node.number} does not belong to this graph")
        if target is self.root:
            raise IncomingRootLinkError("The root cannot have incoming links")
        self._links[source].add(target)

    def commit(self) -> GraphSnapshot:
        """Validate the root rules and return a fixed, complete snapshot."""
        return GraphSnapshot(
            _links={node: frozenset(children) for node, children in self._links.items()},
            root=self._root,
        )
