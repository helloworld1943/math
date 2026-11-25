"""Ordered fixed-slot graphs with indexed outputs and source-slot inputs."""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from types import MappingProxyType


@dataclass(frozen=True, eq=False, slots=True)
class Node:
    """An identity with a permanent number and optional immutable byte value."""

    number: int
    value: bytes | None = None

    def __post_init__(self) -> None:
        if (
            isinstance(self.number, bool)
            or not isinstance(self.number, int)
            or self.number < 0
        ):
            raise ValueError("A node number must be a non-negative integer")
        if self.value is not None and not isinstance(self.value, bytes):
            raise TypeError("A node value must be immutable bytes or None")


@dataclass(frozen=True, slots=True)
class InputLink:
    """The source node ID and its output slot, not a new incoming number."""

    source_node_id: int
    output_link_number: int


class UnknownNodeError(ValueError):
    """A node does not belong to this graph or snapshot."""


class UnknownLinkError(ValueError):
    """An output slot does not exist on its source node."""


class DuplicateLinkError(ValueError):
    """Two outputs of one source would target the same nonempty node."""


class InvalidOutputCountError(ValueError):
    """A non-root node must have at least one output slot."""


class RootOutputLinkError(ValueError):
    """The foundation root cannot have output slots."""


class RootDeletionError(ValueError):
    """The designated root cannot be deleted."""


class UnboundOutputError(ValueError):
    """A non-root node's required output 0 has no target at commit."""

    def __init__(self, nodes: frozenset[Node]) -> None:
        self.nodes = nodes
        numbers = sorted(node.number for node in nodes)
        super().__init__(f"Output 0 has no target on nodes: {numbers}")


class InvalidNodePositionError(ValueError):
    """A creation position is invalid or root 0 is not first."""


class InvalidLinkOrderError(ValueError):
    """An output would point to its source or a later node."""

    def __init__(
        self,
        source: Node,
        number: int,
        target: Node,
        source_position: int,
        target_position: int,
    ) -> None:
        self.source = source
        self.number = number
        self.target = target
        self.source_position = source_position
        self.target_position = target_position
        super().__init__(
            f"Node {source.number} output {number} at position {source_position} "
            f"cannot target node {target.number} at position {target_position}; "
            "the target must be earlier"
        )


def _check_link_number(source: Node, number: int, count: int) -> None:
    if (
        isinstance(number, bool)
        or not isinstance(number, int)
        or not 0 <= number < count
    ):
        raise UnknownLinkError(
            f"Node {source.number} has no output slot numbered {number!r}"
        )


class _GraphQueries:
    __slots__ = ()

    def _read_links(self) -> Mapping[Node, Sequence[Node | None]]:
        raise NotImplementedError

    def _targets(self, node: Node) -> Sequence[Node | None]:
        links = self._read_links()
        if node not in links:
            raise UnknownNodeError(f"Node {node.number} does not belong to this graph")
        return links[node]

    @property
    def nodes(self) -> frozenset[Node]:
        return frozenset(self._read_links())

    @property
    def node_order(self) -> tuple[Node, ...]:
        return tuple(self._read_links())

    def position(self, node: Node) -> int:
        """Current array index, not the permanent node ID."""
        self._targets(node)
        return self.node_order.index(node)

    def get_output(self, node: Node, n: int) -> Node | None:
        """Read a fixed slot; None is an empty target, not a nonexistent slot."""
        targets = self._targets(node)
        _check_link_number(node, n, len(targets))
        return targets[n]

    def get_output_count(self, node: Node) -> int:
        """The fixed number of output slots, including empty ones."""
        return len(self._targets(node))

    def inputs(self, node: Node) -> list[InputLink]:
        """Incoming source-slot records, sorted by source ID and output number."""
        self._targets(node)
        links = self._read_links()
        return [
            InputLink(source.number, number)
            for source in sorted(links, key=lambda source: source.number)
            for number, target in enumerate(links[source])
            if target is node
        ]


@dataclass(frozen=True, slots=True)
class GraphSnapshot(_GraphQueries):
    """A fixed ordered graph with bound output 0 and optional later targets."""

    _links: Mapping[Node, Sequence[Node | None]]
    root: Node

    def __post_init__(self) -> None:
        if self.root not in self._links:
            raise UnknownNodeError(f"Node {self.root.number} is not in this graph")
        if self.root.number != 0:
            raise ValueError("The root must have node number 0")
        frozen: dict[Node, tuple[Node | None, ...]] = {}
        for node, targets in self._links.items():
            if not isinstance(targets, Sequence):
                raise TypeError("Output slots must be an ordered sequence")
            frozen[node] = tuple(targets)
        nodes = frozenset(frozen)
        positions = {node: position for position, node in enumerate(frozen)}
        if len({node.number for node in nodes}) != len(nodes):
            raise ValueError("Node numbers must be unique within a graph")
        if positions[self.root] != 0:
            raise InvalidNodePositionError("Root 0 must be first in node order")
        for source, targets in frozen.items():
            if source is self.root and targets:
                raise RootOutputLinkError("Root 0 must have no output slots")
            if source is not self.root and not targets:
                raise InvalidOutputCountError(
                    f"Node {source.number} must have at least one output slot"
                )
        unbound = frozenset(
            source
            for source, targets in frozen.items()
            if source is not self.root and targets[0] is None
        )
        if unbound:
            raise UnboundOutputError(unbound)
        for source, targets in frozen.items():
            bound = [target for target in targets if target is not None]
            distinct = frozenset(bound)
            if len(distinct) != len(bound):
                raise DuplicateLinkError(
                    f"Node {source.number} has duplicate links to the same target"
                )
            if not distinct <= nodes:
                raise UnknownNodeError("An output targets a node outside this graph")
            for number, target in enumerate(targets):
                if target is not None and positions[target] >= positions[source]:
                    raise InvalidLinkOrderError(
                        source, number, target, positions[source], positions[target]
                    )
        object.__setattr__(self, "_links", MappingProxyType(frozen))

    def _read_links(self) -> Mapping[Node, Sequence[Node | None]]:
        return self._links


class Graph(_GraphQueries):
    """A mutable ordered graph retaining only its latest successful snapshot."""

    def __init__(self) -> None:
        self._root = Node(0)
        self._links: dict[Node, list[Node | None]] = {self._root: []}
        self._next_number = 1
        self._snapshot: GraphSnapshot | None = None

    @property
    def root(self) -> Node:
        return self._root

    @property
    def snapshot(self) -> GraphSnapshot | None:
        return self._snapshot

    def _read_links(self) -> Mapping[Node, Sequence[Node | None]]:
        return self._links

    def create_node(
        self, output_count: int = 1, *, position: int | None = None,
        value: bytes | bytearray | None = None,
    ) -> Node:
        """Insert at birth, appending by default; existing nodes never move."""
        if (
            isinstance(output_count, bool)
            or not isinstance(output_count, int)
            or output_count < 1
        ):
            raise InvalidOutputCountError(
                "A non-root node needs a positive integer output count"
            )
        if position is None:
            position = len(self._links)
        if (
            isinstance(position, bool)
            or not isinstance(position, int)
            or not 1 <= position <= len(self._links)
        ):
            raise InvalidNodePositionError(
                f"Creation position must be an integer from 1 to {len(self._links)}"
            )
        if value is not None and not isinstance(value, (bytes, bytearray)):
            raise TypeError("A node value must be bytes, bytearray, or None")
        node = Node(self._next_number, bytes(value) if value is not None else None)
        targets: list[Node | None] = [None] * output_count
        if position == len(self._links):
            self._links[node] = targets
        else:
            ordered = list(self._links.items())
            ordered.insert(position, (node, targets))
            self._links = dict(ordered)
        self._next_number += 1
        return node

    def edit_link(self, source: Node, number: int, target: Node | None) -> None:
        """Retarget or clear an existing slot without resizing or renumbering."""
        targets = self._targets(source)
        _check_link_number(source, number, len(targets))
        if target is not None:
            self._targets(target)
            source_position = self.position(source)
            target_position = self.position(target)
            if target_position >= source_position:
                raise InvalidLinkOrderError(
                    source, number, target, source_position, target_position
                )
            if target in targets and targets[number] is not target:
                raise DuplicateLinkError(
                    f"Node {source.number} already has an output to node {target.number}"
                )
        self._links[source][number] = target

    def delete_node(self, node: Node) -> None:
        """Remove its owned slots; clear surviving outputs that targeted it."""
        self._targets(node)
        if node is self.root:
            raise RootDeletionError("The root cannot be deleted")
        del self._links[node]
        for targets in self._links.values():
            for number, target in enumerate(targets):
                if target is node:
                    targets[number] = None

    def commit(self) -> GraphSnapshot:
        """Require output 0; validate and preserve optional later output slots."""
        snapshot = GraphSnapshot(self._links, self.root)
        self._snapshot = snapshot
        return snapshot
