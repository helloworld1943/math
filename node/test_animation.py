"""Verify the standalone animation's examples against the public graph API."""

from __future__ import annotations

import json
import unittest
from dataclasses import FrozenInstanceError, asdict, dataclass, field
from html.parser import HTMLParser
from pathlib import Path
from typing import TypedDict

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
    test_layer0,
)


Step = list[str | int | None]


class Shape(TypedDict):
    nodes: dict[str, int]
    outputs: dict[str, list[str | None]]


class State(Shape):
    nextNumber: int


class FixtureOptions(TypedDict, total=False):
    base: str


class Fixture(FixtureOptions):
    steps: list[Step]
    state: State


class InputInfo(TypedDict):
    source_node_id: int
    output_link_number: int


class CaseOptions(TypedDict, total=False):
    error: str
    publishBefore: bool
    expectedNode: str | None
    expectedCount: int
    expectedInputs: list[InputInfo]
    querySlot: int


class Case(CaseOptions):
    id: str
    chapter: str
    title: str
    explanation: str
    before: str
    after: str
    steps: list[Step]
    result: str
    test: str


class SmallGraphs(TypedDict):
    valid: list[int]
    noOutputs: list[int]
    orderViolations: list[int]


class Payload(TypedDict):
    fixtures: dict[str, Fixture]
    cases: list[Case]
    smallGraphs: SmallGraphs


class _CaseDataParser(HTMLParser):
    def __init__(self) -> None:
        super().__init__()
        self.collecting = False
        self.found = 0
        self.parts: list[str] = []

    def handle_starttag(
        self, tag: str, attrs: list[tuple[str, str | None]]
    ) -> None:
        attributes = dict(attrs)
        if tag == "script" and attributes.get("id") == "case-data":
            if attributes.get("type") != "application/json":
                raise ValueError("Animation case data must be JSON")
            self.collecting = True
            self.found += 1

    def handle_data(self, data: str) -> None:
        if self.collecting:
            self.parts.append(data)

    def handle_endtag(self, tag: str) -> None:
        if tag == "script":
            self.collecting = False


@dataclass
class _Run:
    graph: Graph = field(default_factory=Graph)
    handles: dict[str, Node] = field(default_factory=dict)

    def __post_init__(self) -> None:
        self.handles["root"] = self.graph.root


def _name(value: str | int | None) -> str:
    if not isinstance(value, str):
        raise ValueError("An animation node name must be a string")
    return value


def _number(value: str | int | None) -> int:
    if not isinstance(value, int):
        raise ValueError("An animation number must be an integer")
    return value


def _apply(run: _Run, step: Step) -> Node | int | list[InputLink] | None:
    op = _name(step[0])
    graph, handles = run.graph, run.handles
    if op == "create":
        name = _name(step[1])
        if name in handles:
            raise ValueError(f"Repeated animation node name: {name}")
        handles[name] = graph.create_node(
            _number(step[2]), position=_number(step[3]) if len(step) > 3 else None
        )
    elif op == "edit":
        graph.edit_link(
            handles[_name(step[1])],
            _number(step[2]),
            None if step[3] is None else handles[_name(step[3])],
        )
    elif op == "delete":
        graph.delete_node(handles[_name(step[1])])
    elif op == "commit":
        graph.commit()
    elif op == "get":
        return graph.get_output(handles[_name(step[1])], _number(step[2]))
    elif op == "count":
        return graph.get_output_count(handles[_name(step[1])])
    elif op == "inputs":
        return graph.inputs(handles[_name(step[1])])
    elif op == "position":
        return graph.position(handles[_name(step[1])])
    elif op == "snapshot-get":
        if graph.snapshot is None:
            raise ValueError("The snapshot example must commit first")
        return graph.snapshot.get_output(handles[_name(step[1])], _number(step[2]))
    elif op == "move":
        getattr(graph, "move_node")(handles[_name(step[1])], _number(step[2]))
    elif op == "delete-slot":
        getattr(graph, "delete_link")(handles[_name(step[1])], _number(step[2]))
    elif op == "foreign":
        graph.edit_link(handles[_name(step[1])], _number(step[2]), Graph().root)
    elif op == "forged":
        graph.edit_link(
            handles[_name(step[1])],
            _number(step[2]),
            Node(handles[_name(step[3])].number),
        )
    elif op == "freeze-node":
        setattr(handles[_name(step[1])], "number", _number(step[2]))
    elif op == "freeze-snapshot":
        if graph.snapshot is None:
            raise ValueError("The snapshot example must commit first")
        setattr(graph.snapshot, "root", Node(99))
    else:
        raise ValueError(f"Unknown animation operation: {op}")
    return None


def _shape(reader: Graph | GraphSnapshot, handles: dict[str, Node]) -> Shape:
    aliases = {node: name for name, node in handles.items()}
    return {
        "nodes": {aliases[node]: node.number for node in reader.node_order},
        "outputs": {
            aliases[node]: [
                None if target is None else aliases[target]
                for target in (
                    reader.get_output(node, n)
                    for n in range(reader.get_output_count(node))
                )
            ]
            for node in reader.node_order
        },
    }


class NodeAnimationTests(unittest.TestCase):
    data: Payload
    errors: dict[str, type[Exception]] = {
        "AttributeError": AttributeError,
        "DuplicateLinkError": DuplicateLinkError,
        "FrozenInstanceError": FrozenInstanceError,
        "InvalidLinkOrderError": InvalidLinkOrderError,
        "InvalidNodePositionError": InvalidNodePositionError,
        "InvalidOutputCountError": InvalidOutputCountError,
        "RootDeletionError": RootDeletionError,
        "RootOutputLinkError": RootOutputLinkError,
        "UnboundOutputError": UnboundOutputError,
        "UnknownLinkError": UnknownLinkError,
        "UnknownNodeError": UnknownNodeError,
    }

    @classmethod
    def setUpClass(cls) -> None:
        parser = _CaseDataParser()
        parser.feed(Path(__file__).with_name("layer0_animation.html").read_text("utf-8"))
        if parser.found != 1:
            raise ValueError("The animation must have exactly one case-data block")
        cls.data = json.loads("".join(parser.parts))

    def _fixture(self, name: str, seen: frozenset[str] = frozenset()) -> _Run:
        if name in seen:
            raise ValueError("Cyclic animation fixture inheritance")
        fixture = self.data["fixtures"][name]
        run = self._fixture(fixture["base"], seen | {name}) if "base" in fixture else _Run()
        for step in fixture["steps"]:
            _apply(run, step)
        return run

    def _assert_queries(
        self, reader: Graph | GraphSnapshot, state: State, handles: dict[str, Node]
    ) -> None:
        self.assertEqual(_shape(reader, handles), {
            "nodes": state["nodes"], "outputs": state["outputs"]
        })
        self.assertEqual(
            [node.number for node in reader.node_order], list(state["nodes"].values())
        )
        for name, number in state["nodes"].items():
            expected = [
                InputLink(state["nodes"][source], n)
                for source in sorted(state["nodes"], key=lambda source: state["nodes"][source])
                for n, target in enumerate(state["outputs"][source])
                if target == name
            ]
            self.assertEqual(reader.inputs(handles[name]), expected)
            self.assertEqual(handles[name].number, number)

    def test_case_catalog_uses_the_minimal_api_and_real_library_tests(self) -> None:
        cases = self.data["cases"]
        ids = {case["id"] for case in cases}
        self.assertGreaterEqual(len(cases), 30)
        self.assertEqual(len(ids), len(cases))
        self.assertTrue({
            "get-empty", "count", "missing-slot", "inputs-root", "inputs-slot",
            "duplicate", "swap-clear", "swap-middle", "swap-finish",
            "delete-node", "snapshot-empty", "insert-target",
        } <= ids)
        allowed = {
            "create", "edit", "delete", "commit", "get", "count", "inputs",
            "snapshot-get", "position", "move", "delete-slot",
            "foreign", "forged", "freeze-node", "freeze-snapshot",
        }
        for case in cases:
            with self.subTest(case=case["id"]):
                self.assertIn(case["before"], self.data["fixtures"])
                self.assertIn(case["after"], self.data["fixtures"])
                self.assertTrue(hasattr(test_layer0.Layer0Tests, case["test"]))
                self.assertTrue(case["steps"])
                self.assertTrue(all(step[0] in allowed for step in case["steps"]))

    def test_fixture_commits_require_zero_and_preserve_optional_slots(self) -> None:
        for name, fixture in self.data["fixtures"].items():
            with self.subTest(fixture=name):
                run = self._fixture(name)
                self._assert_queries(run.graph, fixture["state"], run.handles)
                missing = frozenset(
                    run.handles[source]
                    for source, targets in fixture["state"]["outputs"].items()
                    if any(target is None for target in targets)
                )
                if missing:
                    with self.assertRaises(UnboundOutputError) as raised:
                        run.graph.commit()
                    self.assertEqual(raised.exception.nodes, missing)
                else:
                    self._assert_queries(run.graph.commit(), fixture["state"], run.handles)
                self.assertEqual(run.graph.create_node().number, fixture["state"]["nextNumber"])

    def test_case_operations_results_and_latest_snapshot_match_python(self) -> None:
        for case in self.data["cases"]:
            with self.subTest(case=case["id"]):
                run = self._fixture(case["before"])
                before = self.data["fixtures"][case["before"]]["state"]
                after = self.data["fixtures"][case["after"]]["state"]
                self._assert_queries(run.graph, before, run.handles)
                survivors = before["nodes"].keys() & after["nodes"].keys()
                self.assertEqual(
                    [name for name in before["nodes"] if name in survivors],
                    [name for name in after["nodes"] if name in survivors],
                )
                for name in survivors:
                    self.assertEqual(before["nodes"][name], after["nodes"][name])
                    self.assertEqual(len(before["outputs"][name]), len(after["outputs"][name]))
                if case.get("publishBefore"):
                    run.graph.commit()
                for step in case["steps"][:-1]:
                    _apply(run, step)
                result = None
                if "error" in case:
                    expected_error = self.errors[case["error"]]
                    with self.assertRaises(expected_error) as raised:
                        _apply(run, case["steps"][-1])
                    self.assertIs(type(raised.exception), expected_error)
                else:
                    result = _apply(run, case["steps"][-1])
                self._assert_queries(run.graph, after, run.handles)
                if "expectedNode" in case:
                    target = case["expectedNode"]
                    self.assertIs(result, None if target is None else run.handles[target])
                if "expectedCount" in case:
                    self.assertEqual(result, case["expectedCount"])
                if "expectedInputs" in case:
                    if not isinstance(result, list):
                        raise AssertionError("inputs must return a list of records")
                    self.assertEqual([asdict(record) for record in result], case["expectedInputs"])
                latest_state = before if case.get("publishBefore") else None
                for position, step in enumerate(case["steps"]):
                    if step[0] == "commit" and not (
                        "error" in case and position == len(case["steps"]) - 1
                    ):
                        latest_state = after
                if latest_state is None:
                    self.assertIsNone(run.graph.snapshot)
                else:
                    snapshot = run.graph.snapshot
                    if snapshot is None:
                        raise AssertionError("A successful commit must publish its snapshot")
                    self._assert_queries(snapshot, latest_state, run.handles)
                self.assertEqual(run.graph.create_node().number, after["nextNumber"])

    def test_swap_walkthrough_clears_the_old_slot_before_retargeting(self) -> None:
        cases = {case["id"]: case for case in self.data["cases"]}
        self.assertEqual(cases["duplicate"]["error"], "DuplicateLinkError")
        self.assertEqual(cases["swap-clear"]["steps"], [["edit", "b", 0, None], ["commit"]])
        self.assertEqual(cases["swap-clear"]["error"], "UnboundOutputError")
        self.assertEqual(cases["swap-middle"]["steps"], [["edit", "b", 1, "root"], ["commit"]])
        self.assertEqual(cases["swap-middle"]["error"], "UnboundOutputError")
        self.assertEqual(cases["swap-finish"]["steps"], [["edit", "b", 0, "a"], ["commit"]])

    def test_all_512_arrow_shape_verdicts_match_the_snapshot_constructor(self) -> None:
        valid = set(self.data["smallGraphs"]["valid"])
        zero_slots = set(self.data["smallGraphs"]["noOutputs"])
        bad_order = set(self.data["smallGraphs"]["orderViolations"])
        self.assertEqual((len(valid), len(zero_slots), len(bad_order)), (3, 15, 46))
        self.assertEqual(len(valid | zero_slots | bad_order), 64)
        for mask in range(512):
            with self.subTest(mask=mask):
                nodes = (Node(0), Node(1), Node(2))
                links = {
                    nodes[i]: tuple(nodes[j] for j in range(3) if mask & (1 << (3 * i + j)))
                    for i in range(3)
                }
                if mask in valid:
                    self.assertEqual(GraphSnapshot(links, nodes[0]).node_order, nodes)
                else:
                    expected = (
                        InvalidOutputCountError if mask in zero_slots
                        else InvalidLinkOrderError if mask in bad_order
                        else RootOutputLinkError
                    )
                    with self.assertRaises(expected):
                        GraphSnapshot(links, nodes[0])


if __name__ == "__main__":
    unittest.main()
