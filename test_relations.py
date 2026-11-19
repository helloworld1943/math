import unittest

from demo import APPLICATION_ARGUMENTS, definitions, example_graph
from relations import (
    Call,
    Composite,
    DefinitionError,
    Node,
    Primitive,
    ValidationError,
    Validator,
)


class RelationTests(unittest.TestCase):
    def test_valid_application(self) -> None:
        Validator(example_graph(), definitions()).require(
            "ValidApplication", *APPLICATION_ARGUMENTS
        )

    def test_both_has_type_alternatives(self) -> None:
        validator = Validator(example_graph(), definitions())
        validator.require("HasType", "zero", "Nat")
        validator.require("HasType", "succ", "NatToNat")

    def test_wrong_argument_type(self) -> None:
        graph = example_graph()
        graph["app"] = Node(
            "application", {"function": "succ", "argument": "succ", "type": "Nat"}
        )
        with self.assertRaisesRegex(ValidationError, r"HasType\(succ, Nat\)"):
            Validator(graph, definitions()).require(
                "ValidApplication",
                "app", "succ", "succ", "NatToNat", "Nat", "Nat", "Nat",
            )

    def test_wrong_result_annotation(self) -> None:
        graph = example_graph()
        graph["app"] = Node(
            "application",
            {"function": "succ", "argument": "zero", "type": "NatToNat"},
        )
        with self.assertRaisesRegex(ValidationError, "SameNode"):
            Validator(graph, definitions()).require(
                "ValidApplication",
                "app", "succ", "zero", "NatToNat", "Nat", "Nat", "NatToNat",
            )

    def test_wrong_function_type_witness(self) -> None:
        with self.assertRaisesRegex(ValidationError, "FunctionTypeShape"):
            Validator(example_graph(), definitions()).require(
                "ValidApplication",
                "app", "succ", "zero", "NatToNat", "NatToNat", "Nat", "Nat",
            )

    def test_annotation_alone_is_not_typing_proof(self) -> None:
        graph = example_graph()
        graph["fake"] = Node("unknown", {"type": "Nat"})
        with self.assertRaisesRegex(ValidationError, "case 2"):
            Validator(graph, definitions()).require("HasType", "fake", "Nat")

    def test_hidden_parameter_rejected_at_definition_time(self) -> None:
        rules = definitions()
        rules["Hidden"] = Composite(
            ("x",), ((Call("SameNode", ("x", "d")),),)
        )
        with self.assertRaisesRegex(DefinitionError, "hidden parameters.*d"):
            Validator(example_graph(), rules)

    def test_exposing_parameter_makes_definition_valid(self) -> None:
        rules = definitions()
        rules["Explicit"] = Composite(
            ("x", "d"), ((Call("SameNode", ("x", "d")),),)
        )
        validator = Validator(example_graph(), rules)
        validator.require("Explicit", "Nat", "Nat")
        with self.assertRaises(ValidationError):
            validator.require("Explicit", "Nat", "zero")

    def test_unknown_relation(self) -> None:
        rules = definitions()
        rules["Bad"] = Composite(("x",), ((Call("Missing", ("x",)),),))
        with self.assertRaisesRegex(DefinitionError, "Unknown relation"):
            Validator(example_graph(), rules)

    def test_wrong_arity(self) -> None:
        rules = definitions()
        rules["Bad"] = Composite(("x",), ((Call("SameNode", ("x",)),),))
        with self.assertRaisesRegex(DefinitionError, "expected 2 arguments"):
            Validator(example_graph(), rules)

    def test_invalid_root_calls(self) -> None:
        validator = Validator(example_graph(), definitions())
        for relation, arguments, message in (
            ("Missing", ("Nat",), "Unknown relation"),
            ("SameNode", ("Nat",), "expected 2 arguments"),
            ("SameNode", ("Nat", "missing"), "Unknown argument node"),
        ):
            with self.subTest(relation=relation, arguments=arguments):
                with self.assertRaisesRegex(DefinitionError, message):
                    validator.require(relation, *arguments)

    def test_recursive_definitions_rejected(self) -> None:
        rules = definitions()
        rules["Loop"] = Composite(("x",), ((Call("Loop", ("x",)),),))
        with self.assertRaisesRegex(DefinitionError, "Recursive"):
            Validator(example_graph(), rules)

    def test_duplicate_parameters_rejected(self) -> None:
        with self.assertRaisesRegex(DefinitionError, "duplicate parameters"):
            Validator({}, {"Bad": Primitive(("x", "x"), lambda g, v: True)})

    def test_empty_cases_rejected(self) -> None:
        for cases in ((), ((),)):
            with self.subTest(cases=cases):
                with self.assertRaisesRegex(DefinitionError, "nonempty"):
                    Validator({}, {"Bad": Composite((), cases)})

    def test_dangling_edge_rejected(self) -> None:
        with self.assertRaisesRegex(DefinitionError, "unknown node"):
            Validator({"x": Node("reference", {"target": "missing"})}, {})

    def test_primitive_exceptions_propagate(self) -> None:
        def broken(graph: object, arguments: object) -> bool:
            raise RuntimeError("implementation bug")

        validator = Validator({}, {"Broken": Primitive((), broken)})
        with self.assertRaisesRegex(RuntimeError, "implementation bug"):
            validator.require("Broken")

    def test_primitive_must_return_boolean(self) -> None:
        validator = Validator(
            {}, {"Bad": Primitive((), lambda g, v: 1)}  # type: ignore[arg-type]
        )
        with self.assertRaisesRegex(TypeError, "must return bool"):
            validator.require("Bad")


if __name__ == "__main__":
    unittest.main()
