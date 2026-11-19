import unittest

from binding_demo import BETA_ARGUMENTS, definitions, example_graph
from relations import Call, Composite, DefinitionError, Node, ValidationError, Validator


class BindingTests(unittest.TestCase):
    def test_substitute_matching_reference(self) -> None:
        Validator(example_graph(), definitions()).require(
            "SubstituteReference", "ref_x", "x", "ref_z", "ref_z", "x"
        )

    def test_preserve_other_reference(self) -> None:
        Validator(example_graph(), definitions()).require(
            "SubstituteReference", "ref_y", "x", "ref_z", "ref_y", "y"
        )

    def test_reject_wrong_substitution_result(self) -> None:
        with self.assertRaisesRegex(ValidationError, "SameNode"):
            Validator(example_graph(), definitions()).require(
                "SubstituteReference", "ref_x", "x", "ref_z", "ref_y", "x"
            )

    def test_reject_forged_target_witness(self) -> None:
        with self.assertRaisesRegex(ValidationError, "ReferenceShape"):
            Validator(example_graph(), definitions()).require(
                "SubstituteReference", "ref_x", "x", "ref_z", "ref_x", "y"
            )

    def test_reference_target_must_be_a_binder(self) -> None:
        graph = example_graph()
        graph["bad"] = Node("reference", {"binder": "inner"})
        with self.assertRaisesRegex(ValidationError, "ReferenceShape"):
            Validator(graph, definitions()).require(
                "SubstituteReference", "bad", "x", "ref_z", "bad", "inner"
            )

    def test_substitute_under_binder(self) -> None:
        Validator(example_graph(), definitions()).require(
            "SubstituteUnderLambda",
            "inner", "x", "ref_z", "result", "y", "ref_x", "ref_z", "x", "z",
        )

    def test_substitution_stops_at_target_binder(self) -> None:
        graph = example_graph()
        graph["identity"] = Node("lambda", {"parameter": "x", "body": "ref_x"})
        Validator(graph, definitions()).require(
            "SubstituteUnderLambda",
            "identity", "x", "ref_z", "identity", "x", "ref_x", "ref_x", "x", "z",
        )

    def test_reject_substitution_through_target_binder(self) -> None:
        graph = example_graph()
        graph["identity"] = Node("lambda", {"parameter": "x", "body": "ref_x"})
        graph["wrong"] = Node("lambda", {"parameter": "x", "body": "ref_z"})
        with self.assertRaises(ValidationError):
            Validator(graph, definitions()).require(
                "SubstituteUnderLambda",
                "identity", "x", "ref_z", "wrong", "x", "ref_x", "ref_z", "x", "z",
            )

    def test_reject_capture(self) -> None:
        graph = example_graph()
        graph["captured"] = Node("lambda", {"parameter": "y", "body": "ref_y"})
        with self.assertRaisesRegex(ValidationError, r"DifferentNode\(y, y\)"):
            Validator(graph, definitions()).require(
                "SubstituteUnderLambda",
                "inner", "x", "ref_y", "captured", "y", "ref_x", "ref_y", "x", "y",
            )

    def test_no_capture_if_argument_is_not_inserted(self) -> None:
        graph = example_graph()
        graph["unchanged"] = Node("lambda", {"parameter": "y", "body": "ref_z"})
        Validator(graph, definitions()).require(
            "SubstituteUnderLambda",
            "unchanged", "x", "ref_y", "unchanged", "y", "ref_z", "ref_z", "z", "y",
        )

    def test_binder_identity_not_display_spelling(self) -> None:
        graph = example_graph()
        graph["outer_y"] = Node("binder")
        graph["outer_ref"] = Node("reference", {"binder": "outer_y"})
        graph["outer_result"] = Node(
            "lambda", {"parameter": "y", "body": "outer_ref"}
        )
        Validator(graph, definitions()).require(
            "SubstituteUnderLambda",
            "inner", "x", "outer_ref", "outer_result", "y",
            "ref_x", "outer_ref", "x", "outer_y",
        )

    def test_nested_beta_step(self) -> None:
        Validator(example_graph(), definitions()).require(
            "BetaUnderLambda", *BETA_ARGUMENTS
        )

    def test_beta_checks_application_argument_edge(self) -> None:
        graph = example_graph()
        graph["app"] = Node("application", {"function": "fn", "argument": "ref_y"})
        with self.assertRaisesRegex(ValidationError, "ApplicationShape"):
            Validator(graph, definitions()).require("BetaUnderLambda", *BETA_ARGUMENTS)

    def test_beta_checks_function_binder(self) -> None:
        graph = example_graph()
        graph["fn"] = Node("lambda", {"parameter": "z", "body": "inner"})
        with self.assertRaisesRegex(ValidationError, "LambdaShape"):
            Validator(graph, definitions()).require("BetaUnderLambda", *BETA_ARGUMENTS)

    def test_identity_beta_can_return_a_type_node(self) -> None:
        graph = example_graph()
        graph["Nat"] = Node("nat")
        graph["identity"] = Node("lambda", {"parameter": "x", "body": "ref_x"})
        graph["type_app"] = Node(
            "application", {"function": "identity", "argument": "Nat"}
        )
        Validator(graph, definitions()).require(
            "BetaReference", "type_app", "identity", "x", "ref_x", "Nat", "Nat", "x"
        )

    def test_identity_beta_can_return_a_value_node(self) -> None:
        graph = example_graph()
        graph["zero"] = Node("zero")
        graph["identity"] = Node("lambda", {"parameter": "x", "body": "ref_x"})
        graph["value_app"] = Node(
            "application", {"function": "identity", "argument": "zero"}
        )
        Validator(graph, definitions()).require(
            "BetaReference", "value_app", "identity", "x", "ref_x", "zero", "zero", "x"
        )

    def test_nested_body_is_outside_current_bounded_relation(self) -> None:
        graph = example_graph()
        graph["deeper"] = Node("lambda", {"parameter": "z", "body": "inner"})
        with self.assertRaisesRegex(ValidationError, "ReferenceShape"):
            Validator(graph, definitions()).require(
                "SubstituteUnderLambda",
                "deeper", "x", "ref_y", "deeper", "z", "inner", "inner", "x", "y",
            )

    def test_recursive_specification_is_an_engine_limit(self) -> None:
        rules = definitions()
        rules["RecursiveSubstitution"] = Composite(
            ("e", "x", "a", "r"),
            ((Call("RecursiveSubstitution", ("e", "x", "a", "r")),),),
        )
        with self.assertRaisesRegex(DefinitionError, "Recursive"):
            Validator(example_graph(), rules)

    def test_substitution_all_reference_combinations(self) -> None:
        validator = Validator(example_graph(), definitions())
        binders = ("x", "y", "z")
        references = ("ref_x", "ref_y", "ref_z")
        for target in binders:
            for replaced in binders:
                for argument in references:
                    for result in references:
                        expression = f"ref_{target}"
                        expected = argument if target == replaced else expression
                        with self.subTest(
                            target=target, replaced=replaced,
                            argument=argument, result=result,
                        ):
                            arguments = (
                                expression, replaced, argument, result, target
                            )
                            if result == expected:
                                validator.require("SubstituteReference", *arguments)
                            else:
                                with self.assertRaises(ValidationError):
                                    validator.require("SubstituteReference", *arguments)

    def test_substitution_all_bounded_lambda_combinations(self) -> None:
        rules = definitions()
        binders = ("x", "y", "z")
        for binder in binders:
            for body_target in binders:
                for arg_target in binders:
                    for result_target in binders:
                        graph = example_graph()
                        body = f"ref_{body_target}"
                        argument = f"ref_{arg_target}"
                        new_body = f"ref_{result_target}"
                        graph["source"] = Node(
                            "lambda", {"parameter": binder, "body": body}
                        )
                        graph["candidate"] = Node(
                            "lambda", {"parameter": binder, "body": new_body}
                        )
                        validator = Validator(graph, rules)
                        for result in ("source", "candidate"):
                            if binder == "x":
                                valid = result == "source" and new_body == body
                            else:
                                inserted = body_target == "x"
                                capture = inserted and arg_target == binder
                                expected = argument if inserted else body
                                actual = body if result == "source" else new_body
                                valid = (
                                    not capture
                                    and new_body == actual
                                    and actual == expected
                                )
                            with self.subTest(
                                binder=binder, body=body_target,
                                argument=arg_target, result_body=result_target,
                                result=result,
                            ):
                                arguments = (
                                    "source", "x", argument, result, binder,
                                    body, new_body, body_target, arg_target,
                                )
                                if valid:
                                    validator.require(
                                        "SubstituteUnderLambda", *arguments
                                    )
                                else:
                                    with self.assertRaises(ValidationError):
                                        validator.require(
                                            "SubstituteUnderLambda", *arguments
                                        )


if __name__ == "__main__":
    unittest.main()
