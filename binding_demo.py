"""Bounded substitution experiments with every witness passed explicitly."""

from demo import definitions as application_definitions
from relations import Call, Composite, Definition, Node, Primitive, Validator


def definitions() -> dict[str, Definition]:
    rules = application_definitions()
    rules.update(
        {
            "Binder": Primitive(("x",), lambda g, v: g[v[0]].kind == "binder"),
            "DifferentNode": Primitive(("x", "y"), lambda _g, v: v[0] != v[1]),
            "ReferenceShape": Primitive(
                ("e", "target"),
                lambda g, v: g[v[0]].kind == "reference"
                and g[v[0]].edges.get("binder") == v[1]
                and g[v[1]].kind == "binder",
            ),
            "LambdaShape": Primitive(
                ("e", "binder", "body"),
                lambda g, v: g[v[0]].kind == "lambda"
                and g[v[0]].edges.get("parameter") == v[1]
                and g[v[0]].edges.get("body") == v[2]
                and g[v[1]].kind == "binder",
            ),
            "SubstituteReference": Composite(
                ("e", "x", "a", "r", "target"),
                (
                    (
                        Call("Binder", ("x",)),
                        Call("ReferenceShape", ("e", "target")),
                        Call("SameNode", ("target", "x")),
                        Call("SameNode", ("r", "a")),
                    ),
                    (
                        Call("Binder", ("x",)),
                        Call("ReferenceShape", ("e", "target")),
                        Call("DifferentNode", ("target", "x")),
                        Call("SameNode", ("r", "e")),
                    ),
                ),
            ),
            "SubstituteUnderLambda": Composite(
                (
                    "e", "x", "a", "r", "binder", "body",
                    "new_body", "body_target", "arg_target",
                ),
                tuple(
                    (
                        Call("Binder", ("x",)),
                        Call("LambdaShape", ("e", "binder", "body")),
                        Call("LambdaShape", ("r", "binder", "new_body")),
                        Call("ReferenceShape", ("body", "body_target")),
                        Call("ReferenceShape", ("a", "arg_target")),
                    )
                    + case
                    for case in (
                        (
                            Call("SameNode", ("binder", "x")),
                            Call("SameNode", ("r", "e")),
                        ),
                        (
                            Call("DifferentNode", ("binder", "x")),
                            Call("SameNode", ("body_target", "x")),
                            Call("DifferentNode", ("arg_target", "binder")),
                            Call(
                                "SubstituteReference",
                                ("body", "x", "a", "new_body", "body_target"),
                            ),
                        ),
                        (
                            Call("DifferentNode", ("binder", "x")),
                            Call("DifferentNode", ("body_target", "x")),
                            Call(
                                "SubstituteReference",
                                ("body", "x", "a", "new_body", "body_target"),
                            ),
                        ),
                    )
                ),
            ),
            "BetaReference": Composite(
                ("p", "fn", "x", "body", "a", "r", "target"),
                (
                    (
                        Call("ApplicationShape", ("p", "fn", "a")),
                        Call("LambdaShape", ("fn", "x", "body")),
                        Call("SubstituteReference", ("body", "x", "a", "r", "target")),
                    ),
                ),
            ),
            "BetaUnderLambda": Composite(
                (
                    "p", "fn", "x", "e", "a", "r", "binder",
                    "body", "new_body", "body_target", "arg_target",
                ),
                (
                    (
                        Call("ApplicationShape", ("p", "fn", "a")),
                        Call("LambdaShape", ("fn", "x", "e")),
                        Call(
                            "SubstituteUnderLambda",
                            (
                                "e", "x", "a", "r", "binder", "body",
                                "new_body", "body_target", "arg_target",
                            ),
                        ),
                    ),
                ),
            ),
        }
    )
    return rules


def example_graph() -> dict[str, Node]:
    return {
        "x": Node("binder"),
        "y": Node("binder"),
        "z": Node("binder"),
        "ref_x": Node("reference", {"binder": "x"}),
        "ref_y": Node("reference", {"binder": "y"}),
        "ref_z": Node("reference", {"binder": "z"}),
        "inner": Node("lambda", {"parameter": "y", "body": "ref_x"}),
        "fn": Node("lambda", {"parameter": "x", "body": "inner"}),
        "app": Node("application", {"function": "fn", "argument": "ref_z"}),
        "result": Node("lambda", {"parameter": "y", "body": "ref_z"}),
    }


BETA_ARGUMENTS = (
    "app", "fn", "x", "inner", "ref_z", "result", "y",
    "ref_x", "ref_z", "x", "z",
)


if __name__ == "__main__":
    rules = definitions()
    validator = Validator(example_graph(), rules)
    validator.require("BetaUnderLambda", *BETA_ARGUMENTS)
    print("VALID: (lambda x. lambda y. x) z reduces to (lambda y. z)")
    for relation in ("SubstituteReference", "SubstituteUnderLambda", "BetaUnderLambda"):
        print(f"{relation}: {len(rules[relation].parameters)} explicit parameters")
