"""A small typed-application graph checked without hidden logical variables."""

from collections.abc import Mapping

from relations import Call, Composite, Definition, Node, Primitive, Validator


def zero_type(graph: Mapping[str, Node], arguments: tuple[str, ...]) -> bool:
    expression, type_node = (graph[name] for name in arguments)
    return (
        expression.kind == "zero"
        and type_node.kind == "nat"
        and expression.edges.get("type") == arguments[1]
    )


def successor_type(graph: Mapping[str, Node], arguments: tuple[str, ...]) -> bool:
    expression, type_node = (graph[name] for name in arguments)
    domain = type_node.edges.get("domain")
    codomain = type_node.edges.get("codomain")
    return (
        expression.kind == "successor"
        and expression.edges.get("type") == arguments[1]
        and type_node.kind == "arrow"
        and domain is not None
        and codomain is not None
        and graph[domain].kind == "nat"
        and graph[codomain].kind == "nat"
    )


def definitions() -> dict[str, Definition]:
    return {
        "ApplicationShape": Primitive(
            ("p", "f", "a"),
            lambda g, v: g[v[0]].kind == "application"
            and g[v[0]].edges.get("function") == v[1]
            and g[v[0]].edges.get("argument") == v[2],
        ),
        "FunctionTypeShape": Primitive(
            ("F", "A", "B"),
            lambda g, v: g[v[0]].kind == "arrow"
            and g[v[0]].edges.get("domain") == v[1]
            and g[v[0]].edges.get("codomain") == v[2],
        ),
        "ZeroType": Primitive(("e", "T"), zero_type),
        "SuccessorType": Primitive(("e", "T"), successor_type),
        "HasType": Composite(
            ("e", "T"),
            (
                (Call("ZeroType", ("e", "T")),),
                (Call("SuccessorType", ("e", "T")),),
            ),
        ),
        "TypeAnnotation": Primitive(
            ("e", "T"), lambda g, v: g[v[0]].edges.get("type") == v[1]
        ),
        "SameNode": Primitive(("x", "y"), lambda g, v: v[0] == v[1]),
        "ValidApplication": Composite(
            ("p", "f", "a", "F", "A", "B", "T"),
            (
                (
                    Call("ApplicationShape", ("p", "f", "a")),
                    Call("FunctionTypeShape", ("F", "A", "B")),
                    Call("HasType", ("f", "F")),
                    Call("HasType", ("a", "A")),
                    Call("TypeAnnotation", ("p", "T")),
                    Call("SameNode", ("T", "B")),
                ),
            ),
        ),
    }


def example_graph() -> dict[str, Node]:
    return {
        "Nat": Node("nat"),
        "NatToNat": Node("arrow", {"domain": "Nat", "codomain": "Nat"}),
        "succ": Node("successor", {"type": "NatToNat"}),
        "zero": Node("zero", {"type": "Nat"}),
        "app": Node(
            "application", {"function": "succ", "argument": "zero", "type": "Nat"}
        ),
    }


APPLICATION_ARGUMENTS = ("app", "succ", "zero", "NatToNat", "Nat", "Nat", "Nat")


if __name__ == "__main__":
    validator = Validator(example_graph(), definitions())
    validator.require("ValidApplication", *APPLICATION_ARGUMENTS)
    print("VALID: Nat.succ zero : Nat")
    print("All application objects and intermediate types were supplied explicitly.")
