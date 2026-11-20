"""Run from the repository root with python3 -m layer1.demo."""

from . import Program, TypeCheckError


def main() -> None:
    program = Program()
    u0, u1, u2 = (program.universe(n) for n in range(3))
    a = program.variable()
    identity = program.lambda_(a, u1, a)
    identity_type = program.function_type(a, u1, u1)
    applied = program.apply(identity, u0)

    x = program.variable()
    ta = program.type_node(a)
    inner = program.lambda_(x, ta, x)
    inner_type = program.function_type(x, ta, ta)
    polymorphic = program.lambda_(a, u1, inner)
    polymorphic_type = program.function_type(a, u1, inner_type)
    specialized = program.apply(polymorphic, u0)
    expected_inner = program.lambda_(x, u0, x)
    expected_inner_type = program.function_type(x, u0, u0)
    computed_type = program.type_node(applied)
    y = program.variable()
    uses_computed_type = program.lambda_(y, computed_type, y)
    uses_computed_type_type = program.function_type(y, u0, u0)

    checks = [
        ("Universe stays primitive: U(0) : U(1)",
         program.relation("HasType", u0, u1)),
        ("Lambda: identity has its function-form TypeNode",
         program.relation("HasType", identity, identity_type)),
        ("Application: identity U(0) : U(1)",
         program.relation("HasType", applied, u1)),
        ("Beta step: identity U(0) reduces to U(0)",
         program.relation("BetaReduces", applied, u0)),
        ("Dependent function: lambda A. lambda x : A. x",
         program.relation("HasType", polymorphic, polymorphic_type)),
        ("Dependent application substitutes A in both domain and codomain",
         program.relation("HasType", specialized, expected_inner_type)),
        ("Dependent beta step substitutes the inner domain",
         program.relation("BetaReduces", specialized, expected_inner)),
        ("A TypeNode can describe an application computing a type",
         program.relation("HasType", uses_computed_type, uses_computed_type_type)),
    ]
    wrong = program.relation("HasType", applied, u2)
    snapshot = program.commit()
    assert snapshot.view(identity_type).kind(identity_type) == "TypeNode"
    for node in (identity_type, ta, computed_type):
        print(f"TYPE FORM: {snapshot.view(node).form(node)} (node {node.number})")
    assert snapshot.view(computed_type).fields(computed_type)["expression"] is applied
    for label, relation in checks:
        snapshot.require(relation)
        print(f"PASS: {label}")
    try:
        snapshot.require(wrong)
    except TypeCheckError as error:
        print(f"EXPECTED REJECTION: {error}")
    else:
        raise AssertionError("The wrong application result type was accepted")

    local = snapshot.view(applied)
    assert identity in local.nodes and u0 in local.nodes
    assert snapshot.root not in local.nodes and u2 not in local.nodes
    print("VISIBILITY: the application sees its function and argument, not the root.")


if __name__ == "__main__":
    main()
