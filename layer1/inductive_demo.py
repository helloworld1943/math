"""Run from the repository root with python3 -m layer1.inductive_demo."""

from . import Program, TypeCheckError


def main() -> None:
    p = Program()
    u0 = p.universe(0)

    boolean = p.inductive("MyBool", u0)
    bool_type = p.type_node(boolean.identity)
    false = boolean.constructor("false", bool_type)
    true = boolean.constructor("true", bool_type)
    bool_definition = boolean.finish()

    natural = p.inductive("MyNat", u0)
    nat_type = p.type_node(natural.identity)
    zero = natural.constructor("zero", nat_type)
    n = p.variable()
    succ_type = p.function_type(n, nat_type, nat_type)
    succ = natural.constructor("succ", succ_type)
    nat_definition = natural.finish()
    one = p.apply(succ, zero)
    two = p.apply(succ, one)

    a = p.variable()
    box = p.inductive("Box", u0, parameters=((a, u0),))
    box_a = p.type_node(p.apply(box.identity, a))
    value = p.variable()
    mk = box.constructor(
        "mk", p.function_type(value, p.type_node(a), box_a)
    )
    box_definition = box.finish()
    box_bool = p.type_node(p.apply(box.identity, bool_type))
    boxed_true = p.apply(p.apply(mk, bool_type), true)

    checks = [
        ("Bool declaration", p.relation("ValidInductive", bool_definition)),
        ("Nat declaration", p.relation("ValidInductive", nat_definition)),
        ("Box declaration", p.relation("ValidInductive", box_definition)),
        ("false : MyBool", p.relation("HasType", false, bool_type)),
        ("true : MyBool", p.relation("HasType", true, bool_type)),
        ("succ : MyNat -> MyNat", p.relation("HasType", succ, succ_type)),
        ("succ (succ zero) : MyNat", p.relation("HasType", two, nat_type)),
        ("Box MyBool : U(0)", p.relation("HasType", box_bool, u0)),
        ("Box.mk MyBool true : Box MyBool", p.relation("HasType", boxed_true, box_bool)),
    ]
    wrong = p.relation("HasType", p.apply(succ, true), nat_type)
    snapshot = p.commit()
    for description, relation in checks:
        snapshot.require(relation, max_steps=100_000)
        print(f"PASS: {description}")
    try:
        snapshot.require(wrong, max_steps=100_000)
    except TypeCheckError as error:
        print(f"EXPECTED REJECTION: {error}")
    else:
        raise AssertionError("A Bool was accepted as a Nat constructor argument")
    view = snapshot.view(zero)
    assert snapshot.root not in view.nodes
    assert view.kind(zero) == "Variable"
    assert view.name(zero) == "zero"
    assert view.kind(view.fields(zero)["context"]) == "Context"
    print("GRAPH: constructors are Context-owned Variables, not Constructor nodes.")
    print("U(0) still uses the existing Type indexing; Prop migration is separate.")


if __name__ == "__main__":
    main()
