"""Run from the repository root with python3 -m layer1.composition_demo."""

from . import Program
from .lean_examples import Examples


def main() -> None:
    program = Program()
    u0, u1, u2 = (program.universe(i) for i in range(3))
    right = program.relation("HasType", u0, u1)
    wrong = program.relation("HasType", u0, u2)

    choice = program.any_of(u0, u1, u2, relations=(wrong, right))
    together = program.all_of(u0, u1, u2, relations=(right, choice))
    failing = program.all_of(u0, u1, u2, relations=(right, wrong))
    snapshot = program.commit()
    snapshot.require(choice)
    snapshot.require(together)
    assert not snapshot.check(failing)
    print("PASS: RelationOr(false, true) holds.")
    print("PASS: RelationAnd(true, child Relation with RelationOr) holds.")
    print("PASS: RelationAnd(true, false) fails.")

    view = snapshot.view(together)
    combination = view.fields(together)["decomposition"]
    assert view.kind(combination) == "RelationAnd"
    assert set(view.fields(together)) == {"inputs", "decomposition"}
    assert view.arguments(together) == (u0, u1, u2)
    assert view.operands(combination) == (right, choice)
    assert snapshot.root not in view.nodes
    print("GRAPH: Relation -> RelationAnd -> child Relations; inputs are explicit.")
    print("No All/Any parent kinds or redundant operator tags are stored.")

    examples = Examples()
    eta = examples.eta_conversion()
    relation = examples.program.relation("HasType", eta.expression, eta.type)
    examples.program.commit().require(relation)
    print("ETA: a value of D f also checks against D (fun x => f x).")
    print("BetaReduces still checks exactly one beta step.")


if __name__ == "__main__":
    main()
