"""Quantified, Type-valued encodings, not primitive Lean Prop."""

from __future__ import annotations

from layer0 import Node

from .lean_examples import Example, Examples


class LogicExamples(Examples):
    def type_of(self, expression: Node) -> Node:
        return self.program.type_node(expression)

    def exists_type(self, a: Node, predicate: Node) -> Node:
        result, witness = self.variables(2)
        tr = self.type_of(result)
        handler = self.program.function_type(
            witness, a, self.arrows(self.type_of(self.apply(predicate, witness)), tr)
        )
        return self.program.function_type(
            result, self.u0, self.arrows(handler, tr)
        )

    def or_type(self, left: Node, right: Node) -> Node:
        result = self.program.variable()
        tr = self.type_of(result)
        return self.program.function_type(
            result, self.u0,
            self.arrows(self.arrows(left, tr), self.arrows(right, tr), tr),
        )

    def equality_type(self, a: Node, x: Node, y: Node) -> Node:
        predicate = self.program.variable()
        return self.program.function_type(
            predicate, self.arrows(a, self.u0),
            self.arrows(
                self.type_of(self.apply(predicate, x)),
                self.type_of(self.apply(predicate, y)),
            ),
        )

    def empty_type(self) -> Node:
        result = self.program.variable()
        return self.program.function_type(result, self.u0, self.type_of(result))

    def forall_reorder(self) -> Example:
        a, b, predicate, h, x, y, i, j = self.variables(8)
        ta, tb = self.type_of(a), self.type_of(b)
        old_order = self.forall(
            ((i, ta), (j, tb)), self.type_of(self.apply(predicate, i, j))
        )
        bindings = (
            (a, self.u0), (b, self.u0),
            (predicate, self.arrows(ta, tb, self.u0)), (h, old_order),
            (y, tb), (x, ta),
        )
        return Example(
            "forallReorder", self.lambdas(bindings, self.apply(h, x, y)),
            self.forall(bindings, self.type_of(self.apply(predicate, x, y))),
        )

    def exists_intro(self) -> Example:
        a, predicate, x, proof, result, handler, i = self.variables(7)
        ta, tr = self.type_of(a), self.type_of(result)
        outer = (
            (a, self.u0), (predicate, self.arrows(ta, self.u0)),
            (x, ta), (proof, self.type_of(self.apply(predicate, x))),
        )
        handler_type = self.program.function_type(
            i, ta, self.arrows(self.type_of(self.apply(predicate, i)), tr)
        )
        expression = self.lambdas(
            (*outer, (result, self.u0), (handler, handler_type)),
            self.apply(handler, x, proof),
        )
        return Example(
            "existsIntro", expression,
            self.forall(outer, self.exists_type(ta, predicate)),
        )

    def exists_elim(self) -> Example:
        a, predicate, value, result, handler, i = self.variables(6)
        ta, tr = self.type_of(a), self.type_of(result)
        handler_type = self.program.function_type(
            i, ta, self.arrows(self.type_of(self.apply(predicate, i)), tr)
        )
        bindings = (
            (a, self.u0), (predicate, self.arrows(ta, self.u0)),
            (value, self.exists_type(ta, predicate)), (result, self.u0),
            (handler, handler_type),
        )
        return Example(
            "existsElim", self.lambdas(bindings, self.apply(value, result, handler)),
            self.forall(bindings, tr),
        )

    def exists_witness(self) -> Example:
        a, predicate, value, x, proof = self.variables(5)
        ta = self.type_of(a)
        bindings = (
            (a, self.u0), (predicate, self.arrows(ta, self.u0)),
            (value, self.exists_type(ta, predicate)),
        )
        handler = self.lambdas(
            ((x, ta), (proof, self.type_of(self.apply(predicate, x)))), x
        )
        return Example(
            "existsWitness", self.lambdas(bindings, self.apply(value, a, handler)),
            self.forall(bindings, ta),
        )

    def exists_map(self) -> Example:
        a, pred_p, pred_q, transform, value, result, handler, x, proof, i, j = (
            self.variables(11)
        )
        ta, tr = self.type_of(a), self.type_of(result)
        transform_type = self.program.function_type(
            i, ta, self.arrows(
                self.type_of(self.apply(pred_p, i)),
                self.type_of(self.apply(pred_q, i)),
            ),
        )
        handler_type = self.program.function_type(
            j, ta, self.arrows(self.type_of(self.apply(pred_q, j)), tr)
        )
        outer = (
            (a, self.u0), (pred_p, self.arrows(ta, self.u0)),
            (pred_q, self.arrows(ta, self.u0)), (transform, transform_type),
            (value, self.exists_type(ta, pred_p)),
        )
        transformed_handler = self.lambdas(
            ((x, ta), (proof, self.type_of(self.apply(pred_p, x)))),
            self.apply(handler, x, self.apply(transform, x, proof)),
        )
        expression = self.lambdas(
            (*outer, (result, self.u0), (handler, handler_type)),
            self.apply(value, result, transformed_handler),
        )
        return Example(
            "existsMap", expression, self.forall(outer, self.exists_type(ta, pred_q))
        )

    def or_intro(self, left: bool) -> Example:
        p, q, proof, result, on_left, on_right = self.variables(6)
        tp, tq, tr = self.type_of(p), self.type_of(q), self.type_of(result)
        outer = ((p, self.u0), (q, self.u0), (proof, tp if left else tq))
        expression = self.lambdas(
            (
                *outer, (result, self.u0),
                (on_left, self.arrows(tp, tr)), (on_right, self.arrows(tq, tr)),
            ),
            self.apply(on_left if left else on_right, proof),
        )
        return Example(
            "orLeft" if left else "orRight", expression,
            self.forall(outer, self.or_type(tp, tq)),
        )

    def or_elim(self) -> Example:
        p, q, result, value, on_left, on_right = self.variables(6)
        tp, tq, tr = self.type_of(p), self.type_of(q), self.type_of(result)
        bindings = (
            (p, self.u0), (q, self.u0), (result, self.u0),
            (value, self.or_type(tp, tq)),
            (on_left, self.arrows(tp, tr)), (on_right, self.arrows(tq, tr)),
        )
        return Example(
            "orElim", self.lambdas(
                bindings, self.apply(value, result, on_left, on_right)
            ),
            self.forall(bindings, tr),
        )

    def equality_refl(self) -> Example:
        a, x, predicate, proof = self.variables(4)
        ta = self.type_of(a)
        outer = ((a, self.u0), (x, ta))
        expression = self.lambdas(
            (
                *outer, (predicate, self.arrows(ta, self.u0)),
                (proof, self.type_of(self.apply(predicate, x))),
            ),
            proof,
        )
        return Example(
            "equalityRefl", expression, self.forall(outer, self.equality_type(ta, x, x))
        )

    def equality_subst(self) -> Example:
        a, x, y, equality, predicate, proof = self.variables(6)
        ta = self.type_of(a)
        bindings = (
            (a, self.u0), (x, ta), (y, ta),
            (equality, self.equality_type(ta, x, y)),
            (predicate, self.arrows(ta, self.u0)),
            (proof, self.type_of(self.apply(predicate, x))),
        )
        return Example(
            "equalitySubst", self.lambdas(
                bindings, self.apply(equality, predicate, proof)
            ),
            self.forall(bindings, self.type_of(self.apply(predicate, y))),
        )

    def equality_symm(self) -> Example:
        a, x, y, equality, predicate, proof_y, z, proof_x = self.variables(8)
        ta = self.type_of(a)
        outer = (
            (a, self.u0), (x, ta), (y, ta),
            (equality, self.equality_type(ta, x, y)),
        )
        px = self.type_of(self.apply(predicate, x))
        reverse_predicate = self.program.lambda_(
            z, ta, self.arrows(self.type_of(self.apply(predicate, z)), px)
        )
        identity = self.program.lambda_(proof_x, px, proof_x)
        expression = self.lambdas(
            (
                *outer, (predicate, self.arrows(ta, self.u0)),
                (proof_y, self.type_of(self.apply(predicate, y))),
            ),
            self.apply(equality, reverse_predicate, identity, proof_y),
        )
        return Example(
            "equalitySymm", expression,
            self.forall(outer, self.equality_type(ta, y, x)),
        )

    def equality_trans(self) -> Example:
        a, x, y, z, xy, yz, predicate, proof = self.variables(8)
        ta = self.type_of(a)
        outer = (
            (a, self.u0), (x, ta), (y, ta), (z, ta),
            (xy, self.equality_type(ta, x, y)), (yz, self.equality_type(ta, y, z)),
        )
        expression = self.lambdas(
            (
                *outer, (predicate, self.arrows(ta, self.u0)),
                (proof, self.type_of(self.apply(predicate, x))),
            ),
            self.apply(yz, predicate, self.apply(xy, predicate, proof)),
        )
        return Example(
            "equalityTrans", expression,
            self.forall(outer, self.equality_type(ta, x, z)),
        )

    def false_elim(self) -> Example:
        empty, result = self.variables(2)
        bindings = ((empty, self.empty_type()), (result, self.u0))
        return Example(
            "falseElim", self.lambdas(bindings, self.apply(empty, result)),
            self.forall(bindings, self.type_of(result)),
        )

    def double_neg_intro(self) -> Example:
        p, proof, negate = self.variables(3)
        tp = self.type_of(p)
        bindings = (
            (p, self.u0), (proof, tp), (negate, self.arrows(tp, self.empty_type())),
        )
        return Example(
            "doubleNegIntro", self.lambdas(bindings, self.apply(negate, proof)),
            self.forall(bindings, self.empty_type()),
        )

    def proof_identity_sensitive(self) -> Example:
        p, first, second, family, value = self.variables(5)
        tp = self.type_of(p)
        bindings = (
            (p, self.u0), (first, tp), (second, tp),
            (family, self.arrows(tp, self.u0)),
            (value, self.type_of(self.apply(family, first))),
        )
        return Example(
            "proofIdentitySensitive", self.lambdas(bindings, value),
            self.forall(bindings, self.type_of(self.apply(family, second))),
        )

    def logical(self) -> tuple[Example, ...]:
        return (
            self.forall_reorder(), self.exists_intro(), self.exists_elim(),
            self.exists_witness(), self.exists_map(), self.or_intro(True),
            self.or_intro(False), self.or_elim(), self.equality_refl(),
            self.equality_subst(), self.equality_symm(), self.equality_trans(),
            self.false_elim(), self.double_neg_intro(),
        )


def main() -> None:
    examples = LogicExamples()
    checks = [
        (example.name, examples.program.relation("HasType", example.expression, example.type))
        for example in examples.logical()
    ]
    snapshot = examples.program.commit()
    for name, relation in checks:
        snapshot.require(relation)
        print(f"PASS: {name}")
    print("These Type-valued encodings are not Lean's primitive Prop/Exists/Or.")


if __name__ == "__main__":
    main()