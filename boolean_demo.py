"""Build a function that returns a type or a function, selected by a Boolean."""

from __future__ import annotations

from dataclasses import dataclass

from dependent import Proof, check
from dependent_demo import Examples, Scope, Typed
from relations import Call, Node


@dataclass(frozen=True)
class MixedFunction:
    function: Typed
    identity: Typed
    identity_type: Typed


class BooleanExamples(Examples):
    def __init__(self) -> None:
        super().__init__()
        self.graph.update(
            {"Bool": Node("bool"), "true": Node("true"), "false": Node("false")}
        )

    def bool_type(self, scope: Scope) -> Typed:
        return Typed(
            "Bool", "U0", Proof("type_bool", (scope.name, "Bool", "U0"), (scope.proof,))
        )

    def boolean(self, scope: Scope, value: bool) -> Typed:
        name = "true" if value else "false"
        return Typed(
            name, "Bool",
            Proof(f"type_{name}", (scope.name, name, "Bool"), (scope.proof,)),
        )

    def weaken(self, value: Typed, parent: Scope, child: Scope) -> Typed:
        return Typed(
            value.term, value.type,
            Proof(
                "type_weaken",
                (
                    child.name, parent.name, child.binder,
                    child.type, value.term, value.type,
                ),
                (
                    child.proof, value.proof,
                    self.fresh(value.term, child.binder),
                    self.fresh(value.type, child.binder),
                ),
            ),
        )

    def fresh(self, term: str, binder: str) -> Proof:
        node = self.graph[term]
        if node.kind in ("bool", "true", "false"):
            return Proof(f"fresh_{node.kind}", (term, binder))
        if node.kind == "bool_elim":
            children = tuple(node.edges[key] for key in (
                "motive", "condition", "then_branch", "else_branch"
            ))
            return Proof(
                "fresh_bool_elim", (term, binder, *children),
                tuple(self.fresh(child, binder) for child in children),
            )
        return super().fresh(term, binder)

    def substitute(self, term: str, binder: str, argument: str) -> tuple[str, Proof]:
        node = self.graph[term]
        if node.kind in ("bool", "true", "false"):
            return term, Proof(f"subst_{node.kind}", (term, binder, argument, term))
        if node.kind == "bool_elim":
            labels = ("motive", "condition", "then_branch", "else_branch")
            children = tuple(node.edges[label] for label in labels)
            substitutions = tuple(
                self.substitute(child, binder, argument) for child in children
            )
            new_children = tuple(result for result, _ in substitutions)
            result = term
            if new_children != children:
                result = self.node("bool_elim", **dict(zip(labels, new_children)))
            return result, Proof(
                "subst_bool_elim",
                (term, binder, argument, result, *children, *new_children),
                tuple(proof for _, proof in substitutions),
            )
        return super().substitute(term, binder, argument)

    def normalize(self, term: str) -> tuple[str, Proof]:
        """Produce head-reduction evidence; this is not part of the checker."""
        node = self.graph[term]
        if node.kind == "application":
            function, argument = node.edges["function"], node.edges["argument"]
            head, head_proof = self.normalize(function)
            middle = term
            congruence = Proof("equal_refl", (term,))
            if head != function:
                middle = self.node("application", function=head, argument=argument)
                congruence = Proof(
                    "equal_app", (term, middle, function, argument, head, argument),
                    (head_proof, Proof("equal_refl", (argument,))),
                )
            head_node = self.graph[head]
            if head_node.kind != "lambda":
                return middle, congruence
            binder, domain, body = (
                head_node.edges[key] for key in ("binder", "domain", "body")
            )
            reduced, substitution = self.substitute(body, binder, argument)
            beta = Proof(
                "beta", (middle, head, binder, domain, body, argument, reduced),
                (substitution,),
            )
            result, tail = self.normalize(reduced)
            return result, Proof(
                "equal_trans", (term, middle, result),
                (
                    congruence,
                    Proof("equal_trans", (middle, reduced, result), (beta, tail)),
                ),
            )
        if node.kind == "bool_elim":
            motive, condition, yes, no = (
                node.edges[key] for key in (
                    "motive", "condition", "then_branch", "else_branch"
                )
            )
            head, condition_proof = self.normalize(condition)
            middle = term
            congruence = Proof("equal_refl", (term,))
            if head != condition:
                middle = self.node(
                    "bool_elim", motive=motive, condition=head,
                    then_branch=yes, else_branch=no,
                )
                congruence = Proof(
                    "equal_bool_elim",
                    (term, middle, motive, condition, yes, no, motive, head, yes, no),
                    (
                        Proof("equal_refl", (motive,)), condition_proof,
                        Proof("equal_refl", (yes,)), Proof("equal_refl", (no,)),
                    ),
                )
            kind = self.graph[head].kind
            if kind not in ("true", "false"):
                return middle, congruence
            selected = yes if kind == "true" else no
            step = Proof(f"reduce_{kind}", (middle, motive, head, yes, no))
            result, tail = self.normalize(selected)
            return result, Proof(
                "equal_trans", (term, middle, result),
                (
                    congruence,
                    Proof("equal_trans", (middle, selected, result), (step, tail)),
                ),
            )
        return term, Proof("equal_refl", (term,))

    def convert(self, scope: Scope, value: Typed, target: Typed) -> Typed:
        left, left_proof = self.normalize(value.type)
        right, right_proof = self.normalize(target.term)
        if left != right:
            raise ValueError(f"Example conversion needs equal heads: {left} != {right}")
        equality = Proof(
            "equal_trans", (value.type, left, target.term),
            (
                left_proof,
                Proof("equal_symm", (left, target.term), (right_proof,)),
            ),
        )
        return Typed(
            value.term, target.term,
            Proof(
                "type_convert",
                (scope.name, value.term, value.type, target.term, target.type),
                (value.proof, equality, target.proof),
            ),
        )

    def eliminate(
        self, scope: Scope, motive: Typed, condition: Typed,
        yes: Typed, no: Typed, yes_type: Typed, no_type: Typed, result_type: Typed,
    ) -> Typed:
        motive_type = self.graph[motive.type]
        binder, domain, universe = (
            motive_type.edges[key] for key in ("binder", "domain", "body")
        )
        term = self.node(
            "bool_elim", motive=motive.term, condition=condition.term,
            then_branch=yes.term, else_branch=no.term,
        )
        return Typed(
            term, result_type.term,
            Proof(
                "type_bool_elim",
                (
                    scope.name, term, motive.term, condition.term,
                    yes.term, no.term, motive.type, binder, domain, universe,
                    "true", "false", yes_type.term, no_type.term, result_type.term,
                ),
                (motive.proof, condition.proof, yes.proof, no.proof),
            ),
        )

    def constant_sort_motive(self, scope: Scope, level: int) -> Typed:
        domain = self.bool_type(scope)
        binder = self.node("binder")
        child = self.extend(scope, binder, domain)
        function_type = self.pi(
            scope, binder, domain, child, self.sort(child, level + 1)
        )
        return self.lam(
            scope, binder, domain, child, self.sort(child, level), function_type
        )

    def mixed_function(self) -> MixedFunction:
        scope = self.empty
        identity = self.identity(scope)
        identity_type = Typed(
            identity.type, identity.proof.arguments[-1], identity.proof.premises[0]
        )
        domain = self.bool_type(scope)

        family_binder = self.node("binder")
        family_scope = self.extend(scope, family_binder, domain)
        constant = self.constant_sort_motive(family_scope, 1)
        family_condition = self.reference(family_scope, family_binder)
        yes_type = self.app(
            family_scope, constant, self.boolean(family_scope, True)
        )
        no_type = self.app(
            family_scope, constant, self.boolean(family_scope, False)
        )
        result_type = self.app(family_scope, constant, family_condition)
        yes = self.convert(family_scope, self.sort(family_scope, 0), yes_type)
        no = self.convert(
            family_scope, self.weaken(identity_type, scope, family_scope), no_type
        )
        family_body = self.eliminate(
            family_scope, constant, family_condition, yes, no,
            yes_type, no_type, result_type,
        )
        family_body = self.convert(
            family_scope, family_body, self.sort(family_scope, 1)
        )
        family_type = self.pi(
            scope, family_binder, domain, family_scope, self.sort(family_scope, 1)
        )
        family = self.lam(
            scope, family_binder, domain, family_scope, family_body, family_type
        )

        binder = self.node("binder")
        child = self.extend(scope, binder, domain)
        motive = self.weaken(family, scope, child)
        condition = self.reference(child, binder)
        yes_type = self.app(child, motive, self.boolean(child, True))
        no_type = self.app(child, motive, self.boolean(child, False))
        result_type = self.app(child, motive, condition)
        yes = self.convert(child, self.bool_type(child), yes_type)
        no = self.convert(child, self.weaken(identity, scope, child), no_type)
        body = self.eliminate(
            child, motive, condition, yes, no, yes_type, no_type, result_type
        )
        function_type = self.pi(scope, binder, domain, child, result_type)
        function = self.lam(scope, binder, domain, child, body, function_type)
        return MixedFunction(function, identity, identity_type)


if __name__ == "__main__":
    examples = BooleanExamples()
    mixed = examples.mixed_function()
    for argument, target, label, expected_value in (
        (True, examples.sort(examples.empty, 0), "Sort 0 (a type)", "Bool"),
        (False, mixed.identity_type, "IdType (a function value)", mixed.identity.term),
    ):
        applied = examples.app(
            examples.empty, mixed.function, examples.boolean(examples.empty, argument)
        )
        converted = examples.convert(examples.empty, applied, target)
        checked = check(
            examples.graph, converted.proof,
            Call("Typing", ("empty", converted.term, converted.type)),
        )
        result, equality = examples.normalize(applied.term)
        if result != expected_value:
            raise AssertionError(f"Unexpected example result: {result}")
        check(examples.graph, equality, Call("Equal", (applied.term, expected_value)))
        print(f"VALID: F {argument} : {label}")
        print(
            f"  {checked.proof_steps} proof steps; "
            f"{checked.explicit_objects} explicit graph objects."
        )
