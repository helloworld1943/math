"""Generated graph/Lean comparisons for the implemented expression fragment."""

from __future__ import annotations

import argparse
import subprocess
from dataclasses import dataclass

from node import Node

from . import EncodingError, Program, Snapshot
from .lean_examples import Examples


@dataclass(frozen=True)
class Case:
    name: str
    expression: Node
    type: Node
    accepted: bool


def build_cases() -> tuple[Program, tuple[Case, ...]]:
    e = Examples()
    p = e.program
    cases: list[Case] = []

    def add(name: str, expression: Node, type_node: Node, accepted: bool) -> None:
        cases.append(Case(name, expression, type_node, accepted))

    for level in range(4):
        for target in range(5):
            add(
                f"universe_{level}_{target}", p.universe(level),
                p.universe(target), target == level + 1,
            )

    for depth in range(1, 6):
        for selected in range(depth):
            variables = e.variables(depth)
            bindings = tuple((variable, e.u1) for variable in variables)
            expression = e.lambdas(bindings, variables[selected])
            for correct in (False, True):
                supplied = e.forall(bindings, e.u1 if correct else e.u0)
                add(f"projection_{depth}_{selected}_{correct}", expression, supplied, correct)

    for count in range(1, 5):
        a = p.variable()
        ta = p.type_node(a)
        variables = e.variables(count)
        bindings = ((a, e.u0), *((variable, ta) for variable in variables))
        for selected, variable in enumerate(variables):
            expression = e.lambdas(bindings, variable)
            for correct in (False, True):
                add(
                    f"dependent_projection_{count}_{selected}_{correct}",
                    expression, e.forall(bindings, ta if correct else e.u0), correct,
                )

    for arity in range(1, 4):
        a, family, function = e.variables(3)
        xs, ys = e.variables(arity), e.variables(arity)
        ta = p.type_node(a)
        family_type = e.arrows(*(ta for _ in range(arity)), e.u0)
        indexes = e.variables(arity)
        function_type = e.forall(
            tuple((index, ta) for index in indexes),
            p.type_node(e.apply(family, *indexes)),
        )
        bindings = (
            (a, e.u0), (family, family_type), (function, function_type),
            *((variable, ta) for variable in (*xs, *ys)),
        )
        expression = e.lambdas(bindings, e.apply(function, *xs))
        for selection in range(1 << arity):
            targets = tuple(
                ys[i] if selection & (1 << i) else xs[i] for i in range(arity)
            )
            add(
                f"family_index_{arity}_{selection}", expression,
                e.forall(bindings, p.type_node(e.apply(family, *targets))),
                selection == 0,
            )

    for expanded in (False, True):
        for same_function in (False, True):
            a, family, f, g, value, x = e.variables(6)
            ta = p.type_node(a)
            function_type = e.arrows(ta, ta)
            target = f if same_function else g
            if expanded:
                target = p.lambda_(x, ta, e.apply(target, x))
            bindings = (
                (a, e.u0), (family, e.arrows(function_type, e.u0)),
                (f, function_type), (g, function_type),
                (value, p.type_node(e.apply(family, f))),
            )
            add(
                f"eta_{expanded}_{same_function}",
                e.lambdas(bindings, value),
                e.forall(bindings, p.type_node(e.apply(family, target))),
                same_function,
            )

    for chain_length in range(1, 6):
        a, x = e.variables(2)
        ta = p.type_node(a)
        body = x
        for _ in range(chain_length):
            y = p.variable()
            body = e.apply(p.lambda_(y, ta, y), body)
        bindings = ((a, e.u0), (x, ta))
        add(
            f"let_chain_{chain_length}", e.lambdas(bindings, body),
            e.forall(bindings, ta), True,
        )

    for field_level in range(3):
        for codomain_level in range(3):
            x = p.variable()
            expression = p.function_type(
                x, p.universe(field_level), p.universe(codomain_level)
            )
            expected = max(field_level, codomain_level) + 1
            add(
                f"pi_universe_{field_level}_{codomain_level}", expression,
                p.universe(expected), True,
            )
            add(
                f"pi_wrong_universe_{field_level}_{codomain_level}", expression,
                p.universe(expected - 1), False,
            )

    return p, tuple(cases)


def render_expression(
    snapshot: Snapshot, expression: Node, bound: tuple[Node, ...] = ()
) -> str:
    """Read graph roles directly; do not use the Python calculus or inferred type."""
    view = snapshot.view(expression)
    kind = view.kind(expression)
    fields = view.fields(expression)
    if kind == "Universe":
        return f"(Type {view.level(expression)})"
    if kind == "Variable":
        if expression not in bound:
            raise EncodingError("The Lean test exporter requires closed expressions")
        return f"v{bound.index(expression)}"
    if kind == "TypeNode":
        form = view.form(expression)
        if form == "variable":
            return render_expression(snapshot, fields["variable"], bound)
        if form == "application":
            return render_expression(snapshot, fields["expression"], bound)
        variable, domain, body = (
            fields[role] for role in ("variable", "domain", "codomain")
        )
        if variable in bound:
            raise EncodingError("A test expression reuses a nested binder identity")
        # Binder names remain stable when nested references to earlier binders occur.
        domain_text = render_expression(snapshot, domain, bound)
        body_text = render_expression(snapshot, body, (*bound, variable))
        return f"((v{len(bound)} : {domain_text}) → {body_text})"
    if kind == "Lambda":
        variable, domain, body = (
            fields[role] for role in ("variable", "domain", "body")
        )
        if variable in bound:
            raise EncodingError("A test expression reuses a nested binder identity")
        return (
            f"(fun (v{len(bound)} : {render_expression(snapshot, domain, bound)}) => "
            f"{render_expression(snapshot, body, (*bound, variable))})"
        )
    if kind == "Application":
        return (
            f"({render_expression(snapshot, fields['function'], bound)} "
            f"{render_expression(snapshot, fields['argument'], bound)})"
        )
    raise EncodingError(f"Unsupported test-export expression kind: {kind}")


def lean_source(snapshot: Snapshot, cases: tuple[Case, ...]) -> str:
    lines = ["namespace GeneratedLayer1Checks"]
    for case in cases:
        expression = render_expression(snapshot, case.expression)
        supplied = render_expression(snapshot, case.type)
        lines.append(f"-- {case.name}")
        if case.accepted:
            lines.append(f"example : {supplied} := {expression}")
        else:
            lines.extend((
                "example : True := by",
                "  fail_if_success",
                f"    have bad : {supplied} := {expression}",
                "  trivial",
            ))
    lines.append("end GeneratedLayer1Checks")
    return "\n".join(lines) + "\n"


def verify_python(p: Program, cases: tuple[Case, ...]) -> Snapshot:
    relations = [
        p.relation("HasType", case.expression, case.type) for case in cases
    ]
    snapshot = p.commit()
    for case, relation in zip(cases, relations):
        actual = snapshot.check(relation, max_steps=100_000)
        if actual != case.accepted:
            raise AssertionError(
                f"{case.name}: expected accepted={case.accepted}, got {actual}"
            )
    return snapshot


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", action="store_true", help="Also run installed Lean 4.35.0")
    args = parser.parse_args()
    p, cases = build_cases()
    snapshot = verify_python(p, cases)
    positives = sum(case.accepted for case in cases)
    print(
        f"Python agrees with {len(cases)} expected cases: "
        f"{positives} accepted, {len(cases) - positives} rejected."
    )
    if args.lean:
        result = subprocess.run(
            ["elan", "run", "leanprover/lean4:v4.35.0", "lean", "--stdin"],
            input=lean_source(snapshot, cases), text=True,
            capture_output=True, timeout=120,
        )
        if result.returncode:
            raise RuntimeError(f"Lean comparison failed:\n{result.stdout}\n{result.stderr}")
        print(f"Lean independently checked the same {len(cases)} acceptance/rejection assertions.")


if __name__ == "__main__":
    main()
