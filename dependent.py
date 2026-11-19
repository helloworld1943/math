"""A small dependent calculus checked through explicit finite proof graphs."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass

from relations import (
    Call,
    Composite,
    Definition,
    DefinitionError,
    Node,
    Primitive,
    ValidationError,
    Validator,
)


@dataclass(frozen=True)
class Rule:
    parameters: tuple[str, ...]
    conclusion: Call
    checks: tuple[Call, ...]
    premises: tuple[Call, ...]


@dataclass(frozen=True)
class Proof:
    rule: str
    arguments: tuple[str, ...]
    premises: tuple[Proof, ...] = ()


@dataclass(frozen=True)
class Checked:
    conclusion: Call
    proof_steps: int
    explicit_objects: int


def _call(text: str) -> Call:
    name, *arguments = text.split()
    return Call(name, tuple(arguments))


def _rule(
    parameters: str,
    conclusion: str,
    checks: tuple[str, ...],
    premises: tuple[str, ...] = (),
) -> Rule:
    result = Rule(
        tuple(parameters.split()),
        _call(conclusion),
        tuple(map(_call, checks)),
        tuple(map(_call, premises)),
    )
    if len(set(result.parameters)) != len(result.parameters):
        raise DefinitionError("Duplicate rule parameters")
    for call in (result.conclusion, *result.checks, *result.premises):
        hidden = set(call.arguments) - set(result.parameters)
        if hidden:
            raise DefinitionError(f"Hidden rule parameters: {sorted(hidden)}")
    return result


def _level(node: Node) -> int | None:
    prefix, separator, value = node.kind.partition(":")
    if prefix != "sort" or not separator or not value.isascii() or not value.isdecimal():
        return None
    return int(value)


def _primitives() -> dict[str, Definition]:
    def shape(kind: str, *labels: str) -> Primitive:
        return Primitive(
            ("node", *labels),
            lambda graph, values: graph[values[0]].kind == kind
            and all(
                graph[values[0]].edges.get(label) == value
                for label, value in zip(labels, values[1:])
            ),
        )

    def successor(graph: Mapping[str, Node], values: tuple[str, ...]) -> bool:
        lower, upper = (_level(graph[name]) for name in values)
        return lower is not None and upper is not None and upper == lower + 1

    def pi_universe(graph: Mapping[str, Node], values: tuple[str, ...]) -> bool:
        domain, body, result = (_level(graph[name]) for name in values)
        return (
            domain is not None
            and body is not None
            and result is not None
            and result == max(domain, body)
        )

    return {
        "Same": Primitive(("x", "y"), lambda _g, v: v[0] == v[1]),
        "Different": Primitive(("x", "y"), lambda _g, v: v[0] != v[1]),
        "Binder": shape("binder"),
        "Empty": shape("empty"),
        "Extend": shape("context", "parent", "binder", "type"),
        "Ref": shape("reference", "binder"),
        "App": shape("application", "function", "argument"),
        "Lam": shape("lambda", "binder", "domain", "body"),
        "Pi": shape("pi", "binder", "domain", "body"),
        "Bool": shape("bool"),
        "True": shape("true"),
        "False": shape("false"),
        "BoolElim": shape(
            "bool_elim", "motive", "condition", "then_branch", "else_branch"
        ),
        "Sort": Primitive(("u",), lambda g, v: _level(g[v[0]]) is not None),
        "ZeroUniverse": Primitive(("u",), lambda g, v: _level(g[v[0]]) == 0),
        "Successor": Primitive(("u", "v"), successor),
        "PiUniverse": Primitive(("u", "v", "w"), pi_universe),
    }


def _rules() -> dict[str, Rule]:
    rules = {
        "context_empty": _rule("c", "Context c", ("Empty c",)),
        "absent_empty": _rule("c x", "Absent c x", ("Empty c", "Binder x")),
        "absent_next": _rule(
            "c parent b A x", "Absent c x",
            ("Extend c parent b A", "Different b x"),
            ("Absent parent x",),
        ),
        "context_extend": _rule(
            "c parent x A u", "Context c",
            ("Extend c parent x A", "Binder x", "Sort u"),
            ("Context parent", "Absent parent x", "Typing parent A u"),
        ),
        "lookup_here": _rule(
            "c parent x A", "Lookup c x A", ("Extend c parent x A",),
        ),
        "lookup_next": _rule(
            "c parent b B x A", "Lookup c x A",
            ("Extend c parent b B", "Different b x"),
            ("Lookup parent x A",),
        ),
        "type_sort": _rule(
            "c e T", "Typing c e T", ("Successor e T",), ("Context c",),
        ),
        "type_ref": _rule(
            "c e x T", "Typing c e T", ("Ref e x",),
            ("Context c", "Lookup c x T"),
        ),
        "type_pi": _rule(
            "c e x A B child u v w", "Typing c e w",
            ("Pi e x A B", "Extend child c x A", "PiUniverse u v w"),
            ("Typing c A u", "Context child", "Typing child B v"),
        ),
        "type_lambda": _rule(
            "c e x A body T B child u", "Typing c e T",
            ("Lam e x A body", "Pi T x A B", "Extend child c x A", "Sort u"),
            ("Typing c T u", "Typing child body B"),
        ),
        "type_app": _rule(
            "c e f a F x A B T", "Typing c e T",
            ("App e f a", "Pi F x A B"),
            ("Typing c f F", "Typing c a A", "Substitute B x a T"),
        ),
        "type_convert": _rule(
            "c e S T u", "Typing c e T", ("Sort u",),
            ("Typing c e S", "Equal S T", "Typing c T u"),
        ),
        "type_weaken": _rule(
            "c parent x A e T", "Typing c e T",
            ("Extend c parent x A",),
            ("Context c", "Typing parent e T", "Fresh e x", "Fresh T x"),
        ),
        "type_bool": _rule(
            "c e u", "Typing c e u", ("Bool e", "ZeroUniverse u"),
            ("Context c",),
        ),
        "type_bool_elim": _rule(
            "c e motive cond t f M b B u yes no yesT noT resultT",
            "Typing c e resultT",
            (
                "BoolElim e motive cond t f", "Pi M b B u",
                "Bool B", "Sort u", "True yes", "False no",
                "App yesT motive yes", "App noT motive no",
                "App resultT motive cond",
            ),
            (
                "Typing c motive M", "Typing c cond B",
                "Typing c t yesT", "Typing c f noT",
            ),
        ),
        "subst_sort": _rule(
            "e x a r", "Substitute e x a r",
            ("Sort e", "Binder x", "Same e r"),
        ),
        "subst_hit": _rule(
            "e x a r", "Substitute e x a r",
            ("Ref e x", "Binder x", "Same a r"),
        ),
        "subst_miss": _rule(
            "e x a r b", "Substitute e x a r",
            ("Ref e b", "Binder x", "Different b x", "Same e r"),
        ),
        "subst_app": _rule(
            "e x a r f arg new_f new_arg", "Substitute e x a r",
            ("App e f arg", "App r new_f new_arg"),
            ("Substitute f x a new_f", "Substitute arg x a new_arg"),
        ),
        "subst_bool_elim": _rule(
            "e x a r m cond t f new_m new_cond new_t new_f",
            "Substitute e x a r",
            ("BoolElim e m cond t f", "BoolElim r new_m new_cond new_t new_f"),
            (
                "Substitute m x a new_m", "Substitute cond x a new_cond",
                "Substitute t x a new_t", "Substitute f x a new_f",
            ),
        ),
        "fresh_sort": _rule(
            "e x", "Fresh e x", ("Sort e", "Binder x"),
        ),
        "fresh_ref": _rule(
            "e x b", "Fresh e x", ("Ref e b", "Binder x", "Different b x"),
        ),
        "fresh_app": _rule(
            "e x f a", "Fresh e x", ("App e f a",),
            ("Fresh f x", "Fresh a x"),
        ),
        "fresh_bool_elim": _rule(
            "e x m cond t f", "Fresh e x", ("BoolElim e m cond t f",),
            ("Fresh m x", "Fresh cond x", "Fresh t x", "Fresh f x"),
        ),
        "beta": _rule(
            "e f x A body a r", "Equal e r",
            ("App e f a", "Lam f x A body"),
            ("Substitute body x a r",),
        ),
        "equal_refl": _rule("e", "Equal e e", ("Same e e",)),
        "equal_symm": _rule("e r", "Equal e r", (), ("Equal r e",)),
        "equal_trans": _rule(
            "e middle r", "Equal e r", (), ("Equal e middle", "Equal middle r"),
        ),
        "equal_app": _rule(
            "e r f a new_f new_a", "Equal e r",
            ("App e f a", "App r new_f new_a"),
            ("Equal f new_f", "Equal a new_a"),
        ),
        "equal_bool_elim": _rule(
            "e r m cond t f new_m new_cond new_t new_f", "Equal e r",
            ("BoolElim e m cond t f", "BoolElim r new_m new_cond new_t new_f"),
            (
                "Equal m new_m", "Equal cond new_cond",
                "Equal t new_t", "Equal f new_f",
            ),
        ),
    }
    for name, shape in (("bool", "Bool"), ("true", "True"), ("false", "False")):
        rules[f"subst_{name}"] = _rule(
            "e x a r", "Substitute e x a r",
            (f"{shape} e", "Binder x", "Same e r"),
        )
        rules[f"fresh_{name}"] = _rule(
            "e x", "Fresh e x", (f"{shape} e", "Binder x"),
        )
        if name != "bool":
            rules[f"type_{name}"] = _rule(
                "c e B", "Typing c e B", (f"{shape} e", "Bool B"),
                ("Context c",),
            )
            selected = "t" if name == "true" else "f"
            rules[f"reduce_{name}"] = _rule(
                "e m cond t f", f"Equal e {selected}",
                ("BoolElim e m cond t f", f"{shape} cond"),
            )
    for name, shape in (("lambda", "Lam"), ("pi", "Pi")):
        rules[f"subst_{name}"] = _rule(
            "e x a r b A body new_A new_body", "Substitute e x a r",
            (
                f"{shape} e b A body", f"{shape} r b new_A new_body",
                "Binder b", "Different b x",
            ),
            (
                "Fresh a b", "Substitute A x a new_A",
                "Substitute body x a new_body",
            ),
        )
        rules[f"subst_{name}_stop"] = _rule(
            "e x a r A body new_A", "Substitute e x a r",
            (f"{shape} e x A body", f"{shape} r x new_A body", "Binder x"),
            ("Substitute A x a new_A",),
        )
        rules[f"fresh_{name}"] = _rule(
            "e x b A body", "Fresh e x",
            (f"{shape} e b A body", "Binder b", "Different b x"),
            ("Fresh A x", "Fresh body x"),
        )
        rules[f"equal_{name}"] = _rule(
            "e r b A body new_A new_body", "Equal e r",
            (f"{shape} e b A body", f"{shape} r b new_A new_body"),
            ("Equal A new_A", "Equal body new_body"),
        )
    return rules


@dataclass(frozen=True)
class _Expanded:
    name: str
    arguments: tuple[str, ...]
    conclusion: Call


def check(graph: Mapping[str, Node], proof: Proof, expected: Call) -> Checked:
    """Check a supplied certificate; never infer a term, type, or missing proof."""
    rules = _rules()
    definitions = _primitives()
    active: set[int] = set()
    expanded: dict[int, _Expanded] = {}

    def expand(step: Proof) -> _Expanded:
        identity = id(step)
        if identity in active:
            raise DefinitionError("Cyclic proof graph")
        if identity in expanded:
            return expanded[identity]
        if step.rule not in rules:
            raise DefinitionError(f"Unknown proof rule {step.rule!r}")
        rule = rules[step.rule]
        if len(step.arguments) != len(rule.parameters):
            raise DefinitionError(f"{step.rule}: wrong number of explicit arguments")
        if len(step.premises) != len(rule.premises):
            raise DefinitionError(f"{step.rule}: wrong number of premises")
        bindings = dict(zip(rule.parameters, step.arguments))

        def instantiate(call: Call) -> Call:
            return Call(call.relation, tuple(bindings[arg] for arg in call.arguments))

        active.add(identity)
        children = tuple(expand(child) for child in step.premises)
        for requirement, child in zip(rule.premises, children):
            wanted = instantiate(requirement)
            if wanted != child.conclusion:
                raise ValidationError(
                    f"{step.rule}: premise mismatch: expected {wanted}, "
                    f"got {child.conclusion}"
                )
        arguments = tuple(
            dict.fromkeys(
                (*step.arguments, *(arg for child in children for arg in child.arguments))
            )
        )
        parameters = tuple(f"p{index}" for index in range(len(arguments)))
        names = dict(zip(arguments, parameters))
        checks = [instantiate(call) for call in rule.checks]
        checks.extend(Call(child.name, child.arguments) for child in children)
        name = f"Proof_{len(expanded)}_{step.rule}"
        definitions[name] = Composite(
            parameters,
            (tuple(Call(call.relation, tuple(names[a] for a in call.arguments))
                   for call in checks),),
        )
        result = _Expanded(name, arguments, instantiate(rule.conclusion))
        active.remove(identity)
        expanded[identity] = result
        return result

    root = expand(proof)
    if root.conclusion != expected:
        raise ValidationError(
            f"Conclusion mismatch: expected {expected}, got {root.conclusion}"
        )
    Validator(graph, definitions).require(root.name, *root.arguments)
    return Checked(root.conclusion, len(expanded), len(root.arguments))
