"""Temporary terms used by primitive checks, not a second program graph."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TypeAlias

from layer0 import Node


class TypeCheckError(ValueError):
    """A required typing or reduction relationship does not hold."""


class CheckLimitError(RuntimeError):
    """Checking exhausted its work budget; this is not a false relationship."""


@dataclass
class Work:
    remaining: int

    def __post_init__(self) -> None:
        if type(self.remaining) is not int or self.remaining <= 0:
            raise ValueError("max_steps must be a positive integer")

    def spend(self) -> None:
        self.remaining -= 1
        if self.remaining < 0:
            raise CheckLimitError("The relation check exceeded max_steps")


@dataclass(frozen=True)
class Universe:
    level: int


@dataclass(frozen=True)
class Bound:
    index: int


@dataclass(frozen=True)
class Constant:
    identity: Node
    type: Term


@dataclass(frozen=True)
class TypeNode:
    expression: Term


@dataclass(frozen=True)
class Lambda:
    domain: Term
    body: Term


@dataclass(frozen=True)
class Pi:
    domain: Term
    codomain: Term


@dataclass(frozen=True)
class Application:
    function: Term
    argument: Term


Term: TypeAlias = Universe | Bound | Constant | TypeNode | Lambda | Pi | Application


def shift(term: Term, amount: int, work: Work, cutoff: int = 0) -> Term:
    work.spend()
    if isinstance(term, (Universe, Constant)):
        return term
    if isinstance(term, Bound):
        return Bound(term.index + amount) if term.index >= cutoff else term
    if isinstance(term, TypeNode):
        return TypeNode(shift(term.expression, amount, work, cutoff))
    if isinstance(term, Lambda):
        return Lambda(
            shift(term.domain, amount, work, cutoff),
            shift(term.body, amount, work, cutoff + 1),
        )
    if isinstance(term, Pi):
        return Pi(
            shift(term.domain, amount, work, cutoff),
            shift(term.codomain, amount, work, cutoff + 1),
        )
    return Application(
        shift(term.function, amount, work, cutoff),
        shift(term.argument, amount, work, cutoff),
    )


def _replace(term: Term, argument: Term, work: Work, depth: int = 0) -> Term:
    work.spend()
    if isinstance(term, (Universe, Constant)):
        return term
    if isinstance(term, Bound):
        return shift(argument, depth, work) if term.index == depth else term
    if isinstance(term, TypeNode):
        return TypeNode(_replace(term.expression, argument, work, depth))
    if isinstance(term, Lambda):
        return Lambda(
            _replace(term.domain, argument, work, depth),
            _replace(term.body, argument, work, depth + 1),
        )
    if isinstance(term, Pi):
        return Pi(
            _replace(term.domain, argument, work, depth),
            _replace(term.codomain, argument, work, depth + 1),
        )
    return Application(
        _replace(term.function, argument, work, depth),
        _replace(term.argument, argument, work, depth),
    )


def instantiate(body: Term, argument: Term, work: Work) -> Term:
    """Remove one binder without capturing references beneath other binders."""
    raised = shift(argument, 1, work)
    return shift(_replace(body, raised, work), -1, work)


def normalize(term: Term, work: Work) -> Term:
    work.spend()
    if isinstance(term, (Universe, Bound, Constant)):
        return term
    if isinstance(term, TypeNode):
        return normalize(term.expression, work)
    if isinstance(term, Lambda):
        return Lambda(normalize(term.domain, work), normalize(term.body, work))
    if isinstance(term, Pi):
        return Pi(
            normalize(term.domain, work), normalize(term.codomain, work)
        )
    function = normalize(term.function, work)
    if isinstance(function, Lambda):
        return normalize(instantiate(function.body, term.argument, work), work)
    return Application(function, normalize(term.argument, work))


def _occurs(term: Term, work: Work, depth: int = 0) -> bool:
    """Does the binder being removed occur free in this subexpression?"""
    work.spend()
    if isinstance(term, (Universe, Constant)):
        return False
    if isinstance(term, Bound):
        return term.index == depth
    if isinstance(term, TypeNode):
        return _occurs(term.expression, work, depth)
    if isinstance(term, (Lambda, Pi)):
        body = term.body if isinstance(term, Lambda) else term.codomain
        return _occurs(term.domain, work, depth) or _occurs(body, work, depth + 1)
    return _occurs(term.function, work, depth) or _occurs(term.argument, work, depth)


def _eta_normal(term: Term, work: Work) -> Term:
    work.spend()
    if isinstance(term, (Universe, Bound, Constant)):
        return term
    if isinstance(term, TypeNode):
        return _eta_normal(term.expression, work)
    if isinstance(term, Lambda):
        domain = _eta_normal(term.domain, work)
        body = _eta_normal(term.body, work)
        if (
            isinstance(body, Application)
            and body.argument == Bound(0)
            and not _occurs(body.function, work)
        ):
            return shift(body.function, -1, work)
        return Lambda(domain, body)
    if isinstance(term, Pi):
        return Pi(
            _eta_normal(term.domain, work), _eta_normal(term.codomain, work)
        )
    return Application(
        _eta_normal(term.function, work), _eta_normal(term.argument, work)
    )


def definitionally_equal(left: Term, right: Term, work: Work) -> bool:
    return _eta_normal(normalize(left, work), work) == _eta_normal(
        normalize(right, work), work
    )


def infer(term: Term, environment: tuple[Term, ...], work: Work) -> Term:
    work.spend()
    if isinstance(term, Universe):
        return Universe(term.level + 1)
    if isinstance(term, Constant):
        return term.type
    if isinstance(term, Bound):
        if not 0 <= term.index < len(environment):
            raise TypeCheckError("A variable has no enclosing declaration")
        return shift(environment[term.index], term.index + 1, work)
    if isinstance(term, TypeNode):
        expression_type = infer(term.expression, environment, work)
        if not isinstance(normalize(expression_type, work), Universe):
            raise TypeCheckError("A TypeNode expression must have a Universe type")
        return expression_type
    if isinstance(term, (Lambda, Pi)):
        domain_sort = normalize(infer(term.domain, environment, work), work)
        if not isinstance(domain_sort, Universe):
            raise TypeCheckError("A function domain must itself have a Universe type")
        child_environment = (term.domain, *environment)
        if isinstance(term, Lambda):
            return Pi(
                term.domain, infer(term.body, child_environment, work)
            )
        body_sort = normalize(infer(term.codomain, child_environment, work), work)
        if not isinstance(body_sort, Universe):
            raise TypeCheckError("A function codomain must have a Universe type")
        return Universe(max(domain_sort.level, body_sort.level))

    function_type = normalize(infer(term.function, environment, work), work)
    if not isinstance(function_type, Pi):
        raise TypeCheckError("The function expression does not have a function type")
    argument_type = infer(term.argument, environment, work)
    if not definitionally_equal(argument_type, function_type.domain, work):
        raise TypeCheckError("The argument type does not match the function domain")
    return instantiate(function_type.codomain, term.argument, work)


def has_type(expression: Term, supplied_type: Term, work: Work) -> None:
    type_sort = normalize(infer(supplied_type, (), work), work)
    if not isinstance(type_sort, Universe):
        raise TypeCheckError("The supplied type must itself have a Universe type")
    actual_type = infer(expression, (), work)
    if not definitionally_equal(actual_type, supplied_type, work):
        raise TypeCheckError("The expression does not have the supplied type")


def _without_type_nodes(term: Term, work: Work) -> Term:
    """Unwrap type handles without evaluating any applications."""
    work.spend()
    if isinstance(term, (Universe, Bound, Constant)):
        return term
    if isinstance(term, TypeNode):
        return _without_type_nodes(term.expression, work)
    if isinstance(term, Lambda):
        return Lambda(
            _without_type_nodes(term.domain, work),
            _without_type_nodes(term.body, work),
        )
    if isinstance(term, Pi):
        return Pi(
            _without_type_nodes(term.domain, work),
            _without_type_nodes(term.codomain, work),
        )
    return Application(
        _without_type_nodes(term.function, work),
        _without_type_nodes(term.argument, work),
    )


def beta_reduces(expression: Term, supplied_result: Term, work: Work) -> None:
    expression = _without_type_nodes(expression, work)
    supplied_result = _without_type_nodes(supplied_result, work)
    if not isinstance(expression, Application) or not isinstance(
        expression.function, Lambda
    ):
        raise TypeCheckError("A beta step requires an Application of a Lambda")
    result = instantiate(expression.function.body, expression.argument, work)
    if result != supplied_result:
        raise TypeCheckError("The supplied result is not this single beta reduction")
