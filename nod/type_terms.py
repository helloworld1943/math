"""Small immutable semantic types and static terms, independent of graph IDs."""

from __future__ import annotations

from dataclasses import dataclass, field, replace


@dataclass(frozen=True)
class Static:
    kind: str
    value: object = None
    children: tuple[Static, ...] = ()


@dataclass(frozen=True)
class DataType:
    name: str
    package: str = ""
    nominal: bool = False
    domain: DataType | None = None
    codomain: DataType | None = None
    binder: Static | None = None
    term: Static | None = None
    level: int | None = None
    label: str | None = field(default=None, compare=False, hash=False)

    def __str__(self) -> str:
        if self.name == "Void":
            return "no-result"
        if self.name == "Function0":
            return f"(() -> {self.codomain})"
        if self.domain is not None:
            domain = f"({self.binder.value[2]}:{self.domain})" if self.binder is not None else str(self.domain)
            return f"({domain} -> {self.codomain})"
        if self.name == "Sort":
            return f"Sort({self.level})"
        if self.name == "$type":
            return format_static(self.term)
        if self.name == "$generated":
            return self.label or format_static(self.term)
        return f"{self.package}.{self.name}" if self.package else self.name


def format_static(term: Static) -> str:
    if term.kind == "ref":
        return str(term.value[2])
    if term.kind == "field":
        return f"{format_static(term.children[0])}.{term.value}"
    if term.kind == "type":
        return str(term.value)
    if term.kind == "literal":
        return str(term.value).lower() if isinstance(term.value, bool) else str(term.value)
    if term.kind == "call":
        return f"{format_static(term.children[0])}({', '.join(format_static(arg) for arg in term.children[1:])})"
    if term.kind == "function":
        return str(term.value[2])
    if term.kind == "lambda":
        return "<pure lambda>"
    if term.kind == "record":
        return str(term.value)
    if term.kind == "proposition":
        fields = ", ".join(
            f"{field.value}={format_static(field.children[0])}" for field in term.children
        )
        package, _, name = term.value
        return f"{package + '.' if package else ''}{name}({fields})"
    if term.kind == "operator":
        operator = "-" if term.value == "nat-sub" else term.value
        return f"({f' {operator} '.join(format_static(arg) for arg in term.children)})"
    return f"<{term.kind}>"


def replace_static(term: Static, replacements: dict[Static, Static]) -> Static:
    if term in replacements:
        return replacements[term]
    if term.kind == "type":
        return Static("type", replace_type(term.value, replacements))
    children = tuple(replace_static(child, replacements) for child in term.children)
    return Static(term.kind, term.value, children)


def replace_type(kind: DataType, replacements: dict[Static, Static]) -> DataType:
    if kind.domain is not None:
        return replace(
            kind, domain=replace_type(kind.domain, replacements),
            codomain=replace_type(kind.codomain, replacements),
        )
    if kind.term is not None:
        return replace(kind, term=replace_static(kind.term, replacements))
    return kind


def references(term: Static) -> set[Static]:
    result = {term} if term.kind == "ref" else set()
    if term.kind == "type":
        return result | type_references(term.value)
    for child in term.children:
        result.update(references(child))
    if term.kind == "lambda":
        result.difference_update(term.value)
    return result


def type_references(kind: DataType) -> set[Static]:
    if kind.domain is not None:
        result = type_references(kind.domain) | type_references(kind.codomain)
        if kind.binder is not None:
            result.discard(kind.binder)
        return result
    return references(kind.term) if kind.term is not None else set()
