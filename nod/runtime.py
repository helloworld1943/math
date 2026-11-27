"""Checked nominal classes, explicit package visibility, and managed runtime values."""

from __future__ import annotations

import math
from dataclasses import dataclass, field

from node import Node
from .language import LanguageError, MAX_SOURCE, MAX_STEPS, Program, export_program, parse
from .type_terms import DataType, Static, format_static, references, replace_static, replace_type, type_references


BUILTINS = frozenset({"Nat", "Int", "Bool", "Float"})
NUMBERS = frozenset({"Nat", "Int", "Float"})
TYPE_NAMES = BUILTINS | {"Type", "Prop", "SortU"}


@dataclass
class Module:
    package: str
    program: Program
    imports: set[str]
    declarations: dict[str, Declaration] = field(default_factory=dict)
    types: dict[Node, DataType] = field(default_factory=dict)
    bindings: dict[Node, Node] = field(default_factory=dict)
    annotations: dict[Node, dict[str, object]] = field(default_factory=dict)


@dataclass
class Declaration:
    name: str
    module: Module
    node: Node
    public: bool
    kind: str
    type: DataType | None = None


@dataclass
class ClassSpec(Declaration):
    fields: dict[str, tuple[DataType, bool, Node]] = field(default_factory=dict)
    aliases: dict[str, tuple[DataType, bool, Node]] = field(default_factory=dict)
    const_fields: set[str] = field(default_factory=set)
    symbols: dict[str, Static] = field(default_factory=dict)
    constructors: list[Function] = field(default_factory=list)
    level: int = 1
    dependent: bool = False
    target: DataType | None = None
    target_source: Node | None = None
    resolved: bool = False
    resolving: bool = False
    synthetic: bool = False


@dataclass
class Function(Declaration):
    parameters: tuple[tuple[str, DataType, Node], ...] = ()
    body: Node | None = None
    receiver: ClassSpec | None = None
    constructor: ClassSpec | None = None
    owner: ClassSpec | None = None
    static: bool = False
    symbols: tuple[Static, ...] = ()
    static_body: Static | None = None
    resolving: bool = False
    checked: bool = False
    checking: bool = False
    field_values: dict[str, Static] = field(default_factory=dict)
    generator: bool = False
    schema_parameters: set[Static] = field(default_factory=set)
    contract: bool = False

    def call_name(self) -> str:
        name = self.name
        owner = self.receiver or self.constructor or self.owner
        if owner is not None:
            name = owner.name + ("." + name if name else "")
        return (self.module.package + "." if self.module.package else "") + name

    def signature(self) -> DataType:
        result = self.type
        if not self.parameters:
            return DataType("Function0", codomain=result)
        for (_, kind, _), symbol in reversed(tuple(zip(self.parameters, self.symbols))):
            result = DataType("Pi", domain=kind, codomain=result, binder=symbol)
        return result


@dataclass(eq=False)
class Instance:
    type: DataType
    fields: dict[str, Value]
    nil: bool = False
    constructing: bool = False
    layout: ClassSpec | None = None


@dataclass(frozen=True)
class Proposition:
    schema: ClassSpec
    fields: tuple[tuple[str, Static], ...]
    source: Node
    module: Module


@dataclass(eq=False)
class FunctionValue:
    function: Function
    receiver: Instance | None = None
    bound: tuple[Value, ...] = ()


Value = int | bool | float | Instance | DataType | FunctionValue | None


@dataclass(frozen=True)
class Access:
    name: str
    declaration: Declaration | None
    fields: tuple[str, ...] = ()


class Return(Exception):
    def __init__(self, value: Value) -> None:
        self.value = value


def descendant(child: str, parent: str) -> bool:
    return child == parent or bool(parent) and child.startswith(parent + ".")


class World:
    def __init__(self, entry: Program, sources: dict[str, str]) -> None:
        if not isinstance(sources, dict) or any(
            not isinstance(key, str) or not isinstance(value, str) for key, value in sources.items()
        ):
            raise LanguageError("input", "packages must map package names to source strings")
        if len(sources) > 32 or sum(len(source) for source in sources.values()) > MAX_SOURCE * 4:
            raise LanguageError("limit", "At most 32 package sources and 128000 package characters")
        self.modules: dict[str, Module] = {}
        self.entry = self.add_module(entry)
        for expected, source in sources.items():
            module = self.add_module(parse(source))
            if module.package != expected:
                raise LanguageError("package", f"Source '{expected}' must declare package {expected}")
        self.classes: dict[DataType, ClassSpec] = {}
        self.functions: list[Function] = []
        self.methods: dict[tuple[DataType, str], Function] = {}
        self.class_functions: dict[tuple[DataType, str], Function] = {}
        self.constructor_functions: dict[tuple[DataType, str], Function] = {}
        self.access: dict[tuple[str, Node], Access] = {}
        self.calls: dict[tuple[str, Node], Function | str] = {}
        self.literals: dict[tuple[str, Node], ClassSpec] = {}
        self.literal_defaults: dict[tuple[str, Node], dict[str, DataType]] = {}
        self.globals: dict[tuple[str, str], Value] = {}
        self.nil_objects: dict[DataType, Instance] = {}
        self.const_nodes: set[tuple[str, Node]] = set()
        self.alias_nodes: set[tuple[str, Node]] = set()
        self.parameter_nodes: set[tuple[str, Node]] = set()
        self.static_values: dict[Static, Static] = {}
        self.symbol_types: dict[Static, DataType] = {}
        self.type_values: dict[tuple[str, Node], DataType] = {}
        self.function_values: dict[tuple[str, Node], Function] = {}
        self.static_functions: dict[Static, Function] = {}
        self.active_constructor: Function | None = None
        self.initialized: dict[str, Static] = {}
        self.active_function: Function | None = None
        self.type_steps = 0
        self.proof_functions: dict[tuple[str, Node], Function] = {}
        self.resolving_variables: set[tuple[str, Node]] = set()
        self.interface_reads: list[set[Static]] = []
        self.runtime_bindings: list[dict[Static, Value]] = [{}]
        self.propositions: dict[DataType, Proposition] = {}
        self.generated_calls: dict[tuple[str, Node], DataType] = {}
        self.static_initializing: set[tuple[str, Node]] = set()
        self.declarations_registered = False
        self.output: list[str] = []
        self.steps = 0
        self.depth = 0

    def add_module(self, program: Program) -> Module:
        package, imports = "", set()
        for node in program.top():
            info = program.description(node)
            if info.kind == "package_decl":
                package = program.path(info.children[0])
            elif info.kind == "import_decl":
                name = program.path(info.children[0])
                if name in imports:
                    raise program.fail("package", node, f"Duplicate import '{name}'")
                imports.add(name)
        if package in self.modules:
            raise LanguageError("package", f"Duplicate package '{package}'")
        module = Module(package, program, imports)
        self.modules[package] = module
        return module

    def fail(self, module: Module, node: Node, message: str) -> LanguageError:
        return module.program.fail("type", node, f"{module.package + ': ' if module.package else ''}{message}")

    def visible(self, caller: Module, declaration: Declaration) -> bool:
        return descendant(caller.package, declaration.module.package) or (
            declaration.public and declaration.module.package in caller.imports
        )

    def parents(self, module: Module) -> list[str]:
        components = module.package.split(".")
        return [".".join(components[:n]) for n in range(len(components) - 1, 0, -1)]

    def resolve(self, module: Module, spelling: str, node: Node) -> Declaration:
        if "." in spelling:
            package, name = spelling.rsplit(".", 1)
            target = self.modules.get(package)
            declaration = target.declarations.get(name) if target else None
            if declaration is None:
                owner = self.resolve(module, package, node)
                if isinstance(owner, ClassSpec):
                    declaration = self.class_functions.get((owner.type, name))
            if declaration is None or not self.visible(module, declaration):
                raise self.fail(module, node, f"Inaccessible or unknown declaration '{spelling}' (import its exact package)")
            return declaration
        for package in [module.package, *self.parents(module)]:
            target = self.modules.get(package)
            if target and spelling in target.declarations:
                return target.declarations[spelling]
        candidates = [
            self.modules[package].declarations[spelling] for package in sorted(module.imports)
            if spelling in self.modules[package].declarations
            and self.modules[package].declarations[spelling].public
        ]
        if len(candidates) != 1:
            reason = "Ambiguous" if candidates else "Unknown or private"
            raise self.fail(module, node, f"{reason} name '{spelling}'")
        return candidates[0]

    def type_of(self, module: Module, node: Node) -> DataType:
        return self.elaborate_type(module, node, [])

    def variable_type(self, declaration: Declaration) -> DataType:
        if declaration.type is not None:
            return declaration.type
        key = declaration.module.package, declaration.node
        if key in self.resolving_variables:
            raise self.fail(declaration.module, declaration.node, "Cyclic dependency in a variable's declared type")
        self.resolving_variables.add(key)
        try:
            declaration.type = self.type_of(
                declaration.module, declaration.module.program.description(declaration.node).children[0],
            )
            self.symbol_types[self.symbol(declaration.module, declaration.node, declaration.name)] = declaration.type
            return declaration.type
        finally:
            self.resolving_variables.remove(key)

    def static_declaration(self, declaration: Declaration) -> None:
        """Resolve a const type description privately, never execute runtime code."""
        key = declaration.module.package, declaration.node
        symbol = self.symbol(declaration.module, declaration.node, declaration.name)
        if symbol in self.static_values:
            return
        if key not in self.const_nodes:
            raise self.fail(declaration.module, declaration.node, "A proposition/type used in a declaration must be const")
        if key in self.static_initializing:
            raise self.fail(declaration.module, declaration.node, "Cyclic construction of a type/proposition description")
        declared = self.variable_type(declaration)
        if declared.name not in ("Sort", "SortU"):
            return
        args = declaration.module.program.description(declaration.node).children
        if len(args) != 3:
            raise self.fail(declaration.module, declaration.node, "A type/proposition declaration requires an initializer")
        self.static_initializing.add(key)
        try:
            self.expression(declaration.module, args[2], [], declared)
            self.static_values[symbol] = self.static_value(declaration.module, args[2], [])
        finally:
            self.static_initializing.remove(key)

    def record_interface_read(self, term: Static) -> None:
        for collector in self.interface_reads:
            collector.update(references(term))

    def interface_type(self, module: Module, node: Node, scope, forbidden: set[Static]) -> DataType:
        observed: set[Static] = set()
        self.interface_reads.append(observed)
        try:
            result = self.elaborate_type(module, node, [scope])
        finally:
            self.interface_reads.pop()
        forbidden = forbidden | set().union(*(set(class_spec.symbols.values()) for class_spec in self.classes.values()))
        if (observed | type_references(result)) & forbidden or self.dependent_arrow(result):
            raise self.fail(module, node, "Function interfaces must be non-dependent; put this relationship in a class")
        return result

    def dependent_arrow(self, kind: DataType) -> bool:
        if kind.domain is None:
            return False
        return (
            kind.binder is not None and kind.binder in type_references(kind.codomain)
            or self.dependent_arrow(kind.domain) or self.dependent_arrow(kind.codomain)
        )

    def type_tick(self, module: Module, node: Node) -> None:
        self.type_steps += 1
        if self.type_steps > 30_000:
            raise self.fail(module, node, "Type-level checking exceeded its work budget")

    def symbol(self, module: Module, node: Node, name: str) -> Static:
        return Static("ref", (module.package, node, name))

    def function_symbol(self, function: Function) -> Static:
        symbol = Static("function", (function.module.package, function.node, function.name))
        self.static_functions[symbol] = function
        return symbol

    def native_type(self, name: str) -> DataType | None:
        if name in BUILTINS or name == "SortU":
            return DataType(name)
        if name == "Prop":
            return DataType("Sort", level=0)
        if name == "Type":
            return DataType("Sort", level=1)
        return None

    def declaration_node(self, module: Module, node: Node) -> tuple[Node, bool]:
        constant = False
        while module.program.description(node).kind == "const_declaration":
            constant = True
            node = module.program.description(node).children[0]
        return node, constant

    def normalize_static(self, module: Module, node: Node, term: Static, active=None) -> Static:
        self.type_tick(module, node)
        if active is None:
            active = set()
        if term in active:
            raise self.fail(module, node, "Cyclic type-level definition")
        if term.kind == "ref" and term not in self.static_values and self.declarations_registered:
            package, source, _ = term.value
            target = self.modules.get(package)
            declaration = next(
                (item for item in target.declarations.values() if item.node is source),
                None,
            ) if target is not None else None
            if declaration is not None and declaration.type is not None and declaration.type.name in ("Sort", "SortU"):
                self.static_declaration(declaration)
        if term in self.static_values:
            return self.normalize_static(module, node, self.static_values[term], active | {term})
        if term.kind == "type":
            return Static("type", self.normalize_type(module, node, term.value))
        if term.kind == "field":
            owner = self.normalize_static(module, node, term.children[0], active)
            if owner.kind == "type" and owner.value.name == "$generated":
                proposition = self.propositions[owner.value]
                field = next((value for name, value in proposition.fields if name == term.value), None)
                if field is None:
                    raise self.fail(module, node, f"Unknown proposition metadata field '{term.value}'")
                return self.normalize_static(module, node, field, active)
            if owner.kind == "record":
                for field_value in owner.children:
                    if field_value.value == term.value:
                        return self.normalize_static(module, node, field_value.children[0], active)
            return Static("field", term.value, (owner,))
        if term.kind == "function":
            function = self.static_functions[term]
            self.resolve_signature(function)
            if function.static_body is not None:
                self.check_function(function)
                return self.normalize_static(
                    module, node, Static("lambda", function.symbols, (function.static_body,)), active | {term},
                )
            return term
        children = tuple(self.normalize_static(module, node, child, active) for child in term.children)
        if term.kind == "call" and children[0].kind == "function":
            raise self.fail(module, node, "Type-level calls require a pure single-return type function")
        if term.kind == "call" and children[0].kind == "lambda":
            parameters = children[0].value
            arguments = children[1:]
            body = replace_static(children[0].children[0], dict(zip(parameters, arguments)))
            if len(arguments) < len(parameters):
                return Static("lambda", parameters[len(arguments):], (body,))
            if len(arguments) > len(parameters):
                body = Static("call", children=(body, *arguments[len(parameters):]))
            return self.normalize_static(module, node, body, active | {term, term.children[0]})
        if term.kind == "operator" and all(child.kind == "literal" for child in children):
            values = [child.value for child in children]
            operations = {
                "+": lambda: values[0] + values[1], "-": lambda: values[0] - values[1],
                "nat-sub": lambda: max(0, values[0] - values[1]),
                "*": lambda: values[0] * values[1], "!": lambda: not values[0],
                "neg": lambda: -values[0], "pos": lambda: +values[0],
            }
            if term.value in operations:
                result = operations[term.value]()
                if isinstance(result, int) and result.bit_length() > 100_000:
                    raise self.fail(module, node, "Type-level integer resource budget exceeded")
                return Static("literal", result)
        return Static(term.kind, term.value, children)

    def normalize_type(self, module: Module, node: Node, kind: DataType) -> DataType:
        self.type_tick(module, node)
        if kind.domain is not None:
            return DataType(
                "Pi", domain=self.normalize_type(module, node, kind.domain),
                codomain=self.normalize_type(module, node, kind.codomain), binder=kind.binder,
            )
        if kind.name == "$type":
            term = self.normalize_static(module, node, kind.term)
            if term.kind == "type":
                return term.value
            declared = self.static_reference_type(term)
            level = declared.level if declared is not None and declared.name == "Sort" else kind.level
            return DataType("$type", term=term, level=level)
        return kind

    def same_type(self, module: Module, node: Node, actual: DataType, expected: DataType) -> bool:
        actual, expected = self.normalize_type(module, node, actual), self.normalize_type(module, node, expected)
        if actual == expected:
            return True
        if actual.name == "$type" and expected.name == "$type" and actual.term == expected.term:
            # Universe-bound metadata is not a second identity for the same expression.
            return True
        if actual.name == "$generated" and expected.name == "$generated":
            return self.same_static(module, node, actual.term, expected.term)
        if actual.domain is not None and expected.domain is not None:
            if not self.same_type(module, node, actual.domain, expected.domain):
                return False
            substitutions = {}
            if actual.binder is not None and expected.binder is not None:
                substitutions[expected.binder] = actual.binder
            return self.same_type(module, node, actual.codomain, replace_type(expected.codomain, substitutions))
        return False

    def same_static(self, module: Module, node: Node, left: Static, right: Static) -> bool:
        self.type_tick(module, node)
        left, right = self.normalize_static(module, node, left), self.normalize_static(module, node, right)
        if left == right:
            return True
        if left.kind != right.kind or len(left.children) != len(right.children):
            return False
        if left.kind == "type":
            return self.same_type(module, node, left.value, right.value)
        if left.kind == "lambda":
            if len(left.value) != len(right.value):
                return False
            replacements = dict(zip(right.value, left.value))
            return all(
                self.same_static(module, node, a, replace_static(b, replacements))
                for a, b in zip(left.children, right.children)
            )
        if left.value != right.value:
            return False
        return all(self.same_static(module, node, a, b) for a, b in zip(left.children, right.children))

    def fits(self, module: Module, node: Node, actual: DataType, expected: DataType) -> bool:
        actual, expected = self.normalize_type(module, node, actual), self.normalize_type(module, node, expected)
        if expected.name == "SortU" and actual.name in ("Sort", "SortU"):
            return True
        return self.same_type(module, node, actual, expected)

    def universe_of(self, module: Module, node: Node, kind: DataType) -> int | None:
        kind = self.normalize_type(module, node, kind)
        if kind.name == "Sort":
            return kind.level + 1
        if kind.name == "SortU":
            return None
        if kind.nominal:
            return self.classes[kind].level
        if kind.domain is not None:
            domain = self.universe_of(module, node, kind.domain)
            codomain = self.universe_of(module, node, kind.codomain)
            return 0 if codomain == 0 else None if domain is None or codomain is None else max(domain, codomain)
        if kind.name == "$type":
            return kind.level
        if kind.name in BUILTINS or kind.name == "Void":
            return 1
        raise self.fail(module, node, f"Not a valid type: {kind}")

    def proof_type(self, module: Module, node: Node, kind: DataType) -> bool:
        kind = self.normalize_type(module, node, kind)
        if kind.domain is not None or kind.name == "Function0":
            return self.proof_type(module, node, kind.codomain)
        return (kind.nominal and self.classes[kind].level == 0) or (kind.name == "$type" and kind.level == 0)

    def elaborate_type(self, module: Module, node: Node, scopes) -> DataType:
        p = module.program
        node = p.type_node(node)
        args, kind = p.description(node).children, p.description(node).kind
        if kind in ("sort", "sort_type"):
            raw = p.text(args[0])
            if len(raw) > 256:
                raise self.fail(module, node, "Sort level is too large")
            return DataType("Sort", level=int(raw))
        if kind in ("variable", "named_type"):
            name = p.path(args[0])
            native = self.native_type(name)
            if native is not None:
                return native
            if not any(name.split(".")[0] in scope for scope in scopes):
                alias = self.alias_type(module, name, node)
                if alias is not None:
                    return alias
            if not any(name.split(".")[0] in scope for scope in scopes):
                declaration = None
                try:
                    declaration = self.resolve(module, name, node)
                except LanguageError:
                    pass
                if isinstance(declaration, ClassSpec):
                    self.resolve_class(declaration)
                    return declaration.target or declaration.type
        if kind == "arrow_type":
            domain_node, _, result_node = args
            left = p.type_node(domain_node)
            if p.description(left).kind == "annotation":
                name_node, domain_node = p.description(left).children
                name = self.path_expression(module, name_node)
                if name is None or "." in name:
                    raise self.fail(module, node, "Dependent arrow binder must be a simple name")
                if name in TYPE_NAMES or name == "this":
                    raise self.fail(module, node, "A type binder cannot shadow a native type name or this")
                binder_node = left
            else:
                name, binder_node = None, node
            domain = self.elaborate_type(module, domain_node, scopes)
            binder = self.symbol(module, binder_node, name) if name is not None else None
            if binder is not None:
                self.const_nodes.add((module.package, binder_node))
                self.symbol_types[binder] = domain
                scopes = [*scopes, {name: (domain, binder_node)}]
            result = self.elaborate_type(module, result_node, scopes)
            return DataType("Pi", domain=domain, codomain=result, binder=binder)
        actual = self.expression(module, node, scopes)
        actual = self.normalize_type(module, node, actual)
        if actual.name not in ("Sort", "SortU"):
            raise self.fail(module, node, f"A type expression must inhabit a Sort, got {actual}")
        term = self.static_value(module, node, scopes)
        normalized = self.normalize_static(module, node, term)
        return normalized.value if normalized.kind == "type" else DataType("$type", term=normalized, level=actual.level)

    def static_value(self, module: Module, node: Node, scopes) -> Static:
        p = module.program
        _, node = p.expression_layers(node)
        args, kind = p.description(node).children, p.description(node).kind
        if kind in ("integer", "boolean"):
            return Static("literal", int(p.text(args[0])) if kind == "integer" else p.text(args[0]) == "true")
        if (module.package, node) in self.type_values:
            return Static("type", self.type_values[module.package, node])
        if (module.package, node) in self.generated_calls:
            return Static("type", self.generated_calls[module.package, node])
        if (module.package, node) in self.function_values:
            return self.function_symbol(self.function_values[module.package, node])
        if kind in ("variable", "named_type"):
            name = p.path(args[0])
            native = self.native_type(name)
            if native is not None:
                return Static("type", native)
            metadata = self.proposition_projection(module, node, scopes)
            if metadata is not None:
                return metadata[1]
            path = name.split(".")
            for scope in reversed(scopes):
                if path[0] in scope:
                    value_type, declaration_node = scope[path[0]]
                    key = module.package, declaration_node
                    if key in self.parameter_nodes:
                        self.const_nodes.add(key)
                    if key not in self.const_nodes and key not in self.alias_nodes:
                        raise self.fail(module, node, f"Type dependency '{path[0]}' must be const")
                    result = self.symbol(module, declaration_node, path[0])
                    suffix = path[1:]
                    break
            else:
                for length in range(len(path), 0, -1):
                    try:
                        declaration = self.resolve(module, ".".join(path[:length]), node)
                    except LanguageError:
                        continue
                    if isinstance(declaration, ClassSpec):
                        return Static("type", declaration.type)
                    if isinstance(declaration, Function):
                        return self.function_symbol(declaration)
                    if (declaration.module.package, declaration.node) not in self.const_nodes:
                        raise self.fail(module, node, f"Type dependency '{declaration.name}' must be const")
                    value_type = self.variable_type(declaration)
                    result = self.symbol(declaration.module, declaration.node, declaration.name)
                    suffix = path[length:]
                    break
                else:
                    raise self.fail(module, node, f"Unknown static name '{name}'")
            for field_name in suffix:
                class_spec = self.classes.get(value_type)
                if class_spec is None or field_name not in class_spec.const_fields:
                    raise self.fail(module, node, f"Type dependency field '{field_name}' must be const through every alias")
                value_type = self.field_type(module, value_type, field_name, node, result)
                result = Static("field", field_name, (result,))
            self.record_interface_read(result)
            return result
        if kind in ("arrow_type", "sort", "sort_type"):
            return Static("type", self.elaborate_type(module, node, scopes))
        if kind == "member":
            owner = self.static_value(module, args[0], scopes)
            owner_type = self.expression(module, args[0], scopes)
            name = p.name(args[1])
            if name not in self.classes[owner_type].const_fields:
                raise self.fail(module, node, f"Type dependency field '{name}' must be const")
            return Static("field", name, (owner,))
        if kind == "call":
            function = self.calls.get((module.package, node))
            if isinstance(function, Function) and function.constructor is not None:
                self.check_function(function)
                needed = set()
                for name, value in function.field_values.items():
                    if name in function.constructor.const_fields:
                        needed |= references(value)
                replacements = {
                    symbol: self.static_value(module, argument, scopes)
                    for symbol, argument in zip(function.symbols, p.description(args[1]).children)
                    if symbol in needed
                }
                return Static(
                    "record", function.type,
                    (Static("identity", (module.package, node)),) +
                    tuple(Static("fieldvalue", name, (replace_static(value, replacements),))
                          for name, value in function.field_values.items()
                          if name in function.constructor.const_fields and value.kind != "unresolved-field"),
                )
            function = self.static_value(module, args[0], scopes)
            result_type = module.types.get(node)
            if result_type is not None and result_type.name not in ("Sort", "SortU"):
                reduced = self.normalize_static(module, node, function)
                if reduced.kind != "lambda":
                    raise self.fail(module, node, "A runtime callback cannot participate in a type-level dependency")
            arguments = tuple(self.static_value(module, arg, scopes) for arg in p.description(args[1]).children)
            return Static("call", children=(function, *arguments))
        if kind in ("unary", "binary"):
            operator = p.text(args[0 if kind == "unary" else 1])
            if kind == "unary":
                operator = {"-": "neg", "+": "pos"}.get(operator, operator)
                children = (self.static_value(module, args[1], scopes),)
            else:
                children = (self.static_value(module, args[0], scopes), self.static_value(module, args[2], scopes))
                if operator == "-" and module.types.get(node) == DataType("Nat"):
                    operator = "nat-sub"
            return Static("operator", operator, children)
        if kind == "class_literal":
            class_spec = self.literals[module.package, node]
            fields = [Static("identity", (module.package, node))]
            for initializer in p.description(args[1]).children:
                name_node, value = p.description(initializer).children
                name = p.name(name_node)
                if name in class_spec.const_fields:
                    fields.append(Static("fieldvalue", name, (self.static_value(module, value, scopes),)))
            return Static("record", class_spec.type, tuple(fields))
        raise self.fail(module, node, "This expression is not a stable type-level dependency")

    def can_capture_static(self, module: Module, node: Node, scopes) -> bool:
        """A const snapshot may be valid even when its precise value is unknown."""
        p = module.program
        _, node = p.expression_layers(node)
        args, kind = p.description(node).children, p.description(node).kind
        if kind in ("integer", "boolean") or (module.package, node) in self.type_values:
            return True
        if (module.package, node) in self.function_values:
            return True
        if kind == "variable":
            access = self.access.get((module.package, node))
            if access is None:
                return False
            if access.declaration is not None:
                key = access.declaration.module.package, access.declaration.node
            else:
                declaration = next((scope[access.name][1] for scope in reversed(scopes) if access.name in scope), None)
                if declaration is None:
                    return False
                key = module.package, declaration
            if key not in self.const_nodes:
                return False
            if access.fields:
                kind = self.variable_type(access.declaration) if access.declaration is not None else next(
                    scope[access.name][0] for scope in reversed(scopes) if access.name in scope
                )
                owner = Static("ref", (key[0], key[1], access.name))
                for name in access.fields:
                    kind = self.normalize_type(module, node, kind)
                    class_spec = self.classes.get(kind)
                    if class_spec is None or name not in class_spec.const_fields:
                        return False
                    kind = self.field_type(module, kind, name, node, owner)
                    owner = Static("field", name, (owner,))
            return True
        if kind == "class_literal":
            class_spec = self.literals[module.package, node]
            return all(
                self.can_capture_static(module, p.description(initializer).children[1], scopes)
                for initializer in p.description(args[1]).children
                if p.name(p.description(initializer).children[0]) in class_spec.const_fields
            )
        if kind == "call":
            function = self.calls.get((module.package, node))
            if isinstance(function, Function) and function.constructor:
                self.check_function(function)
                needed = set()
                for name, value in function.field_values.items():
                    if name in function.constructor.const_fields:
                        needed |= references(value)
                return all(
                    self.can_capture_static(module, argument, scopes)
                    for symbol, argument in zip(function.symbols, p.description(args[1]).children)
                    if symbol in needed
                )
            if function == "function-value":
                if not self.can_capture_static(module, args[0], scopes):
                    return False
                target = self.normalize_static(module, node, self.static_value(module, args[0], scopes))
                return target.kind == "lambda" and all(
                    self.can_capture_static(module, argument, scopes) for argument in p.description(args[1]).children
                )
            return isinstance(function, Function) and function.static_body is not None and all(
                self.can_capture_static(module, argument, scopes) for argument in p.description(args[1]).children
            )
        if kind == "unary":
            return self.can_capture_static(module, args[1], scopes)
        if kind == "binary":
            return self.can_capture_static(module, args[0], scopes) and self.can_capture_static(module, args[2], scopes)
        return False

    def records(self, module: Module):
        for node in module.program.items():
            public = module.program.description(node).kind == "public_item"
            if public:
                node = module.program.description(node).children[0]
            yield node, public

    def function_owner(self, function: Function) -> tuple[ClassSpec, str]:
        module, p = function.module, function.module.program
        path_node = p.description(function.node).children[0]
        spelling = p.path(path_node) if function.kind == "constructor" else function.name
        if function.kind == "constructor":
            package, _, name = spelling.rpartition(".")
            target = self.modules.get(package)
            exact = target.declarations.get(name) if target else None
            if "." not in spelling or isinstance(exact, ClassSpec):
                owner_name, name = spelling, ""
            else:
                owner_name, name = spelling.rsplit(".", 1)
        else:
            owner_name, name = spelling.rsplit(".", 1)
        owner = self.resolve(module, owner_name, path_node)
        if not isinstance(owner, ClassSpec) or owner.module is not module:
            label = "Constructors" if function.kind == "constructor" else "Functions/methods"
            raise self.fail(module, path_node, f"{label} must be declared in the class's package")
        return owner, name

    def initialize_definitions(self) -> list[Module]:
        for module in self.modules.values():
            for package in module.imports:
                if package not in self.modules:
                    raise LanguageError("package", f"{module.package}: missing exact import '{package}'")
                if package == module.package:
                    raise LanguageError("package", "A package cannot import itself")
            for node, public in self.records(module):
                info = module.program.description(node)
                static = info.kind == "static_function"
                if static:
                    module.annotations[node] = {"static": True}
                    node = info.children[0]
                    info = module.program.description(node)
                if info.kind == "class_decl":
                    name = module.program.name(info.children[0])
                    value = ClassSpec(name, module, node, public, "class", DataType(name, module.package, True))
                    for child in info.children[1:]:
                        annotation = module.program.description(child)
                        if annotation.kind == "class_sort_name":
                            spelling = module.program.path(annotation.children[0])
                            if spelling in ("Type", "Prop"):
                                value.level = 0 if spelling == "Prop" else 1
                            else:
                                if spelling in TYPE_NAMES:
                                    raise self.fail(module, child, "A class sort must be Type, Prop, Sort(n), or a generated proposition")
                                value.target_source = annotation.children[0]
                        elif annotation.kind == "class_sort_level":
                            value.level = int(module.program.text(annotation.children[0]))
                elif info.kind in ("function", "contract_function", "procedure", "constructor"):
                    if info.kind in ("function", "procedure"):
                        name = module.program.path(info.children[0])
                    elif info.kind == "constructor":
                        name = module.program.path(info.children[0])
                        self.functions.append(Function(name, module, node, public, "constructor"))
                        continue
                    else:
                        name = module.program.path(info.children[1])
                    if "." not in name:
                        raise self.fail(module, node, "Function declarations require a class owner; use static func Owner.name(...) ReturnType or an instance method")
                    self.functions.append(Function(name, module, node, public, "function", static=static,
                                                   contract=info.kind == "contract_function"))
                    continue
                else:
                    statement = module.program.description(info.children[0]) if info.kind == "statement" else info
                    if statement.kind == "const_declaration":
                        declaration_node, _ = self.declaration_node(module, info.children[0] if info.kind == "statement" else node)
                        statement = module.program.description(declaration_node)
                        self.const_nodes.add((module.package, declaration_node))
                    if statement.kind != "declaration":
                        continue
                    if info.kind == "statement":
                        node = info.children[0]
                    node, constant = self.declaration_node(module, node)
                    if constant:
                        self.const_nodes.add((module.package, node))
                    name = module.program.name(statement.children[1])
                    value = Declaration(name, module, node, public, "variable")
                if name in module.declarations or name in TYPE_NAMES or name == "this":
                    raise self.fail(module, node, f"Duplicate or reserved declaration '{name}'")
                module.declarations[name] = value
                if isinstance(value, ClassSpec):
                    self.classes[value.type] = value
        self.declarations_registered = True
        # Register ownership before resolving bodies/types that may generate P.
        for function in self.functions:
            owner, function.name = self.function_owner(function)
            if function.kind != "constructor":
                key = owner.type, function.name
                members = self.class_functions if function.static else self.methods
                if key in members:
                    raise self.fail(function.module, function.node, f"Duplicate member '{function.name}'")
                members[key] = function
                if function.static:
                    function.owner = owner
                else:
                    function.receiver = owner
                continue
            function.constructor = owner
            key = owner.type, function.name
            if key in self.constructor_functions:
                label = f"constructor '{function.name}'" if function.name else f"unnamed constructor for '{owner.type}'"
                raise self.fail(function.module, function.node, f"Duplicate {label}")
            self.constructor_functions[key] = function
            owner.constructors.append(function)
        for class_spec in tuple(self.classes.values()):
            self.resolve_class(class_spec)
        for module in self.modules.values():
            for declaration in module.declarations.values():
                if declaration.kind == "variable":
                    self.variable_type(declaration)
        for function in self.functions:
            self.resolve_signature(function)
        order, active, done = [], set(), set()
        def visit(module):
            if module.package in active:
                raise LanguageError("package", f"Cyclic package dependency at '{module.package}'")
            if module.package in done:
                return
            active.add(module.package)
            for dependency in sorted(module.imports | set(self.parents(module)) & self.modules.keys()):
                visit(self.modules[dependency])
            active.remove(module.package)
            done.add(module.package)
            order.append(module)
        for module in self.modules.values():
            visit(module)
        return order

    def resolve_class(self, class_spec: ClassSpec) -> None:
        if class_spec.resolved or class_spec.synthetic:
            return
        if class_spec.resolving:
            if class_spec.target_source is not None:
                raise self.fail(class_spec.module, class_spec.node, "Cyclic evidence specification target")
            return
        class_spec.resolving = True
        try:
            if class_spec.target_source is not None:
                spelling = class_spec.module.program.path(class_spec.target_source)
                target = self.resolve(class_spec.module, spelling, class_spec.target_source)
                if target.kind != "variable":
                    raise self.fail(class_spec.module, class_spec.target_source, "Evidence target must name a particular generated proposition")
                self.static_declaration(target)
                term = self.normalize_static(
                    class_spec.module, class_spec.target_source, self.symbol(target.module, target.node, target.name),
                )
                if term.kind != "type" or term.value.name != "$generated":
                    raise self.fail(class_spec.module, class_spec.target_source, "A class annotation must be a universe or a generated proposition target")
                proposition = self.propositions[term.value]
                if proposition.schema.module is not class_spec.module:
                    raise self.fail(class_spec.module, class_spec.target_source, "Evidence rules must be declared in the generated proposition's package")
                class_spec.target = term.value
                class_spec.level = 0
            scope = {}
            for field_node in class_spec.module.program.description(class_spec.node).children[1:]:
                field_info = class_spec.module.program.description(field_node)
                if field_info.kind.startswith("class_sort"):
                    continue
                unwrapped = field_node
                while class_spec.module.program.description(unwrapped).kind in ("const_field", "public_const_field"):
                    unwrapped = class_spec.module.program.description(unwrapped).children[0]
                if unwrapped is not field_node and class_spec.module.program.description(unwrapped).kind in ("type_alias", "public_type_alias"):
                    raise self.fail(class_spec.module, field_node, "TypeDef is a checked alias, not const field storage")
                if field_info.kind in ("type_alias", "public_type_alias"):
                    name_node, type_node = field_info.children
                    name = class_spec.module.program.name(name_node)
                    if name in class_spec.fields or name in class_spec.aliases or name in TYPE_NAMES or name == "this":
                        raise self.fail(class_spec.module, field_node, f"Duplicate or reserved alias '{name}'")
                    declared = self.elaborate_type(class_spec.module, type_node, [scope])
                    level = self.universe_of(class_spec.module, field_node, declared)
                    if class_spec.level != 0 and (level is None or level > class_spec.level):
                        raise self.fail(class_spec.module, field_node, "Alias type exceeds the class universe")
                    public = field_info.kind == "public_type_alias"
                    if public:
                        self.check_public_type(class_spec.module, field_node, declared)
                    class_spec.aliases[name] = declared, public, field_node
                    symbol = self.symbol(class_spec.module, field_node, name)
                    self.symbol_types[symbol] = DataType("Sort", level=level) if level is not None else DataType("SortU")
                    self.static_values[symbol] = Static("type", declared)
                    self.alias_nodes.add((class_spec.module.package, field_node))
                    scope[name] = self.symbol_types[symbol], field_node
                    continue
                field_type, name, constant, public = class_spec.module.program.binding(field_node)
                if name is None:
                    raise self.fail(class_spec.module, field_node, "Class fields require names")
                if name in TYPE_NAMES or name in ("this", "Copy"):
                    raise self.fail(class_spec.module, field_node, f"Reserved field name '{name}'")
                if name in class_spec.fields or name in class_spec.aliases:
                    raise self.fail(class_spec.module, field_node, f"Duplicate field '{name}'")
                declared = self.elaborate_type(class_spec.module, field_type, [scope])
                if class_spec.target is not None and self.contains_type(class_spec.module, field_node, declared, class_spec.target):
                    raise self.fail(class_spec.module, field_node, "Recursive evidence specifications need explicit positivity rules and are not supported")
                dependencies = type_references(declared)
                class_spec.dependent = class_spec.dependent or bool(dependencies & set(class_spec.symbols.values())) or declared.name == "SortU"
                class_spec.fields[name] = declared, public, field_node
                if constant or class_spec.level == 0:
                    class_spec.const_fields.add(name)
                    self.const_nodes.add((class_spec.module.package, field_node))
                class_spec.symbols[name] = self.symbol(class_spec.module, field_node, name)
                self.symbol_types[class_spec.symbols[name]] = declared
                scope[name] = declared, field_node
                if class_spec.level != 0:
                    field_level = self.universe_of(class_spec.module, field_node, declared)
                    if field_level is not None and field_level > class_spec.level:
                        raise self.fail(class_spec.module, field_node, f"Field type lives in Sort({field_level}), above class Sort({class_spec.level})")
            class_spec.resolved = True
        finally:
            class_spec.resolving = False

    def alias_type(self, module: Module, spelling: str, node: Node) -> DataType | None:
        if "." not in spelling:
            return None
        owner_name, name = spelling.rsplit(".", 1)
        try:
            owner = self.resolve(module, owner_name, node)
        except LanguageError:
            return None
        if owner.kind == "variable" and self.variable_type(owner).name == "Sort":
            self.static_declaration(owner)
            term = self.normalize_static(module, node, self.symbol(owner.module, owner.node, owner.name))
            if term.kind != "type" or term.value.name != "$generated":
                return None
            proposition = self.propositions[term.value]
            schema = proposition.schema
            if name not in schema.aliases:
                return None
            kind, public, _ = schema.aliases[name]
            if not public and not descendant(module.package, schema.module.package):
                raise self.fail(module, node, f"Private TypeDef '{spelling}'")
            replacements = {schema.symbols[field]: value for field, value in proposition.fields}
            return self.normalize_type(module, node, replace_type(kind, replacements))
        if not isinstance(owner, ClassSpec):
            return None
        self.resolve_class(owner)
        if name not in owner.aliases:
            return None
        kind, public, _ = owner.aliases[name]
        if not public and not descendant(module.package, owner.module.package):
            raise self.fail(module, node, f"Private TypeDef '{spelling}'")
        return kind

    def resolve_contract(self, function: Function) -> None:
        module, p = function.module, function.module.program
        contract_node, _, body = p.description(function.node).children
        owner = function.owner or function.receiver
        self.resolve_class(owner)
        if function.name in owner.fields or function.name in owner.aliases or (owner.type, function.name) in self.constructor_functions:
            raise self.fail(module, function.node, f"Duplicate member '{function.name}'")
        spelling = self.path_expression(module, p.type_node(contract_node))
        if spelling is None:
            raise self.fail(module, contract_node, "Named contracts require a class TypeDef name")
        if "." not in spelling:
            if spelling not in owner.aliases:
                raise self.fail(module, contract_node, "Named contracts require a class TypeDef")
            contract, public, _ = owner.aliases[spelling]
        else:
            contract = self.alias_type(module, spelling, contract_node)
            alias_owner_name, alias_name = spelling.rsplit(".", 1)
            alias_owner = self.resolve(module, alias_owner_name, contract_node)
            public = isinstance(alias_owner, ClassSpec) and alias_name in alias_owner.aliases and alias_owner.aliases[alias_name][1]
            if alias_owner.kind == "variable":
                term = self.normalize_static(module, contract_node, self.symbol(
                    alias_owner.module, alias_owner.node, alias_owner.name,
                ))
                if term.kind == "type" and term.value.name == "$generated":
                    schema = self.propositions[term.value].schema
                    public = alias_name in schema.aliases and schema.aliases[alias_name][1]
        if contract is None or contract.domain is None:
            raise self.fail(module, contract_node, "A named contract must define a complete arrow type")
        if function.public and not public:
            raise self.fail(module, contract_node, "A public function cannot expose a private TypeDef")
        if function.receiver is not None:
            raise self.fail(module, contract_node, "Named contracts must be static; capture stable paths explicitly")
        free_schema_symbols = set().union(*(set(class_spec.symbols.values()) for class_spec in self.classes.values()))
        if type_references(contract) & free_schema_symbols:
            raise self.fail(module, contract_node, "Named contracts require explicit capture binders, not unbound schema fields")
        parameters, symbols, replacements = [], [], {}
        while contract.domain is not None:
            original = contract.binder
            if original is None:
                raise self.fail(module, contract_node, "Named contracts require named arrow binders")
            package, source, name = original.value
            if any(parameter[0] == name for parameter in parameters):
                raise self.fail(module, contract_node, "Contract binders must be distinct")
            if package != module.package:
                source = function.node
            symbol = self.symbol(module, source, name)
            parameters.append((name, replace_type(contract.domain, replacements), source))
            symbols.append(symbol)
            replacements[original] = symbol
            self.symbol_types[symbol] = parameters[-1][1]
            self.parameter_nodes.add((module.package, source))
            self.const_nodes.add((module.package, source))
            contract = contract.codomain
        function.parameters, function.symbols = tuple(parameters), tuple(symbols)
        function.type, function.body = replace_type(contract, replacements), body
        if function.public:
            self.check_public_type(module, function.node, owner.type)
            for kind in [function.type, *(kind for _, kind, _ in parameters)]:
                self.check_public_type(module, function.node, kind)
        if function.type.name in ("Sort", "SortU"):
            statements = p.description(body).children
            statement = p.description(statements[0]).children[0] if len(statements) == 1 else None
            if statement is None or p.description(statement).kind != "return_stmt":
                raise self.fail(module, body, "Type-producing contracts require a pure single return")
            scope = {name: (kind, source) for name, kind, source in parameters}
            function.static_body = self.static_value(module, p.description(statement).children[0], [scope])

    def resolve_signature(self, function: Function) -> None:
        if function.type is not None:
            return
        module, p = function.module, function.module.program
        if function.resolving:
            raise self.fail(module, function.node, "Cyclic dependency in a function's type signature")
        function.resolving = True
        try:
            info = p.description(function.node)
            if function.contract:
                self.resolve_contract(function)
                return
            if info.kind == "procedure":
                name, params, body = info.children
                result = None
            else:
                name, params, result, body = info.children
            if info.kind == "constructor":
                self.resolve_class(function.constructor)
                explicit = self.type_of(module, result)
                function.generator = explicit == DataType("Sort", level=0)
                target = function.constructor.target or function.constructor.type
                if not function.generator and not self.same_type(module, result, explicit, target):
                    raise self.fail(module, result, "A constructor result must be its target type or explicit Prop for proposition generation")
                if function.generator and (function.constructor.target is not None or function.constructor.level == 0):
                    raise self.fail(module, result, "A proposition generator needs a data specification class, not a proof/evidence class")
                if function.generator and function.constructor.const_fields != set(function.constructor.fields):
                    raise self.fail(module, result, "Every proposition specification field must be const")
            owner = function.receiver or function.owner
            if owner is not None:
                self.resolve_class(owner)
                if owner.target is not None:
                    raise self.fail(module, function.node, "Evidence specifications define constructors, not ordinary functions/methods")
                if function.name in owner.fields or function.name in owner.aliases or (function.static and (owner.type, function.name) in self.constructor_functions):
                    raise self.fail(module, function.node, f"Duplicate member '{function.name}'")
            scope = {}
            receiver = function.receiver or function.constructor
            if owner is not None:
                for alias_name, (_, _, alias_node) in owner.aliases.items():
                    alias_symbol = self.symbol(module, alias_node, alias_name)
                    scope[alias_name] = self.symbol_types[alias_symbol], alias_node
            if receiver is not None:
                scope["this"] = receiver.type, function.node
                self.const_nodes.add((module.package, function.node))
            parameters, symbols, seen = [], [], {"this", *TYPE_NAMES}
            forbidden = {self.symbol(module, function.node, "this")} if receiver is not None else set()
            if owner is not None:
                forbidden.update(owner.symbols.values())
            field_parameters = {}
            for index, parameter in enumerate(p.description(params).children):
                type_node, name, constant, _ = p.binding(parameter)
                inferred_field = None
                schema_name = None
                if function.constructor is not None:
                    type_info = p.description(p.type_node(type_node))
                    if type_info.kind == "variable":
                        candidate = p.path(type_info.children[0])
                        if candidate in function.constructor.fields:
                            name = name or candidate
                            schema_name = candidate
                            inferred_field = function.constructor.fields[candidate]
                        elif candidate in function.constructor.aliases:
                            inferred_field = function.constructor.aliases[candidate]
                simple = p.type_node(type_node)
                if p.description(simple).kind == "annotation":
                    simple = p.type_node(p.description(simple).children[1])
                if p.description(simple).kind not in ("variable", "named_type", "sort", "sort_type"):
                    raise self.fail(module, parameter, "Formal parameter types must be simple names; use TypeDef for complex contracts")
                name = name if name is not None else f"$arg{index}"
                if name in seen:
                    raise self.fail(module, parameter, f"Duplicate or reserved parameter '{name}'")
                seen.add(name)
                if inferred_field is not None:
                    declared = replace_type(inferred_field[0], field_parameters)
                    missing = type_references(declared) & set(function.constructor.symbols.values())
                    if missing:
                        raise self.fail(module, parameter, "Inferred constructor parameters must follow their field dependency order")
                else:
                    declared = self.interface_type(module, type_node, scope, forbidden)
                    if function.constructor is not None and name in function.constructor.fields:
                        field_type = replace_type(function.constructor.fields[name][0], field_parameters)
                        unresolved = type_references(field_type) & set(function.constructor.symbols.values())
                        if not unresolved and self.same_type(module, parameter, declared, field_type):
                            schema_name = name
                self.parameter_nodes.add((module.package, parameter))
                if constant or declared.name in ("SortU", "Sort") or function.generator:
                    self.const_nodes.add((module.package, parameter))
                scope[name] = declared, parameter
                parameters.append((name, declared, parameter))
                symbol = self.symbol(module, parameter, name)
                symbols.append(symbol)
                self.symbol_types[symbol] = declared
                forbidden.add(symbol)
                if schema_name is not None:
                    field_parameters[function.constructor.symbols[schema_name]] = symbol
                if inferred_field is not None or schema_name is not None:
                    function.schema_parameters.add(symbol)
            function.parameters = tuple(parameters)
            function.symbols = tuple(symbols)
            if function.constructor is not None:
                function.type = DataType("Sort", level=0) if function.generator else (
                    function.constructor.target or function.constructor.type
                )
            else:
                function.type = self.interface_type(module, result, scope, forbidden) if result is not None else DataType("Void")
            function.body = body
            if function.public:
                exposed = [function.type, *(kind for _, kind, _ in function.parameters)]
                if receiver is not None:
                    exposed.append(receiver.type)
                elif function.owner is not None:
                    exposed.append(function.owner.type)
                for kind in exposed:
                    self.check_public_type(module, function.node, kind)
            if function.type.name in ("Sort", "SortU") and not function.generator:
                statements = p.description(body).children
                statement = statements[0] if len(statements) == 1 else None
                if statement is not None and p.description(statement).kind == "statement":
                    statement = p.description(statement).children[0]
                if statement is None or p.description(statement).kind != "return_stmt":
                    raise self.fail(module, body, "Type-producing functions must be pure single-return expressions")
                function.static_body = self.static_value(module, p.description(statement).children[0], [scope])
        finally:
            function.resolving = False

    def check_public_type(self, module: Module, node: Node, kind: DataType) -> None:
        if kind.nominal and not self.classes[kind].public:
            raise self.fail(module, node, f"Public signature exposes private type '{kind}'")
        if kind.domain is not None:
            self.check_public_type(module, node, kind.domain)
            self.check_public_type(module, node, kind.codomain)
        if kind.term is not None:
            self.check_public_static(module, node, kind.term)
            for term in type_references(kind):
                package, declaration_node, _ = term.value
                target = self.modules[package]
                for declaration in target.declarations.values():
                    if declaration.node is declaration_node and not declaration.public:
                        raise self.fail(module, node, "Public dependent signature exposes a private declaration")

    def static_reference_type(self, term: Static) -> DataType | None:
        if term.kind == "ref":
            return self.symbol_types.get(term)
        if term.kind == "field":
            owner = self.static_reference_type(term.children[0])
            class_spec = self.classes.get(owner)
            return class_spec.fields[term.value][0] if class_spec is not None and term.value in class_spec.fields else None
        return None

    def check_public_static(self, module: Module, node: Node, term: Static) -> None:
        if term.kind == "field":
            owner = self.static_reference_type(term.children[0])
            class_spec = self.classes.get(owner)
            if class_spec is not None and not class_spec.fields[term.value][1]:
                raise self.fail(module, node, f"Public dependent signature uses private field '{term.value}'")
        if term.kind == "type":
            self.check_public_type(module, node, term.value)
        for child in term.children:
            self.check_public_static(module, node, child)

    def check_field_universe(self, module: Module, node: Node, class_spec: ClassSpec, kind: DataType, value_type: DataType) -> None:
        if class_spec.level == 0:
            return
        field_type = value_type if kind.name == "SortU" else kind
        level = self.universe_of(module, node, field_type)
        if level is None:
            raise self.fail(module, node, "A data class needs a bounded universe; use Sort(n) rather than an unbounded SortU constructor parameter")
        if level > class_spec.level:
            raise self.fail(module, node, f"Field requires Sort({level}), above class Sort({class_spec.level})")

    def contains_type(self, module: Module, node: Node, kind: DataType, target: DataType) -> bool:
        kind = self.normalize_type(module, node, kind)
        if kind == target:
            return True
        if kind.domain is not None:
            return self.contains_type(module, node, kind.domain, target) or self.contains_type(module, node, kind.codomain, target)
        if kind.term is not None:
            return self.static_contains_type(module, node, kind.term, target)
        return False

    def static_contains_type(self, module: Module, node: Node, term: Static, target: DataType) -> bool:
        if term.kind == "type" and self.contains_type(module, node, term.value, target):
            return True
        return any(self.static_contains_type(module, node, child, target) for child in term.children)

    def proposition_projection(self, module: Module, node: Node, scopes) -> tuple[DataType, Static] | None:
        """Project immutable metadata from a type description, never from its proof."""
        spelling = self.path_expression(module, node)
        if spelling is None or "." not in spelling:
            return None
        parts = spelling.split(".")
        # A package-qualified ordinary declaration is not a field projection.
        for scope in reversed(scopes):
            if parts[0] in scope:
                declared, source = scope[parts[0]]
                if declared.name != "Sort" or (module.package, source) not in self.const_nodes:
                    return None
                owner = self.normalize_static(module, node, self.symbol(module, source, parts[0]))
                suffix = parts[1:]
                break
        else:
            for length in range(len(parts) - 1, 0, -1):
                try:
                    declaration = self.resolve(module, ".".join(parts[:length]), node)
                except LanguageError:
                    continue
                if declaration.kind != "variable" or self.variable_type(declaration).name != "Sort":
                    continue
                self.static_declaration(declaration)
                owner = self.normalize_static(module, node, self.symbol(declaration.module, declaration.node, declaration.name))
                suffix = parts[length:]
                break
            else:
                return None
        if owner.kind != "type" or owner.value.name != "$generated":
            return None
        if len(suffix) != 1:
            raise self.fail(module, node, "Proposition metadata projections use one declared field at a time")
        proposition = self.propositions[owner.value]
        name = suffix[0]
        if name not in proposition.schema.fields:
            raise self.fail(module, node, f"Unknown proposition metadata field '{name}'")
        field_type, public, _ = proposition.schema.fields[name]
        if not public and not descendant(module.package, proposition.schema.module.package):
            raise self.fail(module, node, f"Private proposition metadata field '{name}'")
        replacements = {
            proposition.schema.symbols[field_name]: value
            for field_name, value in proposition.fields
        }
        value = dict(proposition.fields)[name]
        return self.normalize_type(module, node, replace_type(field_type, replacements)), value

    def generate_proposition(self, module: Module, node: Node, function: Function, values: tuple[Node, ...], scopes) -> DataType:
        self.check_function(function)
        if any(value.kind == "unresolved-field" for value in function.field_values.values()):
            raise self.fail(module, node, "Every generated proposition field requires an explicit stable value")
        substitutions = {
            symbol: self.static_value(module, value, scopes)
            for symbol, value in zip(function.symbols, values)
        }
        raw_fields = tuple(
            (name, replace_static(function.field_values[name], substitutions))
            for name in function.constructor.fields
        )
        frozen_fields = []
        for name, value in raw_fields:
            normalized = self.normalize_static(module, node, value)
            if references(normalized):
                raise self.fail(module, node, "Proposition generation requires statically established field information, not an unresolved runtime argument")
            frozen_fields.append(Static("fieldvalue", name, (normalized,)))
        identity = Static(
            "proposition",
            (function.constructor.module.package, function.constructor.node, function.constructor.name),
            tuple(frozen_fields),
        )
        schema_name = str(function.constructor.type)
        label = f"{schema_name}({', '.join(f'{name}={format_static(value)}' for name, value in raw_fields)})"
        result = DataType("$generated", nominal=True, term=identity, level=0, label=label)
        if result not in self.propositions:
            self.propositions[result] = Proposition(function.constructor, raw_fields, node, module)
            self.classes[result] = ClassSpec(
                str(result), function.constructor.module, function.constructor.node,
                function.constructor.public, "generated proposition", result,
                level=0, resolved=True, synthetic=True,
            )
        self.generated_calls[module.package, node] = result
        self.type_values[module.package, node] = result
        return result

    def lookup(self, module: Module, node: Node, scopes) -> tuple[DataType, Access]:
        p = module.program
        _, node = p.expression_layers(node)
        info = p.description(node)
        if info.kind == "member":
            base_type = self.expression(module, info.children[0], scopes)
            name = p.name(info.children[1])
            field_type = self.field_type(module, base_type, name, node)
            if type_references(field_type):
                owner = self.reference_value(module, info.children[0], scopes)
                field_type = self.field_type(module, base_type, name, node, owner)
            module.types[node] = field_type
            return field_type, Access("", None, (name,))
        if info.kind not in ("variable", "named_type"):
            raise self.fail(module, node, "Assignment target must be a variable or field")
        path = p.path(info.children[0]).split(".")
        for scope in reversed(scopes):
            if path[0] in scope:
                kind, declaration = scope[path[0]]
                access = Access(path[0], None, tuple(path[1:]))
                module.bindings[node] = declaration
                owner = self.symbol(module, declaration, path[0])
                break
        else:
            found = None
            for length in range(len(path), 0, -1):
                try:
                    candidate = self.resolve(module, ".".join(path[:length]), node)
                except LanguageError:
                    continue
                if candidate.kind == "variable":
                    found = candidate, length
                    break
                if length == len(path):
                    raise self.fail(module, node, f"'{'.'.join(path)}' is not a variable")
            if found is None:
                raise self.fail(module, node, f"Unknown variable '{'.'.join(path)}'")
            candidate, length = found
            kind = self.variable_type(candidate)
            access = Access(candidate.name, candidate, tuple(path[length:]))
            owner = self.symbol(candidate.module, candidate.node, candidate.name)
            if candidate.module is module:
                module.bindings[node] = candidate.node
        for field_name in access.fields:
            kind = self.field_type(module, kind, field_name, node, owner)
            owner = Static("field", field_name, (owner,))
        self.access[module.package, node] = access
        module.types[node] = kind
        return kind, access

    def reference_value(self, module: Module, node: Node, scopes) -> Static:
        p = module.program
        _, node = p.expression_layers(node)
        info = p.description(node)
        if info.kind == "member":
            return Static("field", p.name(info.children[1]), (self.reference_value(module, info.children[0], scopes),))
        if info.kind in ("variable", "named_type"):
            parts = p.path(info.children[0]).split(".")
            for scope in reversed(scopes):
                if parts[0] in scope:
                    result = self.symbol(module, scope[parts[0]][1], parts[0])
                    suffix = parts[1:]
                    break
            else:
                for length in range(len(parts), 0, -1):
                    try:
                        declaration = self.resolve(module, ".".join(parts[:length]), node)
                    except LanguageError:
                        continue
                    if declaration.kind == "variable":
                        result = self.symbol(declaration.module, declaration.node, declaration.name)
                        suffix = parts[length:]
                        break
                else:
                    raise self.fail(module, node, "Dependent field access requires an explicit instance reference")
            for name in suffix:
                result = Static("field", name, (result,))
            return result
        return self.static_value(module, node, scopes)

    def field_type(self, module, kind, name, node, owner: Static | None = None):
        kind = self.normalize_type(module, node, kind)
        class_spec = self.classes.get(kind)
        if class_spec is None or name not in class_spec.fields:
            raise self.fail(module, node, f"Unknown field '{name}' on {kind}")
        result, public, _ = class_spec.fields[name]
        if not public and not descendant(module.package, class_spec.module.package):
            raise self.fail(module, node, f"Private field '{name}'")
        if class_spec.level == 0 and (
            self.active_constructor is None or self.active_constructor.constructor is not class_spec
        ):
            raise self.fail(module, node, "Prop class fields are opaque outside their constructors (no unrestricted data extraction)")
        if owner is not None:
            replacements = {
                symbol: Static("field", field_name, (owner,))
                for field_name, symbol in class_spec.symbols.items()
            }
            if self.active_constructor and owner == self.symbol(module, self.active_constructor.node, "this"):
                if name not in self.initialized:
                    raise self.fail(module, node, f"Constructor reads field '{name}' before initialization")
                replacements.update({
                    class_spec.symbols[field_name]: value for field_name, value in self.initialized.items()
                })
            result = replace_type(result, replacements)
        return self.normalize_type(module, node, result)

    def path_expression(self, module: Module, node: Node) -> str | None:
        p = module.program
        _, node = p.expression_layers(node)
        info = p.description(node)
        return p.path(info.children[0]) if info.kind in ("variable", "named_type") else None

    def expression(self, module: Module, node: Node, scopes, expected: DataType | None = None) -> DataType:
        p = module.program
        if expected is not None:
            expected = self.normalize_type(module, node, expected)
        layers, node = p.expression_layers(node)
        args, kind = p.description(node).children, p.description(node).kind
        if kind == "integer":
            result = expected if expected and expected.name in ("Nat", "Int", "Float") and not expected.nominal else DataType("Int")
        elif kind == "decimal":
            result = DataType("Float")
        elif kind == "boolean":
            result = DataType("Bool")
        elif kind == "nil_literal":
            if expected is None or not expected.nominal:
                raise self.fail(module, node, "nil requires an expected class type")
            self.allow_creation(module, node, expected, nil=True)
            self.check_default(module, node, expected, set())
            result = expected
        elif kind in ("variable", "named_type"):
            name = p.path(args[0])
            metadata = self.proposition_projection(module, node, scopes)
            if metadata is not None:
                result = metadata[0]
                module.types[node] = result
                for layer in layers:
                    module.types[layer] = result
                if expected is not None and not self.fits(module, node, result, expected):
                    raise self.fail(module, node, f"Expected {expected}, got {result}")
                return result
            if name == "this" and self.active_constructor and len(self.initialized) != len(self.active_constructor.constructor.fields):
                raise self.fail(module, node, "An unfinished constructor instance cannot escape")
            if name == "this" and self.active_constructor and (
                self.active_constructor.generator or self.active_constructor.constructor.target is not None
            ):
                raise self.fail(module, node, "Use return this to finish this construction; its internal schema object cannot escape")
            native = self.native_type(name)
            local = any(name.split(".")[0] in scope for scope in scopes)
            declaration = None
            if not local and native is None:
                try:
                    declaration = self.resolve(module, name, node)
                except LanguageError:
                    pass
            if native is not None or isinstance(declaration, ClassSpec):
                if isinstance(declaration, ClassSpec):
                    self.resolve_class(declaration)
                value = native if native is not None else declaration.type
                if isinstance(declaration, ClassSpec) and declaration.target is not None:
                    value = declaration.target
                self.type_values[module.package, node] = value
                level = self.universe_of(module, node, value)
                if value.name == "SortU":
                    raise self.fail(module, node, "SortU is a native checking marker, not a first-class type of all universes")
                result = DataType("Sort", level=level) if level is not None else DataType("SortU")
            elif isinstance(declaration, Function):
                self.resolve_signature(declaration)
                self.function_values[module.package, node] = declaration
                result = declaration.signature()
            else:
                result, _ = self.lookup(module, node, scopes)
        elif kind == "member":
            result, _ = self.lookup(module, node, scopes)
        elif kind in ("sort", "sort_type", "arrow_type"):
            value = self.elaborate_type(module, node, scopes)
            self.type_values[module.package, node] = value
            level = self.universe_of(module, node, value)
            result = DataType("Sort", level=level) if level is not None else DataType("SortU")
        elif kind == "annotation":
            declared = self.elaborate_type(module, args[1], scopes)
            result = self.expression(module, args[0], scopes, declared)
        elif kind == "class_literal":
            spelling = self.path_expression(module, args[0])
            if spelling is None:
                raise self.fail(module, node, "Class literal requires a type name")
            class_spec = self.resolve(module, spelling, node)
            if not isinstance(class_spec, ClassSpec):
                raise self.fail(module, node, f"'{spelling}' is not a class")
            self.allow_creation(module, node, class_spec.type)
            given = {}
            replacements = {}
            defaults = {}
            initializers = p.description(args[1]).children
            supplied = {}
            for initializer in initializers:
                name_node, value = p.description(initializer).children
                name = p.name(name_node)
                if name in supplied:
                    raise self.fail(module, initializer, f"Duplicate initializer '{name}'")
                if name not in class_spec.fields:
                    raise self.fail(module, initializer, f"Unknown field '{name}'")
                supplied[name] = initializer
            if class_spec.dependent and list(supplied) != [name for name in class_spec.fields if name in supplied]:
                raise self.fail(module, node, "Dependent class initializers must follow field declaration order")
            for name, (template, public, field_node) in class_spec.fields.items():
                initializer = supplied.get(name)
                if initializer is None:
                    default_type = self.normalize_type(module, node, replace_type(template, replacements))
                    self.check_default(module, node, default_type, set())
                    defaults[name] = default_type
                    continue
                name_node, value = p.description(initializer).children
                if not public and not descendant(module.package, class_spec.module.package):
                    raise self.fail(module, initializer, f"Private field '{name}'")
                field_type = replace_type(template, replacements)
                actual = self.expression(module, value, scopes, field_type)
                self.check_field_universe(module, value, class_spec, self.normalize_type(module, value, field_type), actual)
                given[name] = value
                if name in class_spec.const_fields:
                    replacements[class_spec.symbols[name]] = self.static_value(module, value, scopes)
            self.literals[module.package, node] = class_spec
            self.literal_defaults[module.package, node] = defaults
            result = class_spec.type
        elif kind == "call":
            result = self.check_call(module, node, scopes)
        elif kind == "unary":
            operator = p.text(args[0])
            target = DataType("Bool") if operator == "!" else expected if expected and expected.name in NUMBERS else None
            if operator == "-" and target is not None and target.name == "Nat":
                raise self.fail(module, node, "Negative values are not Nat")
            result = self.expression(module, args[1], scopes, target)
            if operator != "!" and result.name not in NUMBERS:
                raise self.fail(module, node, "Unary arithmetic requires a numeric type")
            if operator == "-" and result.name == "Nat":
                raise self.fail(module, node, "Negating Nat requires an explicit Int conversion")
        elif kind == "binary":
            operator = p.text(args[1])
            left_hint = expected if expected and expected.name in NUMBERS else None
            _, left_node = p.expression_layers(args[0])
            _, right_node = p.expression_layers(args[2])
            if p.description(left_node).kind in ("integer", "nil_literal") and p.description(right_node).kind not in ("integer", "nil_literal"):
                right_type = self.expression(module, args[2], scopes)
                left = self.expression(module, args[0], scopes, right_type)
                right = right_type
            else:
                left = self.expression(module, args[0], scopes, left_hint)
                right = self.expression(module, args[2], scopes, left)
            if operator in ("&&", "||", "&", "|"):
                if left != DataType("Bool") or right != left:
                    raise self.fail(module, node, "Boolean operators require Bool operands")
                result = DataType("Bool")
            elif operator in ("==", "!="):
                result = DataType("Bool")
            else:
                if left.nominal or left.name not in NUMBERS:
                    raise self.fail(module, node, "Arithmetic/comparison requires numeric operands")
                result = DataType("Bool") if operator in ("<", ">", "<=", ">=") else left
        else:
            raise self.fail(module, node, f"Not a runtime expression: {kind}")
        if expected is not None and not self.fits(module, node, result, expected):
            raise self.fail(module, node, f"Expected {expected}, got {result}")
        if self.proof_type(module, node, result):
            function = self.function_values.get((module.package, node))
            if function is not None:
                self.proof_functions[function.module.package, function.node] = function
        module.types[node] = result
        for layer in layers:
            module.types[layer] = result
        return result

    def check_call(self, module: Module, node: Node, scopes) -> DataType:
        p = module.program
        target, arguments_node = p.description(node).children
        values = p.description(arguments_node).children
        spelling = self.path_expression(module, target)
        metadata_callable = self.proposition_projection(module, target, scopes) is not None
        local = spelling is not None and any(spelling.split(".")[0] in scope for scope in scopes)
        declaration = None
        if spelling is not None and not local and spelling not in TYPE_NAMES:
            try:
                declaration = self.resolve(module, spelling, node)
            except LanguageError:
                pass
        function = declaration if isinstance(declaration, Function) else None
        if isinstance(declaration, ClassSpec):
            function = self.constructor_functions.get((declaration.type, ""))
            if function is None:
                if len(values) != 1 or p.description(p.expression_layers(values[0])[1]).kind != "nil_literal":
                    raise self.fail(module, node, f"No unnamed constructor for '{declaration.type}'; call a declared named constructor")
                self.allow_creation(module, node, declaration.type, nil=True)
                self.expression(module, values[0], scopes, declaration.type)
                self.calls[module.package, node] = "typed-nil"
                return declaration.type
        if spelling in BUILTINS:
            if len(values) != 1:
                raise self.fail(module, node, f"{spelling} expects one argument")
            actual = self.expression(module, values[0], scopes)
            if actual.nominal or actual.name not in NUMBERS or spelling not in NUMBERS:
                raise self.fail(module, node, "Numeric conversions require numeric scalar types")
            self.calls[module.package, node] = spelling
            return DataType(spelling)
        receiver = None
        receiver_type = None
        method_name = None
        if function is None and spelling and "." in spelling and not metadata_callable:
            prefix, method_name = spelling.rsplit(".", 1)
            type_declaration = None
            if not local:
                try:
                    type_declaration = self.resolve(module, prefix, node)
                except LanguageError:
                    pass
            if isinstance(type_declaration, ClassSpec):
                function = self.constructor_functions.get((type_declaration.type, method_name))
                if function is None:
                    raise self.fail(module, node, f"Unknown constructor '{spelling}'")
            else:
                receiver_type = self.path_type(module, prefix, target, scopes)
                function = self.methods.get((receiver_type, method_name))
                receiver = prefix
        elif function is None and spelling is None:
            _, base = p.expression_layers(target)
            member = p.description(base)
            if member.kind == "member":
                receiver_type = self.expression(module, member.children[0], scopes)
                method_name = p.name(member.children[1])
                function = self.methods.get((receiver_type, method_name))
                receiver = member.children[0]
        if function is None and method_name == "Copy" and receiver_type in self.classes:
            if values:
                raise self.fail(module, node, "Copy() expects no arguments")
            class_spec = self.classes[receiver_type]
            if class_spec.constructors or class_spec.level == 0:
                raise self.fail(module, node, "Constructor-controlled/Prop classes require an explicit checked Copy method")
            self.calls[module.package, node] = "implicit-copy"
            self.receivers[module.package, node] = receiver
            return receiver_type
        if function is not None:
            self.resolve_signature(function)
            if not self.visible(module, function):
                raise self.fail(module, node, f"Private or unimported function/method '{function.call_name()}'")
            if function.contract and 0 < len(values) < len(function.parameters):
                callable_type = self.expression(module, target, scopes)
                for value in values:
                    self.expression(module, value, scopes, callable_type.domain)
                    substitutions = {}
                    if callable_type.binder in type_references(callable_type.codomain):
                        substitutions[callable_type.binder] = self.static_value(module, value, scopes)
                    callable_type = replace_type(callable_type.codomain, substitutions)
                self.calls[module.package, node] = "function-value"
                return self.normalize_type(module, node, callable_type)
            if len(values) != len(function.parameters):
                raise self.fail(module, node, f"'{function.call_name()}' expects {len(function.parameters)} arguments, got {len(values)}")
            substitutions = {}
            if receiver is not None:
                self.receivers[module.package, node] = receiver
                this_symbol = self.symbol(function.module, function.node, "this")
                if this_symbol in type_references(function.type) or any(
                    this_symbol in type_references(kind) for _, kind, _ in function.parameters
                ):
                    if isinstance(receiver, str):
                        substitutions[this_symbol] = self.static_path(module, receiver, target, scopes)
                    else:
                        substitutions[this_symbol] = self.static_value(module, receiver, scopes)
            for index, (value, (_, kind, _), symbol) in enumerate(zip(values, function.parameters, function.symbols)):
                self.expression(module, value, scopes, replace_type(kind, substitutions))
                remaining = type_references(function.type)
                for _, later_type, _ in function.parameters[index + 1:]:
                    remaining |= type_references(later_type)
                if symbol in remaining:
                    substitutions[symbol] = self.static_value(module, value, scopes)
            self.calls[module.package, node] = function
            if function.constructor:
                self.check_function(function)
            if function.generator:
                self.generate_proposition(module, node, function, values, scopes)
                return DataType("Sort", level=0)
            result = self.normalize_type(module, node, replace_type(function.type, substitutions))
            if self.proof_type(module, node, result):
                self.proof_functions[function.module.package, function.node] = function
            return result
        # A parameter/local/field can hold a function without naming a declaration.
        field_callable = receiver_type in self.classes and method_name in self.classes[receiver_type].fields
        if spelling is not None and declaration is None and not local and not field_callable and not metadata_callable:
            raise self.fail(module, node, f"Unknown function or method '{spelling}'")
        callable_type = self.normalize_type(module, node, self.expression(module, target, scopes))
        if callable_type.name == "Function0":
            if values:
                raise self.fail(module, node, "A zero-argument function value expects no arguments")
            self.calls[module.package, node] = "function-value"
            return callable_type.codomain
        if callable_type.domain is None:
            raise self.fail(module, node, f"Variable '{spelling or 'expression'}' is not callable")
        for value in values:
            if callable_type.domain is None:
                raise self.fail(module, node, "Too many arguments for function value")
            self.expression(module, value, scopes, callable_type.domain)
            substitutions = {}
            if callable_type.binder is not None and callable_type.binder in type_references(callable_type.codomain):
                substitutions[callable_type.binder] = self.static_value(module, value, scopes)
            callable_type = self.normalize_type(module, node, replace_type(callable_type.codomain, substitutions))
        if not values:
            raise self.fail(module, node, "A function value requires an argument")
        self.calls[module.package, node] = "function-value"
        return callable_type

    def static_path(self, module: Module, spelling: str, node: Node, scopes) -> Static:
        parts = spelling.split(".")
        for scope in reversed(scopes):
            if parts[0] in scope:
                kind, declaration = scope[parts[0]]
                key = module.package, declaration
                if key in self.parameter_nodes:
                    self.const_nodes.add(key)
                if key not in self.const_nodes:
                    raise self.fail(module, node, f"Type dependency '{parts[0]}' must be const")
                result = self.symbol(module, declaration, parts[0])
                suffix = parts[1:]
                break
        else:
            for length in range(len(parts), 0, -1):
                try:
                    declaration = self.resolve(module, ".".join(parts[:length]), node)
                except LanguageError:
                    continue
                if declaration.kind == "variable":
                    if (declaration.module.package, declaration.node) not in self.const_nodes:
                        raise self.fail(module, node, "Dependent receiver must be const")
                    kind = self.variable_type(declaration)
                    result = self.symbol(declaration.module, declaration.node, declaration.name)
                    suffix = parts[length:]
                    break
            else:
                raise self.fail(module, node, "Unknown dependent receiver")
        for name in suffix:
            class_spec = self.classes[kind]
            if name not in class_spec.const_fields:
                raise self.fail(module, node, f"Type dependency field '{name}' must be const")
            kind = self.field_type(module, kind, name, node, result)
            result = Static("field", name, (result,))
        self.record_interface_read(result)
        return result

    def allow_creation(self, module: Module, node: Node, kind: DataType, *, nil=False) -> None:
        class_spec = self.classes[kind]
        if class_spec.level == 0 or class_spec.constructors:
            raise self.fail(module, node, f"'{kind}' requires a declared constructor; direct fields, defaults and nil are forbidden")
        if nil and class_spec.dependent:
            raise self.fail(module, node, "Typed nil is not available for dependent classes without a complete initialization")

    def check_default(self, module: Module, node: Node, kind: DataType, visited: set[DataType]) -> None:
        kind = self.normalize_type(module, node, kind)
        if kind in visited:
            return
        if kind.nominal:
            self.allow_creation(module, node, kind, nil=True)
            visited.add(kind)
            for field_type, _, _ in self.classes[kind].fields.values():
                self.check_default(module, node, field_type, visited)
        elif kind.name not in BUILTINS:
            raise self.fail(module, node, f"'{kind}' has no automatic default; initialize it explicitly")

    def constructor_assignment(self, module: Module, node: Node, target: Node, value: Node, scopes) -> bool:
        if self.active_constructor is None:
            return False
        spelling = self.path_expression(module, target)
        if spelling is None or not spelling.startswith("this.") or spelling.count(".") != 1:
            return False
        function = self.active_constructor
        class_spec = function.constructor
        name = spelling.split(".")[1]
        if name not in class_spec.fields:
            raise self.fail(module, target, f"Unknown constructor field '{name}'")
        if name in self.initialized:
            if name in class_spec.const_fields:
                raise self.fail(module, target, f"Const field '{name}' is already initialized")
            return False
        expected_name = list(class_spec.fields)[len(self.initialized)]
        if name != expected_name:
            raise self.fail(module, target, f"Initialize constructor field '{expected_name}' before '{name}'")
        substitutions = {class_spec.symbols[field_name]: item for field_name, item in self.initialized.items()}
        expected = replace_type(class_spec.fields[name][0], substitutions)
        actual = self.expression(module, value, scopes, expected)
        self.check_field_universe(module, value, class_spec, self.normalize_type(module, value, expected), actual)
        determines_type = any(class_spec.symbols[name] in type_references(field_type) for field_type, _, _ in class_spec.fields.values())
        item = (
            self.static_value(module, value, scopes)
            if name in class_spec.const_fields and (determines_type or self.can_capture_static(module, value, scopes))
            else Static("unresolved-field", name)
        )
        self.initialized[name] = item
        target = module.program.expression_layers(target)[1]
        self.access[module.package, target] = Access("this", None, (name,))
        module.types[target] = expected
        return True

    def const_target(self, module: Module, target: Node, scopes) -> None:
        p = module.program
        _, target = p.expression_layers(target)
        info = p.description(target)
        if info.kind == "member":
            owner = self.expression(module, info.children[0], scopes)
            name = p.name(info.children[1])
            if name in self.classes[owner].const_fields:
                raise self.fail(module, target, f"Cannot reassign const field '{name}' through any alias")
            return
        parts = p.path(info.children[0]).split(".")
        access = self.access[module.package, target]
        if access.fields:
            owner_type = self.path_type(module, ".".join(parts[:-1]), target, scopes)
            if parts[-1] in self.classes[owner_type].const_fields:
                raise self.fail(module, target, f"Cannot reassign const field '{parts[-1]}' through any alias")
        else:
            if access.declaration is not None:
                key = access.declaration.module.package, access.declaration.node
            else:
                declaration = next(scope[access.name][1] for scope in reversed(scopes) if access.name in scope)
                key = module.package, declaration
            if key in self.const_nodes:
                raise self.fail(module, target, f"Cannot reassign const/type-dependent binding '{access.name}'")

    def path_type(self, module, spelling, node, scopes):
        parts = spelling.split(".")
        for scope in reversed(scopes):
            if parts[0] in scope:
                kind = scope[parts[0]][0]
                owner = self.symbol(module, scope[parts[0]][1], parts[0])
                suffix = parts[1:]
                break
        else:
            for length in range(len(parts), 0, -1):
                try:
                    declaration = self.resolve(module, ".".join(parts[:length]), node)
                except LanguageError:
                    continue
                if declaration.kind == "variable":
                    kind, suffix = self.variable_type(declaration), parts[length:]
                    owner = self.symbol(declaration.module, declaration.node, declaration.name)
                    break
            else:
                raise self.fail(module, node, f"Unknown receiver '{spelling}'")
        for name in suffix:
            kind = self.field_type(module, kind, name, node, owner)
            owner = Static("field", name, (owner,))
        return kind

    def statement(self, module, node, scopes, returns=None, *, top=False):
        p = module.program
        info = p.description(node)
        if info.kind == "statement":
            return self.statement(module, info.children[0], scopes, returns, top=top)
        if info.kind == "const_declaration":
            inner, _ = self.declaration_node(module, node)
            self.const_nodes.add((module.package, inner))
            return self.statement(module, inner, scopes, returns, top=top)
        args, kind = info.children, info.kind
        if kind == "declaration":
            name, declared = p.name(args[1]), self.elaborate_type(module, args[0], scopes)
            if not top and (name in scopes[-1] or name == "this" or name in TYPE_NAMES):
                raise self.fail(module, node, f"Duplicate declaration or reserved name '{name}'")
            if len(args) == 3:
                self.expression(module, args[2], scopes, declared)
                if (module.package, node) in self.const_nodes and self.can_capture_static(module, args[2], scopes):
                    reference = self.symbol(module, node, name)
                    value = self.static_value(module, args[2], scopes)
                    self.static_values[reference] = value
            elif declared.nominal:
                class_spec = self.classes[declared]
                if class_spec.constructors or class_spec.level == 0:
                    raise self.fail(module, node, "Default creation cannot bypass a constructor or introduce a proof")
                for field_type, _, _ in class_spec.fields.values():
                    self.check_default(module, node, field_type, set())
            elif declared.name not in BUILTINS:
                raise self.fail(module, node, f"'{declared}' requires an explicit initializer")
            elif (module.package, node) in self.const_nodes:
                default = False if declared.name == "Bool" else 0.0 if declared.name == "Float" else 0
                self.static_values[self.symbol(module, node, name)] = Static("literal", default)
            if not top:
                scopes[-1][name] = declared, node
            self.symbol_types[self.symbol(module, node, name)] = declared
            module.types[node] = declared
        elif kind == "assignment":
            if self.proposition_projection(module, args[0], scopes) is not None:
                raise self.fail(module, args[0], "Generated proposition metadata is immutable")
            if self.constructor_assignment(module, node, args[0], args[1], scopes):
                return False
            declared, _ = self.lookup(module, args[0], scopes)
            _, target = p.expression_layers(args[0])
            access = self.access.get((module.package, target))
            if access and access.name == "this" and not access.fields:
                raise self.fail(module, node, "this cannot be reassigned")
            self.const_target(module, args[0], scopes)
            self.expression(module, args[1], scopes, declared)
        elif kind in ("print_stmt", "expression_statement"):
            self.expression(module, args[0], scopes)
        elif kind == "return_stmt":
            if returns is None:
                raise self.fail(module, node, "return is only allowed inside a function")
            if self.active_constructor and self.path_expression(module, args[0]) != "this":
                raise self.fail(module, node, "A constructor must finish its own this instance, not return another object")
            if self.active_constructor and (
                self.active_constructor.generator or self.active_constructor.constructor.target is not None
            ):
                if len(self.initialized) != len(self.active_constructor.constructor.fields):
                    raise self.fail(module, node, "A construction cannot return before every field is initialized")
                expression = p.expression_layers(args[0])[1]
                module.types[expression] = returns
                return True
            self.expression(module, args[0], scopes, returns)
            return True
        elif kind in ("if_stmt", "while_stmt"):
            if self.active_constructor and len(self.initialized) != len(self.active_constructor.constructor.fields):
                raise self.fail(module, node, "Initialize constructor fields in order before branching or looping")
            self.expression(module, args[0], scopes, DataType("Bool"))
            branch_returns = []
            for block in args[1:]:
                scopes.append({})
                try:
                    guaranteed = False
                    for statement in p.description(block).children:
                        guaranteed = self.statement(module, statement, scopes, returns) or guaranteed
                    branch_returns.append(guaranteed)
                finally:
                    scopes.pop()
            return kind == "if_stmt" and len(branch_returns) == 2 and all(branch_returns)
        else:
            raise self.fail(module, node, f"Not a runtime statement: {kind}")
        return False

    def check(self):
        self.receivers: dict[tuple[str, Node], Node | str] = {}
        order = self.initialize_definitions()
        for (receiver, name), function in self.methods.items():
            if name == "Copy" and (function.parameters or function.type != receiver):
                raise self.fail(function.module, function.node, "Copy method requires no arguments and must return its receiver type")
        for module in order:
            for node, _ in self.records(module):
                if module.program.description(node).kind not in ("function", "contract_function", "static_function", "procedure", "constructor", "class_decl", "check_command"):
                    self.statement(module, node, [{}], top=True)
        for class_spec in self.classes.values():
            if class_spec.level == 0:
                continue
            for field_type, _, field_node in class_spec.fields.values():
                level = self.universe_of(class_spec.module, field_node, field_type)
                if level is not None and level > class_spec.level:
                    raise self.fail(class_spec.module, field_node, f"Field type lives in Sort({level}), above class Sort({class_spec.level})")
        for function in self.functions:
            normalized_types = [self.normalize_type(function.module, function.node, function.type)]
            normalized_types.extend(
                self.normalize_type(function.module, node, kind) for _, kind, node in function.parameters
            )
            forbidden = set(function.symbols)
            if function.receiver or function.constructor:
                forbidden.add(self.symbol(function.module, function.node, "this"))
            for kind in normalized_types:
                if (self.dependent_arrow(kind) or type_references(kind) & forbidden) and not function.schema_parameters and not function.contract:
                    raise self.fail(function.module, function.node, "Function interfaces must be non-dependent; package the dependency in a class")
                if function.public:
                    self.check_public_type(function.module, function.node, kind)
            self.check_function(function)
            if self.proof_type(function.module, function.node, function.type):
                self.proof_functions[function.module.package, function.node] = function
        for function in tuple(self.proof_functions.values()):
            self.audit_proof_function(function, set())
        return order

    def audit_proof_function(self, function: Function, active: set[tuple[str, Node]]) -> None:
        key = function.module.package, function.node
        if key in active:
            raise self.fail(function.module, function.node, "Recursive code cannot serve as a proof; the proof fragment must be total")
        self.check_function(function)
        self.audit_proof_body(function.module, function.body, function, active | {key})

    def audit_proof_body(self, module: Module, root: Node, function: Function, active: set[tuple[str, Node]]) -> None:
        pending, seen = [root], set()
        p = module.program
        while pending:
            node = pending.pop()
            if node in seen:
                continue
            seen.add(node)
            self.type_tick(module, node)
            info = p.description(node)
            if info.kind in ("while_stmt", "print_stmt"):
                raise self.fail(module, node, "Proof-producing code cannot loop or perform print effects")
            if info.kind == "assignment" and not (
                function.constructor is not None
                and self.path_expression(module, info.children[0]) is not None
                and self.path_expression(module, info.children[0]).startswith("this.")
            ):
                raise self.fail(module, node, "Proof-producing code cannot mutate runtime state")
            if info.kind == "variable":
                access = self.access.get((module.package, node))
                if access and access.declaration and (access.declaration.module.package, access.declaration.node) not in self.const_nodes:
                    raise self.fail(module, node, "Proof-producing code cannot read mutable globals")
                spelling = self.path_expression(module, node)
                if access and access.fields and not (
                    function.constructor is not None and spelling.startswith("this.")
                ):
                    self.static_path(module, spelling, node, self.proof_scope(function))
            if info.kind == "binary" and p.text(info.children[1]) in ("/", "%"):
                denominator = p.expression_layers(info.children[2])[1]
                if p.description(denominator).kind != "integer" or int(p.text(p.description(denominator).children[0])) == 0:
                    raise self.fail(module, node, "Proof code needs a statically nonzero divisor")
            if info.kind == "call":
                callee = self.calls.get((module.package, node))
                if isinstance(callee, Function):
                    self.audit_proof_function(callee, active)
                elif callee == "function-value":
                    target_type = module.types.get(p.expression_layers(info.children[0])[1])
                    if target_type is None or not self.proof_type(module, node, target_type):
                        raise self.fail(module, node, "An unknown runtime callback cannot determine a proof")
                elif callee in ("Float", "Int", "Nat"):
                    raise self.fail(module, node, "Partial numeric conversion is not permitted in proof code")
            pending.extend(info.children)

    def proof_scope(self, function: Function):
        scope = {name: (kind, node) for name, kind, node in function.parameters}
        if function.receiver or function.constructor:
            scope["this"] = (function.receiver or function.constructor).type, function.node
        return [scope]

    def check_function(self, function: Function) -> None:
        if function.checked:
            return
        if function.checking:
            raise self.fail(function.module, function.node, "Recursive constructor checking would bypass complete initialization")
        self.resolve_signature(function)
        saved = self.active_constructor, self.initialized, self.active_function
        self.active_constructor = function if function.constructor else None
        self.initialized = {}
        self.active_function = function
        function.checking = True
        scopes = [{name: (kind, node) for name, kind, node in function.parameters}]
        receiver = function.receiver or function.constructor
        if receiver:
            scopes[0]["this"] = receiver.type, function.node
        try:
            guaranteed = False
            for node in function.module.program.description(function.body).children:
                if guaranteed and function.constructor:
                    raise self.fail(function.module, node, "Code after a guaranteed return is not allowed")
                guaranteed = self.statement(function.module, node, scopes, function.type) or guaranteed
            if function.constructor:
                missing = set(function.constructor.fields) - self.initialized.keys()
                if missing:
                    raise self.fail(function.module, function.body, f"Constructor leaves required fields uninitialized: {', '.join(sorted(missing))}")
                function.field_values = dict(self.initialized)
                if function.generator:
                    self.audit_generator_body(function)
            elif function.type.name != "Void" and not guaranteed:
                raise self.fail(function.module, function.node, "Function must return a value on every path")
            function.checked = True
        finally:
            function.checking = False
            self.active_constructor, self.initialized, self.active_function = saved

    def audit_generator_body(self, function: Function) -> None:
        """A proposition generator composes metadata, not arbitrary runtime effects."""
        p = function.module.program
        for statement in p.description(function.body).children:
            if p.description(statement).kind == "statement":
                statement = p.description(statement).children[0]
            info = p.description(statement)
            if info.kind == "assignment":
                path = self.path_expression(function.module, info.children[0])
                if path is not None and path.startswith("this.") and path.count(".") == 1:
                    continue
            if info.kind == "return_stmt" and self.path_expression(function.module, info.children[0]) == "this":
                continue
            raise self.fail(function.module, statement, "A proposition generator only initializes its const schema fields and finishes; no print, loops, or external effects")

    def tick(self, module, node):
        self.steps += 1
        if self.steps > MAX_STEPS:
            raise module.program.fail("runtime", node, f"Execution exceeded {MAX_STEPS} steps")

    def runtime_error(self, module, node, message):
        return module.program.fail("runtime", node, message)

    def default_value(self, kind: DataType) -> Value:
        """Field defaults use the one mutable nil object for each nominal type."""
        if kind.nominal:
            return self.nil_object(kind)
        if kind.name == "Bool":
            return False
        if kind.name == "Float":
            return 0.0
        if kind.name in ("Int", "Nat"):
            return 0
        raise RuntimeError(f"No default for checked type {kind}")

    def nil_object(self, kind: DataType) -> Instance:
        class_spec = self.classes[kind]
        if class_spec.level == 0 or class_spec.constructors or class_spec.dependent:
            raise RuntimeError("Checker allowed forbidden nil construction")
        if kind not in self.nil_objects:
            result = Instance(kind, {}, nil=True)
            # Register before descending: self/mutually recursive fields share it.
            self.nil_objects[kind] = result
            result.fields.update(self.default_fields(kind))
        return self.nil_objects[kind]

    def default_fields(self, kind: DataType) -> dict[str, Value]:
        class_spec = self.classes[kind]
        return {
            name: self.default_value(self.normalize_type(class_spec.module, node, field_type))
            for name, (field_type, _, node) in class_spec.fields.items()
        }

    def default_declaration(self, kind: DataType) -> Value:
        return Instance(kind, self.default_fields(kind)) if kind.nominal else self.default_value(kind)

    def instance(self, module: Module, node: Node, value: Value) -> Instance:
        if not isinstance(value, Instance):
            raise RuntimeError("Checked class expression did not produce an instance")
        return value

    def path_value(self, module, spelling, scopes, node):
        parts = spelling.split(".")
        for scope in reversed(scopes):
            if parts[0] in scope:
                value, suffix = scope[parts[0]], parts[1:]
                break
        else:
            for length in range(len(parts), 0, -1):
                try:
                    declaration = self.resolve(module, ".".join(parts[:length]), node)
                except LanguageError:
                    continue
                if declaration.kind == "variable":
                    key = declaration.module.package, declaration.name
                    if key not in self.globals:
                        raise self.runtime_error(module, node, f"Global '{spelling}' used before initialization")
                    value, suffix = self.globals[key], parts[length:]
                    break
            else:
                raise RuntimeError("Checked variable disappeared")
        for name in suffix:
            value = self.read_runtime_field(module, node, value, name)
        return value

    def read_runtime_field(self, module: Module, node: Node, value: Value, name: str) -> Value:
        if isinstance(value, DataType) and value.name == "$generated":
            field = dict(self.propositions[value].fields).get(name)
            if field is None:
                raise RuntimeError("Checked proposition metadata field disappeared")
            return self.materialize_static(module, node, field)
        return self.instance(module, node, value).fields[name]

    def materialize_static(self, module: Module, node: Node, term: Static) -> Value:
        if term.kind == "literal":
            return term.value
        if term.kind == "type":
            return self.runtime_type(module, node, term.value)
        if term.kind == "function":
            return FunctionValue(self.static_functions[term])
        if term.kind == "call" and term.children[0].kind == "function":
            function = self.static_functions[term.children[0]]
            arguments = term.children[1:]
            if len(arguments) < len(function.parameters):
                return FunctionValue(function, bound=tuple(
                    self.materialize_static(module, node, argument) for argument in arguments
                ))
        if term.kind in ("ref", "field"):
            return self.runtime_reference(module, node, term)
        if term.kind == "lambda":
            for symbol, function in self.static_functions.items():
                if term.value == function.symbols and self.same_static(module, node, term, symbol):
                    return FunctionValue(function)
        normalized = self.normalize_static(module, node, term)
        if normalized != term:
            return self.materialize_static(module, node, normalized)
        raise self.runtime_error(module, node, "Unsupported runtime projection from a generated proposition")

    def copy_value(self, module, node, value):
        self.tick(module, node)
        if not isinstance(value, Instance):
            return value
        return Instance(value.type, dict(value.fields))

    def set_field(self, module: Module, node: Node, instance: Instance, name: str, value: Value) -> None:
        class_spec = instance.layout or self.classes[instance.type]
        if name in class_spec.const_fields and (not instance.constructing or name in instance.fields):
            raise self.runtime_error(module, node, f"Cannot mutate const field '{name}' through an alias")
        instance.fields[name] = value

    def runtime_reference(self, module: Module, node: Node, term: Static) -> Value:
        if term.kind == "field":
            owner = self.runtime_reference(module, node, term.children[0])
            return self.read_runtime_field(module, node, owner, term.value)
        if term.kind != "ref":
            raise RuntimeError("Type substitution requires a bound reference")
        for scope in reversed(self.runtime_bindings):
            if term in scope:
                return scope[term]
        package, _, name = term.value
        if (package, name) in self.globals:
            return self.globals[package, name]
        raise self.runtime_error(module, node, f"Type parameter '{name}' has no runtime binding")

    def runtime_static(self, module: Module, node: Node, term: Static) -> Static:
        if term.kind in ("ref", "field"):
            value = self.runtime_reference(module, node, term)
            if isinstance(value, DataType):
                return Static("type", value)
            if isinstance(value, FunctionValue):
                function = self.function_symbol(value.function)
                if value.bound:
                    arguments = []
                    for argument in value.bound:
                        if isinstance(argument, DataType):
                            arguments.append(Static("type", argument))
                        elif isinstance(argument, (int, bool, float)):
                            arguments.append(Static("literal", argument))
                        else:
                            raise self.runtime_error(module, node, "Unsupported bound type-level argument")
                    function = Static("call", children=(function, *arguments))
                return function
            if isinstance(value, (int, bool, float)):
                return Static("literal", value)
            raise self.runtime_error(module, node, "A type expression cannot consume mutable object contents implicitly")
        if term.kind == "type":
            return Static("type", self.runtime_type(module, node, term.value))
        return Static(term.kind, term.value, tuple(self.runtime_static(module, node, child) for child in term.children))

    def runtime_type(self, module: Module, node: Node, kind: DataType) -> DataType:
        if kind.name == "$generated":
            return kind
        if kind.domain is not None:
            replacements = {
                symbol: self.runtime_static(module, node, symbol)
                for symbol in type_references(kind)
            }
            return self.normalize_type(module, node, replace_type(kind, replacements))
        if kind.term is not None:
            return self.normalize_type(module, node, DataType(
                kind.name, term=self.runtime_static(module, node, kind.term), level=kind.level,
            ))
        return kind

    def invoke(self, module: Module, node: Node, function: FunctionValue, values: list[Value]) -> Value:
        self.depth += 1
        if self.depth > 64:
            raise self.runtime_error(module, node, "Function call depth exceeded 64")
        try:
            definition = function.function
            values = [*function.bound, *values]
            if len(values) < len(definition.parameters):
                return FunctionValue(definition, function.receiver, tuple(values))
            consumed, trailing = values[:len(definition.parameters)], values[len(definition.parameters):]
            frame = {name: value for (name, _, _), value in zip(definition.parameters, consumed)}
            if definition.constructor:
                receiver = Instance(
                    definition.constructor.type if definition.generator else definition.type,
                    {}, constructing=True, layout=definition.constructor,
                )
                frame["this"] = receiver
            elif definition.receiver:
                frame["this"] = function.receiver
            bindings = dict(zip(definition.symbols, consumed))
            if definition.receiver or definition.constructor:
                bindings[self.symbol(definition.module, definition.node, "this")] = frame["this"]
            self.runtime_bindings.append(bindings)
            try:
                try:
                    for statement in definition.module.program.description(definition.body).children:
                        self.execute(definition.module, statement, [frame])
                except Return as returned:
                    result = returned.value
                else:
                    if definition.constructor:
                        result = receiver
                    elif definition.type.name == "Void":
                        result = None
                    else:
                        raise RuntimeError("Checked function returned no value")
            finally:
                self.runtime_bindings.pop()
            if definition.constructor:
                if result is not receiver or set(receiver.fields) != set(definition.constructor.fields):
                    raise RuntimeError("Checker allowed incomplete or escaping constructor instance")
                receiver.constructing = False
                if definition.generator:
                    raise RuntimeError("Proposition generators are checked static constructions, not runtime function invocations")
            if trailing:
                if not isinstance(result, FunctionValue):
                    raise RuntimeError("Checked application did not return a function")
                return self.invoke(module, node, result, trailing)
            return result
        finally:
            self.depth -= 1

    def evaluate(self, module, node, scopes):
        p = module.program
        _, node = p.expression_layers(node)
        self.tick(module, node)
        args, kind = p.description(node).children, p.description(node).kind
        result_type = module.types[node]
        if (module.package, node) in self.type_values:
            result = self.runtime_type(module, node, self.type_values[module.package, node])
        elif (module.package, node) in self.function_values:
            result = FunctionValue(self.function_values[module.package, node])
        elif kind == "integer":
            result = int(p.text(args[0]))
            if result_type.name == "Float":
                try:
                    result = float(result)
                except OverflowError as error:
                    raise self.runtime_error(module, node, "Float literal overflow") from error
        elif kind == "decimal":
            result = float(p.text(args[0]))
        elif kind == "boolean":
            result = p.text(args[0]) == "true"
        elif kind == "nil_literal":
            result = self.nil_object(result_type)
        elif kind == "variable":
            result = self.path_value(module, p.path(args[0]), scopes, node)
        elif kind == "member":
            result = self.instance(module, node, self.evaluate(module, args[0], scopes)).fields[p.name(args[1])]
        elif kind == "class_literal":
            class_spec = self.literals[module.package, node]
            fields = {
                name: self.default_value(kind)
                for name, kind in self.literal_defaults[module.package, node].items()
            }
            for init in p.description(args[1]).children:
                name, value = p.description(init).children
                fields[p.name(name)] = self.evaluate(module, value, scopes)
            result = Instance(class_spec.type, {name: fields[name] for name in class_spec.fields})
        elif kind == "annotation":
            result = self.evaluate(module, args[0], scopes)
        elif kind == "call":
            function = self.calls[module.package, node]
            callable_value = self.evaluate(module, args[0], scopes) if function == "function-value" else None
            receiver_value = None
            if function == "implicit-copy" or isinstance(function, Function) and function.receiver:
                receiver = self.receivers[module.package, node]
                receiver_value = (self.path_value(module, receiver, scopes, node) if isinstance(receiver, str)
                                  else self.evaluate(module, receiver, scopes))
                receiver_value = self.instance(module, node, receiver_value)
            values = [self.evaluate(module, arg, scopes) for arg in p.description(args[1]).children]
            if isinstance(function, str):
                if function == "function-value":
                    if not isinstance(callable_value, FunctionValue):
                        raise RuntimeError("Checked function value was not callable")
                    result = self.invoke(module, node, callable_value, values)
                elif function == "typed-nil":
                    result = self.nil_object(result_type)
                elif function == "implicit-copy":
                    result = self.copy_value(module, node, receiver_value)
                elif function == "Float":
                    try:
                        result = float(values[0])
                    except OverflowError as error:
                        raise self.runtime_error(module, node, "Float conversion overflow") from error
                else:
                    result = int(values[0])
                    if function == "Nat" and result < 0:
                        raise self.runtime_error(module, node, "Cannot convert a negative value to Nat")
            else:
                result = self.invoke(module, node, FunctionValue(function, receiver_value), values)
        elif kind == "unary":
            operator, value = p.text(args[0]), self.evaluate(module, args[1], scopes)
            result = not value if operator == "!" else -value if operator == "-" else value
        elif kind == "binary":
            operator = p.text(args[1])
            left = self.evaluate(module, args[0], scopes)
            if operator == "&&" and not left:
                return False
            if operator == "||" and left:
                return True
            right = self.evaluate(module, args[2], scopes)
            if operator in ("&&", "&"):
                result = bool(left and right)
            elif operator in ("||", "|"):
                result = bool(left or right)
            elif operator == "==":
                result = (left is right if isinstance(left, Instance)
                          else self.same_type(module, node, left, right) if isinstance(left, DataType)
                          else left == right)
            elif operator == "!=":
                result = (left is not right if isinstance(left, Instance)
                          else not self.same_type(module, node, left, right) if isinstance(left, DataType)
                          else left != right)
            elif operator == "+":
                result = left + right
            elif operator == "-":
                result = max(0, left - right) if result_type.name == "Nat" else left - right
            elif operator == "*":
                result = left * right
            elif operator in ("/", "%"):
                if right == 0:
                    raise self.runtime_error(module, node, "Division by zero")
                if result_type.name == "Float":
                    result = left / right if operator == "/" else math.fmod(left, right)
                else:
                    quotient = abs(left) // abs(right)
                    if (left < 0) != (right < 0):
                        quotient = -quotient
                    result = quotient if operator == "/" else left - quotient * right
            elif operator == "<":
                result = left < right
            elif operator == ">":
                result = left > right
            elif operator == "<=":
                result = left <= right
            elif operator == ">=":
                result = left >= right
            else:
                raise RuntimeError("Unknown checked operator")
        else:
            raise RuntimeError(f"Unknown checked expression {kind}")
        if isinstance(result, float) and not math.isfinite(result):
            raise self.runtime_error(module, node, "Nonfinite Float result")
        if isinstance(result, int) and result.bit_length() > 100_000:
            raise self.runtime_error(module, node, "Integer result exceeds playground resource budget")
        return result

    def assign(self, module, target, value, scopes):
        p = module.program
        _, target = p.expression_layers(target)
        info = p.description(target)
        if info.kind == "member":
            instance = self.instance(module, target, self.evaluate(module, info.children[0], scopes))
            self.set_field(module, target, instance, p.name(info.children[1]), value)
            return
        access = self.access[module.package, target]
        if access.fields:
            base = self.path_value(module, p.path(info.children[0]).rsplit(".", 1)[0], scopes, target)
            self.set_field(module, target, self.instance(module, target, base), access.fields[-1], value)
        elif access.declaration:
            self.globals[access.declaration.module.package, access.name] = value
        else:
            for scope in reversed(scopes):
                if access.name in scope:
                    scope[access.name] = value
                    return

    def execute(self, module, node, scopes, *, top=False):
        p = module.program
        info = p.description(node)
        if info.kind == "statement":
            return self.execute(module, info.children[0], scopes, top=top)
        if info.kind == "const_declaration":
            return self.execute(module, self.declaration_node(module, node)[0], scopes, top=top)
        self.tick(module, node)
        args, kind = info.children, info.kind
        if kind == "declaration":
            name = p.name(args[1])
            value = self.evaluate(module, args[2], scopes) if len(args) == 3 else self.default_declaration(module.types[node])
            if top:
                self.globals[module.package, name] = value
            else:
                scopes[-1][name] = value
            self.runtime_bindings[-1][self.symbol(module, node, name)] = value
        elif kind == "assignment":
            self.assign(module, args[0], self.evaluate(module, args[1], scopes), scopes)
        elif kind == "print_stmt":
            value = self.evaluate(module, args[0], scopes)
            if len(self.output) >= 2000:
                raise self.runtime_error(module, node, "Print output exceeds playground budget")
            self.output.append(self.display(value))
        elif kind == "expression_statement":
            self.evaluate(module, args[0], scopes)
        elif kind == "return_stmt":
            raise Return(self.evaluate(module, args[0], scopes))
        elif kind == "if_stmt":
            branch = 1 if self.evaluate(module, args[0], scopes) else 2
            if branch < len(args):
                self.execute_block(module, args[branch], scopes)
        elif kind == "while_stmt":
            while self.evaluate(module, args[0], scopes):
                self.execute_block(module, args[1], scopes)
        else:
            raise RuntimeError("Unexpected checked statement")

    def execute_block(self, module, block, scopes):
        scopes.append({})
        try:
            for node in module.program.description(block).children:
                self.execute(module, node, scopes)
        finally:
            scopes.pop()

    def display(self, value, seen=None):
        if value is None:
            return "void"
        if isinstance(value, DataType):
            return str(value)
        if isinstance(value, FunctionValue):
            return "<function>"
        if isinstance(value, Instance) and self.classes[value.type].level == 0:
            return f"<proof {value.type}>"
        if isinstance(value, Instance) and value.nil:
            return f"{value.type}(nil)"
        if isinstance(value, bool):
            return str(value).lower()
        if not isinstance(value, Instance):
            if isinstance(value, int) and value.bit_length() > 12000:
                return f"<integer: {value.bit_length()} bits>"
            return str(value)
        if seen is None:
            seen = set()
        if id(value) in seen:
            return f"{value.type}{{...}}"
        seen.add(id(value))
        fields = ", ".join(f"{name}: {self.display(child, seen)}" for name, child in value.fields.items())
        seen.remove(id(value))
        return f"{value.type}{{{fields}}}"

    def serialize_values(self):
        ids, objects = {}, []
        def convert(value):
            if not isinstance(value, Instance):
                if value is None:
                    return None
                if isinstance(value, DataType):
                    return {"typeValue": str(value)}
                if isinstance(value, FunctionValue):
                    return {"function": value.function.name}
                if isinstance(value, int) and not isinstance(value, bool) and abs(value) > 2**53 - 1:
                    return self.display(value)
                return value
            identity = id(value)
            if identity not in ids:
                ids[identity] = len(ids) + 1
                item = {"id": ids[identity], "type": str(value.type), "nil": value.nil, "fields": {}}
                objects.append(item)
                class_spec = self.classes[value.type]
                item["constFields"] = sorted(class_spec.const_fields)
                item["prop"] = class_spec.level == 0
                if not item["prop"]:
                    item["fields"] = {name: convert(child) for name, child in value.fields.items()}
            return {"object": ids[identity], "type": str(value.type), "nil": value.nil}
        variables = {
            (f"{package}.{name}" if package and package != self.entry.package else name): convert(value)
            for (package, name), value in self.globals.items()
        }
        return variables, objects

    def formal_graph(self, reports):
        """Encode established judgments, without inventing nominal alias types."""
        from .language import Composer, Description

        composer = Composer()

        def leaf(kind, text):
            node = composer.graph.create_node(value=text.encode())
            composer.graph.edit_link(node, 0, composer.graph.root)
            composer.descriptions[node] = Description(kind, (), (), 1, 1)
            return node

        annotations = []
        for report in reports:
            term = leaf("CheckedName", report["term"])
            level = report.pop("typeLevel")
            inferred = leaf("Sort", str(level)) if level is not None else leaf("CheckedType", report["type"])
            normal = term if report["normal"] == report["term"] else leaf("CheckedType", report["normal"])
            annotation = composer.compose("Annotation", (term, inferred))
            annotations.append(annotation)
            report.update(node=term.number, typeNode=inferred.number, normalNode=normal.number,
                          normalTypeNode=inferred.number, annotation=annotation.number)
        final = composer.compose("Judgments", tuple(annotations))
        program = Program(composer.graph.commit(), final, composer.descriptions, ())
        graph = export_program(program)
        by_id = {node["id"]: node for node in graph["nodes"]}
        for report in reports:
            by_id[report["node"]]["type"] = report["type"]
            by_id[report["annotation"]]["type"] = report["type"]
            if report["normalNode"] != report["node"]:
                by_id[report["normalNode"]].update(
                    type=report["type"], alias=True, definition=report["normal"],
                )
        return {**graph, "reports": reports}

    def run(self, *, check_only=False):
        order = self.check()
        reports = []
        for module in order:
            for node, _ in self.records(module):
                if module.program.description(node).kind != "check_command":
                    continue
                expression = module.program.description(node).children[0]
                target = module.program.type_node(expression)
                if module.program.description(target).kind == "annotation":
                    target = module.program.type_node(module.program.description(target).children[0])
                spelling = self.path_expression(module, target)
                if spelling is None:
                    raise self.fail(module, node, "Checks require a named declaration or class TypeDef")
                alias = self.alias_type(module, spelling, target)
                if alias is not None:
                    self.type_values[module.package, target] = alias
                    level = self.universe_of(module, target, alias)
                    inferred = DataType("Sort", level=level) if level is not None else DataType("SortU")
                    outer = module.program.type_node(expression)
                    if module.program.description(outer).kind == "annotation":
                        expected = self.elaborate_type(module, module.program.description(outer).children[1], [])
                        if not self.fits(module, node, inferred, expected):
                            raise self.fail(module, node, f"Expected {expected}, got {inferred}")
                else:
                    inferred = self.expression(module, expression, [])
                module.types[node] = inferred
                module.annotations[node] = {"formalCheck": True}
                reports.append({"source": node.number, "node": target.number, "typeNode": node.number,
                                "annotation": node.number, "term": spelling, "type": str(inferred),
                                "typeLevel": inferred.level,
                                "normal": str(alias) if alias is not None else spelling,
                                "normalType": str(inferred), "normalNode": target.number,
                                "normalTypeNode": node.number})
        for module in order:
            for node, _ in self.records(module):
                if not check_only and module.program.description(node).kind not in ("function", "contract_function", "static_function", "procedure", "constructor", "class_decl", "check_command"):
                    self.execute(module, node, [{}], top=True)
        variables, objects = self.serialize_values()
        for module in order:
            for package, node in self.const_nodes:
                if package == module.package and node in module.program.graph.nodes:
                    module.annotations.setdefault(node, {})["const"] = True
        for class_spec in self.classes.values():
            if class_spec.synthetic:
                continue
            class_spec.module.annotations[class_spec.node] = {
                "sort": class_spec.level, "dependent": class_spec.dependent, "public": class_spec.public,
                "evidenceTarget": str(class_spec.target) if class_spec.target is not None else None,
            }
            if class_spec.target is None:
                class_spec.module.types[class_spec.node] = DataType("Sort", level=class_spec.level)
            for name, (kind, public, node) in class_spec.fields.items():
                class_spec.module.types[node] = kind
                class_spec.module.annotations[node] = {"const": name in class_spec.const_fields, "public": public}
            for name, (kind, public, node) in class_spec.aliases.items():
                level = self.universe_of(class_spec.module, node, kind)
                class_spec.module.types[node] = DataType("Sort", level=level) if level is not None else DataType("SortU")
                class_spec.module.annotations[node] = {"alias": True, "name": name, "definition": str(kind), "public": public}
        for function in self.functions:
            function.module.annotations[function.node] = {
                "constructor": function.constructor is not None, "public": function.public,
                "generator": function.generator, "unnamed": function.constructor is not None and not function.name,
                "static": function.static,
                "contract": function.contract,
                "procedure": function.type.name == "Void",
            }
            function.module.types[function.node] = function.signature()
            for _, kind, node in function.parameters:
                if node is not function.node:
                    function.module.types[node] = kind
        for module in order:
            for node, _ in self.records(module):
                if module.program.description(node).kind == "static_function":
                    function_node = module.program.description(node).children[0]
                    module.types[node] = module.types[function_node]
                    module.annotations[node] = dict(module.annotations[function_node])
        graphs = {module.package: export_program(module.program, module) for module in order}
        result = {
            **graphs[self.entry.package], "package": self.entry.package, "packageGraphs": graphs,
            "output": self.output, "variables": variables, "objects": objects, "steps": self.steps,
            "functions": [
                {"name": fn.call_name(),
                 "parameters": [(name, str(kind)) for name, kind, _ in fn.parameters],
                 "returns": None if fn.type.name == "Void" else str(fn.type),
                 "procedure": fn.type.name == "Void", "public": fn.public, "constructor": fn.constructor is not None,
                 "generator": fn.generator, "unnamed": fn.constructor is not None and not fn.name,
                 "static": fn.static, "contract": fn.contract,
                 "owner": str((fn.constructor or fn.receiver or fn.owner).type)}
                for fn in self.functions
            ] + [
                {"name": f"{class_spec.type}.Copy", "parameters": [], "returns": str(class_spec.type),
                 "public": class_spec.public, "implicit": True, "owner": str(class_spec.type),
                 "static": False, "constructor": False, "generator": False, "unnamed": False}
                for class_spec in self.classes.values()
                if not class_spec.synthetic and (class_spec.type, "Copy") not in self.methods and not class_spec.constructors and class_spec.level != 0
            ],
            "classes": [
                {
                    "name": str(class_spec.type), "sort": class_spec.level, "public": class_spec.public,
                    "fields": [
                        {"name": name, "type": str(kind), "const": name in class_spec.const_fields, "public": public}
                        for name, (kind, public, _) in class_spec.fields.items()
                    ],
                    "constructors": [function.name or "(unnamed)" for function in class_spec.constructors],
                    "aliases": [
                        {"name": name, "type": str(kind), "public": public}
                        for name, (kind, public, _) in class_spec.aliases.items()
                    ],
                    "evidenceTarget": str(class_spec.target) if class_spec.target is not None else None,
                }
                for class_spec in self.classes.values() if not class_spec.synthetic
            ],
            "generatedPropositions": [
                {
                    "type": str(kind), "sort": 0, "schema": str(proposition.schema.type),
                    "source": proposition.source.number, "package": proposition.module.package,
                    "fields": {name: (
                                   format_static(self.normalize_static(proposition.module, proposition.source, value))
                                   if check_only else self.display(self.materialize_static(proposition.module, proposition.source, value))
                               )
                               for name, value in proposition.fields},
                    "aliases": [
                        {"name": name, "type": str(self.normalize_type(
                            proposition.module, proposition.source, replace_type(
                                alias_type, {proposition.schema.symbols[field]: value
                                             for field, value in proposition.fields},
                            ),
                        )), "public": public}
                        for name, (alias_type, public, _) in proposition.schema.aliases.items()
                    ],
                    "evidenceSpecifications": [
                        str(class_spec.type) for class_spec in self.classes.values()
                        if class_spec.target is not None and self.same_type(class_spec.module, class_spec.node, class_spec.target, kind)
                    ],
                }
                for kind, proposition in self.propositions.items()
            ],
        }
        if check_only:
            result["theory"] = self.formal_graph(reports)
            result["execution"] = "class specification checking"
            result["output"] = [f"{report['term']} : {report['type']}" for report in reports]
        return result
