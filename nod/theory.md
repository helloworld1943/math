# Formal named specifications without runtime effects

The [theory explorer](./theory.html) checks the same named class specifications
as the runtime model. It does not execute their constructors, function bodies,
printing, assignments, or loops. Invalid proposals publish no partial graphs.

```text
class Box:Sort(2) {
    const A:Type;
    value:A;
}
check Box:Sort(2);

class Contracts:Sort(2) {
    TypeDef Identity:((T:Type)->(x:T)->T);
    TypeDef Natural:Nat;
}
static func Identity Contracts.identity { return x; }
check Contracts.Identity:Sort(2);
check Contracts.Natural:Type;
```

Class fields and aliases are checked in declaration order. `TypeDef` is a
transparent type definition, not a runtime field, nominal type, or const-storage
slot. Public/private ownership, stable dependencies, bounded universes, complete
construction, and function-body obligations are checked before publishing.
See [ordered contracts](./dependent_classes.md) for the complete semantics.

`static func H Owner.name { ... }` implements the named arrow binders of a
class-defined complete contract H. It is distinct from an ordinary function
whose first type denotes its return value and whose parameter list is explicit.
Ordinary interfaces remain non-dependent. There is no anonymous source
implementation or anonymous top-level checking demo. Complex contract definitions
belong in TypeDef; formal parameter annotations use simple type names.

## What the graphs mean

The source graph preserves fresh grammar and token occurrence descriptions.
The verified-judgment graph encodes established facts: a CheckedName leaf,
an actual Sort leaf with numeric level (or a CheckedType leaf for a non-universe
type), and an Annotation composer linking the two. CheckedType leaves also show
transparent, elaborated alias definitions. These are representations of facts
established by the specification checker, not independently assumed nominal
aliases or an execution trace. Reports link back to their source check nodes.

Annotations in the source graph include actual inferred types, aliases distinct
from fields, and `formalCheck` markers. Equal names/descriptions may have different
graph IDs. Checking does allocate internal semantic descriptions; absence of
runtime effects does not imply absence of checker allocations.

`Sort(n):Sort(n+1)`, with Prop=Sort(0) and Type=Sort(1).
Dependent-arrow universes are impredicative into Prop and otherwise take the
maximum of domain and codomain universes.

## Source APIs

`run_source(source, check_only=True)` and `POST /api/theory` use
`World.run(check_only=True)`, the same specification checker as execution.
A `check` command also makes `run_source(source)` and `POST /api/run` check-only.
Canonical `Nat`, `Int`, `Bool`, and `Float` are the runtime's native types;
unknown names are errors, not new opaque assumptions. Source `axiom`, `def`,
and anonymous `fun` implementations are not accepted.

`/api/theory` accepts a single source and rejects nonempty package-source maps.
Successful responses contain `ok`, a `syntax` graph, and a `theory` judgment graph
with `reports`; they contain no runtime output, variable state, or object table.
The main source API additionally reports `execution: "class specification checking"`,
zero runtime steps, and the checked judgments as output lines.
Sources may contain ordinary effectful code: its types and obligations are checked,
but printing, assignment, loops, and runtime failures are not executed.

## Semantic equality and limits

Equality uses alpha-renaming, beta substitution of named implementations, delta
unfolding, and checked annotation erasure, not physical Node identity.
Aliases add no new nominal identity. Distinct nominal class declarations
remain distinct even when their fields match.
No mandatory interning, anonymous shortcuts, silent fallbacks, or configurable
compatibility modes are introduced.

Proof implementations are checked for totality; generated propositions do not
provide automatic evidence. No proof eliminators, inductive declarations,
recursors, tactics, universe variables, implicit arguments, eta conversion,
proof irrelevance, or unrestricted recursion are added. Work remains bounded.

```sh
.venv/bin/python -m unittest nod.test_checking nod.test_dependent_classes nod.test_generated_propositions
elan run leanprover/lean4:v4.35.0 lean nod/theory_reference.lean
```

The [Lean reference](./theory_reference.lean) independently describes named
classes, Identity, and Any/Exists introductions; it is never called by the playground.
