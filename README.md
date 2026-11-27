# Nod

Nod is a graph-backed language with explicit class specifications, checked
type aliases, named function contracts, and managed execution.

The repository has two implementation components:

- [node/](./node/readme.md): immutable node values, ordered fixed-slot graphs,
  draft editing, and validated snapshots.
- [nod/](./nod/nod.md): tokenization, grammar composers, semantic checking,
  runtime values, and the local playground.

## Run the playground

```sh
python3 -m venv .venv
.venv/bin/python -m pip install -r nod/requirements.txt
.venv/bin/python -m nod.server --port 8769
```

Open `http://127.0.0.1:8769/`. The
[formal checker](./nod/theory.html) checks named class types and `TypeDef`
aliases without executing program effects.

```text
class Counter { Int value; }
constructor func Counter(Int value) Counter { this.value=value; }
Counter counter=Counter(3);
print(counter.value);
```

Constructors always declare explicit result types. Ordinary functions may
omit the result for a procedure: `static func Functions.show(Int n){print(n);}`.
There is no source `Void` type. Named constructors use
`constructor func Counter.named(Int value) Counter { ... }` and are called
as `Counter.named(value)`. A complete named `TypeDef` contract remains
`static func H Owner.prove { ... }`, with H supplying the entire function type.

See the [language guide](./nod/nod.md),
[dependent classes and contracts](./nod/dependent_classes.md),
[formal checking guide](./nod/theory.md), and complete examples:

- [Scalar values and methods](./nod/example.nod).
- [Dependent classes](./nod/dependent_example.nod).
- [Any and Exists evidence](./nod/proposition_example.nod).
- [Named class checks](./nod/theory_example.nod).
- [Packages](./nod/package_example.json).

## Validate

Run from the repository root:

```sh
.venv/bin/python -m unittest discover
.venv/bin/python -m node.layer0_demo
elan run leanprover/lean4:v4.35.0 lean nod/theory_reference.lean
```

The Lean file is an independent reference for type contracts and evidence
introduction. The playground does not invoke Lean.
