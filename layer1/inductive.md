# First inductive declarations

This is a small, checked declaration fragment, not all of Lean's inductive
system. The implementation is in [inductive.py](./inductive.py), with examples
in [inductive_demo.py](./inductive_demo.py) and tests in
[test_inductive.py](./test_inductive.py).

## 1. The graph

```text
Inductive
    identity   -> introduced type identity
    parameters -> Parameters
    type       -> declared type-family signature
    context    -> Context owning the introduced identity
    body       -> InductiveBody
                      context -> Context owning constructor declarations
```

The introduced type, constructors, and parameter declarations are Variable
nodes. Completed declarations have `context` and `typing` fields. Type and
constructor identities also have graph-encoded names.

The associated typing field points to `HasType [identity, declaredType]`.
The constructor Context identifies its inductive definition and includes
the parameter Context as its parent. Its ordered declaration list identifies
the constructors. There is no special Constructor node type.

The construction uses the existing plain Layer 0 links, markers, and field
slots. No numbered links, new root rule, or Layer 0 changes were added.

## 2. Build Nat

Run the following from the repository root with Python 3.10 or newer:

```python
from layer1 import Program

p = Program()
u0 = p.universe(0)
nat = p.inductive("MyNat", u0)
nat_type = p.type_node(nat.identity)

zero = nat.constructor("zero", nat_type)
n = p.variable()
succ_type = p.function_type(n, nat_type, nat_type)
succ = nat.constructor("succ", succ_type)
definition = nat.finish()

one = p.apply(succ, zero)
two = p.apply(succ, one)
declaration_check = p.relation("ValidInductive", definition)
value_check = p.relation("HasType", two, nat_type)
snapshot = p.commit()
snapshot.require(declaration_check)
snapshot.require(value_check)
```

This checks the equivalent declaration:

```text
MyNat : U(0)
zero  : MyNat
succ  : MyNat -> MyNat
```

The current code still uses `U(n)` like Lean `Type n`, not the newly agreed
`Sort n` indexing. The Sort/Prop migration and universe-form TypeNode are
separate pending changes. This example does not claim `U(0)` is Prop.

## 3. Staging and references

`p.inductive(...)` begins a draft and returns an `InductiveBuilder`.
Its `identity` is available immediately so constructor signatures can
reference it. `constructor(name, signature)` introduces an identity but
does not yet make it a trusted constructor.

`finish()` creates the full graph fields and Context ownership. It does not
perform semantic validation. Repeating finish or adding constructors afterward
is an error. Checking an unfinished declaration reports a structural error.

The graph can contain cycles:

```text
type identity -> owning Context -> Inductive
    -> body -> constructor Context -> succ
        -> typing Relation -> function signature -> type identity
```

The decoder treats the type identity as a nominal constant while checking
constructor signatures. It does not unfold the declaration through that
cycle. This also distinguishes separately declared types with the same name.

Type checking validates the full definition before trusting a type identity
or any constructor from it. One invalid constructor invalidates the declaration,
even if a different constructor appears valid by itself.

The provisional type identity is used only inside declaration validation.
Invalid declarations leave no trusted constants in the validation cache.
This is not accepting a HasType Relation as its own proof.

## 4. Shared parameters: Box

```python
a = p.variable()
box = p.inductive("Box", u0, parameters=((a, u0),))
box_a = p.type_node(p.apply(box.identity, a))
value = p.variable()
mk = box.constructor(
    "mk", p.function_type(value, p.type_node(a), box_a)
)
box_definition = box.finish()

box_nat = p.type_node(p.apply(box.identity, nat_type))
boxed_zero = p.apply(p.apply(mk, nat_type), zero)
box_check = p.relation("ValidInductive", box_definition)
boxed_check = p.relation("HasType", boxed_zero, box_nat)
updated = p.commit()
updated.require(box_check)
updated.require(boxed_check)
```

The supplied constructor signature excludes the shared parameters; the builder
adds their function-type binders to the introduced type and every constructor.
In this explicit API the resulting `mk` is applied first to its type parameter,
then to its field. Lean may infer that type parameter using implicit notation.

The parameter list is ordered. Later parameter types may refer to earlier
parameters. The builder stores one parameter Context and validates entries
with the earlier entries bound in a temporary environment. It does not yet
implement the conceptual chain of per-entry prefix Context nodes.

Each parameter receives an owned declaration and associated typing Relation.
Parameters cannot be reused as declarations of another inductive.
Per-constructor field binders still use the older identity-only function-type
API; the general Variable and Lambda migration is unfinished.

## 5. What is checked

`ValidInductive [definition]` is a fixed primitive Relation with one input.
It can also be included in RelationAnd/RelationOr decompositions.

Validation checks:

- Complete Inductive, Parameters, InductiveBody, and Context structure.
- Distinct parameter identities, ordering, and valid declared parameter types.
- Context ownership and typing Relations referring to the correct identities.
- Unique constructor names within the body's own Context.
- A type-family signature ending in a Universe.
- Well-typed constructor signatures, including computed signatures.
- Constructor field types whose universe levels do not exceed the result level.
- Constructor results referring to this exact inductive identity with all
  shared parameters unchanged.
- Direct positive recursive fields, such as MyNat or MyList A.

Negative recursive function-domain occurrences are rejected.
Other recursion, including positive function-valued recursive fields and
nested or mutual recursion, is outside this fragment. Unsupported features
raise `UnsupportedInductiveError`, not an ordinary false result.

Known schema mismatches raise EncodingError. Invalid typing or supported
fragment rules raise TypeCheckError. A checking budget failure raises
CheckLimitError. These follow the existing library's failure conventions.

The constructors have no executable Lambda body. Their applications are typed
using their checked signatures and remain constructor applications under
normalization. `BetaReduces` does not reduce `succ zero` to `zero`.

## 6. Inspect it

```python
local = snapshot.view(definition)
body = local.fields(definition)["body"]
context = local.fields(body)["context"]
assert local.kind(body) == "InductiveBody"
assert local.kind(context) == "Context"
assert local.kind(zero) == "Variable"
assert local.name(zero) == "zero"
assert local.fields(zero)["context"] == context
assert snapshot.root not in local.nodes
```

Names are encoded as text helpers in the graph. The implementation stores
character codes using its existing number/Universe encoding; these number
helpers do not assert semantic universe typing claims about the names.
Names support identifier characters and serve display and uniqueness checks.
References still use node identity.

Declaration validation sees only the outgoing view of its explicit arguments,
which includes the required declaration and its Contexts. It does not scan
incoming links or use the global root implicitly. Old snapshots are unaffected
by finishing another draft declaration later.

## 7. Tests and limits

```sh
python3 -m layer1.inductive_demo
python3 -m unittest -v layer1.test_inductive
elan run leanprover/lean4:v4.35.0 lean layer1/inductive_examples.lean
```

The optional Lean check uses the already installed compiler and needs no
Mathlib. [inductive_examples.lean](./inductive_examples.lean) independently
checks Bool, Nat, Box, a recursive list, dependent parameters, function-valued
parameters, and an empty type.

Python tests cover the same fragment and malformed/invalid declarations:
wrong result types, wrong constructor arguments, wrong Context ownership,
negative recursion, changing parameters, duplicate names, universe thresholds,
circular justification, snapshot isolation, and work limits.
The tests also check actual graph shapes rather than adding a Constructor
node kind.

Missing features:

- General indices and type families that change indices in constructor results.
- Recursors, case analysis, induction, and dependent elimination.
- Nested/mutual recursion and positive function-valued recursive fields.
- General Context assumptions, imports, and the Parameters/LambdaBody migration.
- Universe polymorphism, Sort/Prop migration, and proof irrelevance.

This code validates declarations and constructor applications. It does not
claim full Lean compatibility or formally proved soundness. The existing
shared-expression performance limitation has not been optimized in this change.
