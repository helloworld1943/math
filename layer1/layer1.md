# Layer 1: a first implementation of the expression core

The core has **Lambda**, **Application**, and **TypeNode**. A TypeNode has
one of three forms: **function**, **variable**, or **application**.
There is no separate FunctionType graph node kind. These are built on the
existing [Layer 0](../layer0/layer0.md) without modifying that library.

The code also supplies reusable TypeNode objects, Variable and Universe nodes,
and fixed Relation kinds so we can actually test the expressions:

- `HasType [expression, suppliedType]`
- `BetaReduces [application, suppliedResult]`
- `ValidInductive [declaration]`
- Graph-decomposed Relations owning RelationAnd or RelationOr nodes.

The node meanings are in [nodetype.md](./nodetype.md).

For a visual explanation, open [animation.html](./animation.html) in a browser.
It is a standalone, roughly 40-second walkthrough with play/pause, back/next,
step selection, clickable nodes, and an AND/OR comparison. No server or
external packages are needed. The animation distinguishes currently implemented
examples from design-only changes; it does not run the Python checker in the
browser. Reduced-motion preferences disable autoplay.

The design now gives a Variable declaration exactly one owner: a Context.
It also has its Layer 0 identity, an associated `HasType`
Relation, and an optional display name. The inductive builder now implements
this declaration metadata for type identities, shared parameters, and
constructors. The older Lambda APIs and examples below still use the
identity-only Variable model.

The conceptual Lambda design now connects a **Parameters node** and a
**LambdaBody node**. Parameters organizes ordered declarations and establishes
their Context. LambdaBody connects that available Context to the expression
describing the computation; it does not own the Variables it uses. A
function-form TypeNode likewise uses a parameter Context for its codomain.
These are semantic uses of Layer 0 links, not new visibility rules.
Layer 1 also requires the root to point to a global Context. Context already
has its own node type; no Plain type or new Layer 0 root type is needed.
Inductive Parameters now has a Context API through the staged builder.
The global root convention and LambdaBody Context connections remain conceptual.
The code in
this guide still uses `lambda_(variable, domain, body)` for one parameter.
Lambda does not yet use the Parameters API, and LambdaBody is not implemented.

## 1. Run it

From the repository root, using Python 3.10 or newer:

```sh
python3 -m layer1.demo
python3 -m unittest -v layer1.test_core
python3 -m unittest -v layer1.test_type_node
python3 -m layer1.composition_demo
python3 -m unittest -v layer1.test_eta layer1.test_composition
python3 -m unittest -q
```

No third-party packages are needed.

Files:

- [core.py](./core.py): graph construction, reading, and fixed Relation dispatch.
- [_calculus.py](./_calculus.py): the primitive typing and substitution checks.
- [demo.py](./demo.py): small runnable examples.
- [test_core.py](./test_core.py): accepted examples and rejection tests.
- [test_type_node.py](./test_type_node.py): type-object reuse, validity, passing
  types, binding, visibility, and backwards compatibility.
- [composition_demo.py](./composition_demo.py): graph AND/OR and eta typing.
- [test_composition.py](./test_composition.py): Boolean tables, graph shape,
  explicit inputs, shared checks, errors, cycles, and deep composition.
- [test_eta.py](./test_eta.py): eta equality and its binding side condition.

## 2. A type object is not a type check

```text
T: TypeNode
    form = function, variable, or application
    ...connections for that form...

r: Relation
    kind = HasType
    arguments = [x, T]
```

`T` is a reusable object describing a type. `r` is a checking computation's
request: it asserts that `x` has that type. The check returns true or false;
it does not return `T` or create a missing type object.

The forms and their constructors are:

| Form | Connections | Constructor |
|---|---|---|
| `function` | variable, domain, codomain | `p.function_type(x, A, B)` |
| `variable` | variable | `p.type_node(type_variable)` |
| `application` | expression pointing to an Application | `p.type_node(type_application)` |

`p.function_type(...)` keeps its existing method name, but returns a
function-form TypeNode directly. There is no intermediate FunctionType node.
`type_node()` no longer wraps an arbitrary expression.

Other nodes can share these type objects. Construction checks their shape,
but does not prove their meaning is valid. A type variable must stand for a
type; an application describing a type must have a Universe as its type.

Universes remain primitive nodes, not another TypeNode form.
`p.type_node(universe)` returns that Universe unchanged.
`p.type_node(existingTypeNode)` likewise returns that same node.
Neither allocates a wrapper. `p.type_node(lambda)` raises `EncodingError`.

Direct type-valued expressions remain accepted in type positions. A
TypeNode is not a mandatory extra field on every expression, and an inline
Application does not need to be named or wrapped before use.

## 3. A function, its type, and an application

```python
from layer1 import Program

p = Program()
u0 = p.universe(0)
u1 = p.universe(1)
x = p.variable()

identity = p.lambda_(x, u1, x)
identity_type = p.function_type(x, u1, u1)
application = p.apply(identity, u0)

function_check = p.relation("HasType", identity, identity_type)
application_check = p.relation("HasType", application, u1)
computation_check = p.relation("BetaReduces", application, u0)

snapshot = p.commit()
snapshot.require(function_check)
snapshot.require(application_check)
snapshot.require(computation_check)
```

In this existing API, `variable()` does not create an owner or a typing
Relation. The domain comes from the enclosing Lambda or function-form TypeNode.
The example reuses `x` for both binders, which the current code permits.
Under the newer single-owner design, those would be separate declarations
whose bound positions match.

The three expressions mean:

```text
identity      = lambda (x : U(1)). x
identity_type = (x : U(1)) -> U(1)
application   = identity U(0)

identity U(0) : U(1)
identity U(0) reduces to U(0)
```

The domain here is `U(1)`, since `U(0) : U(1)`. Using `U(0)` as the domain
while supplying `U(0)` as the argument would be a type error.

All returned expression and Relation handles are Layer 0 `Node` objects.
`application` has only function and argument fields. Its type claim is the
separate Relation node, not a new Application field. We supplied that claim
because we want to check it, not because every Application must have one.
The same applies to a Lambda's function-type claim.

For comparison:

```text
identity_type     a TypeNode with form = function
function_check    a HasType checking request about identity and identity_type
```

## 4. Dependent function types

```python
a = p.variable()
y = p.variable()
ta = p.type_node(a)

inner = p.lambda_(y, ta, y)
inner_type = p.function_type(y, ta, ta)
function = p.lambda_(a, u1, inner)
function_type = p.function_type(a, u1, inner_type)

specialized = p.apply(function, u0)
specialized_type = p.function_type(y, u0, u0)
```

This describes:

```text
function : (A : U(1)) -> (y : A) -> A
function U(0) : (y : U(0)) -> U(0)
```

Use `p.relation("HasType", function, function_type)` and
`p.relation("HasType", specialized, specialized_type)` to state the checks,
then commit again and require those Relations.

No addition, literals, `if`, or loops are used. They belong to later work.

A TypeNode can also describe a type by computation:

```python
computed_type = p.type_node(application)
z = p.variable()
another_function = p.lambda_(z, computed_type, z)
another_type = p.function_type(z, u0, u0)
check = p.relation("HasType", another_function, another_type)
p.commit().require(check)
```

Here `application` reduces to `U(0)`. Checking uses that fact without replacing
the Application inside `computed_type` in the stored graph.

## 5. How the information is stored in the graph

Layer 0 has no labeled links or node attributes. Layer 1 uses distinguished
marker nodes and small field-slot nodes:

```text
Application node
    -> marker "Application"
    -> slot
        -> marker "function"
        -> function expression
    -> slot
        -> marker "argument"
        -> argument expression
```

The marker names above are labels for this explanation. In Layer 0 they are
ordinary nodes. A fixed Layer 1 vocabulary associates their identities with
these meanings. Marker nodes have no outgoing links.

TypeNode uses the same convention. For example, the application form is:

```text
TypeNode
    -> marker "TypeNode"
    -> slot
        -> marker "form"
        -> marker "application"
    -> slot
        -> marker "expression"
        -> the expression describing the type
```

The function form has `form`, `variable`, `domain`, and `codomain` slots.
The variable form has `form` and `variable` slots. Unknown forms, missing or
extra fields, and form/target-kind mismatches are rejected. For example, the
application form must point to an Application, not a Lambda or a Variable.
The `form` field points to a fixed marker; `.form(node)` reads its name.

Each created node is reachable from the root. The root has no incoming links.
Connecting everything from the root does not give expressions reverse access
to it.

The two-input primitive Relations use distinct `first` and `second` slots.
This preserves order and repeated arguments even though Layer 0 links are
unordered sets. For example, `HasType [x, x]` still has two positions.
The one-input `ValidInductive` Relation uses a `target` slot.

For composite Relations, `inputs` points to an ordered linked list, and
`decomposition` points to the owned RelationAnd/RelationOr node.
That combination's `operands` field points to another ordered linked list
of child Relations. `_ListItem(value, next)` and `_ListEnd` are private
encoding helpers using the same marker/slot convention.
Lists have no fixed length and preserve order and repeated nodes.

A Universe's level is encoded in binary using helper nodes, so arbitrary
non-negative integer levels do not require a fixed-size field or a chain as
long as the level's numeric value. Repeated `p.universe(n)` calls reuse a node
within that Program.

This is one initial encoding, not an addition of special link kinds to Layer 0.
The vocabulary is part of the trusted implementation; the raw Layer 0 graph
alone is not yet a portable serialized Layer 1 program.

## 6. Inspecting the concepts

```python
local = snapshot.view(application)
assert local.kind(application) == "Application"
assert local.fields(application)["function"] == identity
assert local.fields(application)["argument"] == u0
assert snapshot.root not in local.nodes

type_view = snapshot.view(identity_type)
assert type_view.kind(identity_type) == "TypeNode"
assert type_view.form(identity_type) == "function"
assert type_view.fields(identity_type)["domain"] == u1
```

`fields()` is read-only. `.children(node)` and `.nodes` expose the underlying
visible Layer 0 nodes, including helper nodes. `.form(typeNode)` returns one
of `function`, `variable`, or `application`; it raises `EncodingError` on
other node kinds. `.level(universe)` reads its integer level.
Calling these methods on a hidden node raises
`UnknownNodeError`.

Later construction does not change an existing snapshot. Call `p.commit()`
again to obtain a snapshot containing the new nodes.

## 7. What a check does

A Relation kind is fixed by the library, not supplied by user Python code.
There is no per-node callback argument.

The code currently obtains a parameter's type from its enclosing binder,
not from a typing Relation attached to that Variable. This is why a separate
`HasType [x, A]` for an open Variable cannot yet be checked using Context
declarations. The newer design must validate declarations before using them;
an attached Relation must not prove itself.

`require(relation)` reads the Relation's two operands and creates a Layer 0
view rooted at those operands. The primitive checks cannot obtain unrelated
graph data through that view or automatically access the program root.

The check decodes only the needed expression structure. Variable identities
are converted to bound positions in temporary Python terms. This lets typing
compare separately allocated but equivalent binders and lets substitution
preserve binding without editing the shared source graph.

`HasType` checks that the proposed type itself has a Universe type, computes
the expression's type internally, and compares it with the proposed type
using beta/eta conversion. These temporary computations do not allocate program
nodes or return an inferred type to the user.

This internal inference is an implementation choice, not a requirement that
every Lambda or Application have a stored or automatically generated type.
If the program needs to refer to a type object elsewhere, the builder must
create or reuse the appropriate type object explicitly.

When checking a function-form TypeNode, the checker validates its domain and
codomain under the binder. For variable and application forms, it checks that
the referenced expression has a Universe as its type under the enclosing
binders. An application returning an ordinary function value is therefore
not a valid type description. TypeNode is not permission to call any value
a type.

The primitive checker uses a temporary mathematical `Pi` term for a
dependent function type. That is an internal computation value, not an
additional FunctionType node in the program graph.

`BetaReduces` checks exactly one outermost application of a Lambda. It does
not normalize all remaining applications and does not prove that the
application is well-typed. Typing is a separate check.

Variable-form and application-form TypeNodes are transparent during beta
comparison. Following their references does not count as another beta step.
Function-form TypeNodes retain their binder/domain/codomain structure.
Applications within descriptions are not automatically evaluated by this
relation. As before, `BetaReduces` checks substitution, not the validity of
type annotations.

`HasType` and `BetaReduces` are **primitive Python checks**. Decomposed Relations
are evaluated through their graph-stored RelationAnd / RelationOr nodes by common
Layer 1 logic. This does not yet represent the internal typing derivations
of `HasType` as graph proof steps.

## 8. Failures are explicit

- `snapshot.check(relation)` returns a Boolean for a well-formed Relation.
- `snapshot.require(relation)` raises `TypeCheckError` if the relation fails.
- Malformed graph structure raises `EncodingError`; it is not silently
  treated as an ordinary false relationship.
- A work-budget failure raises `CheckLimitError`, not false. Both checking
  methods accept `max_steps`, defaulting to 10,000 work units. Other Python
  errors, including recursion exhaustion, propagate.
- Wrong argument counts, unknown Relation kinds, and nodes from other
  Programs are rejected.

Committing checks Layer 0 validity. It does not automatically require every
Relation in the graph to hold. The caller explicitly selects Relations to
check; a false example may be stored alongside a true one.

Likewise, `type_node()` only records an allowed description form. An
application form referring to an expression that does not represent a type
may exist in a snapshot, but using it in a typing check fails.

## 9. What is deliberately limited

- Typing and beta checking accept closed expressions and references to
  validated inductive type/constructor declarations. There is no implicit
  general Context. A function's local binding information still comes from
  its own graph structure.
- Variable scope is lexical: domains are checked outside their binder;
  bodies and codomains are checked inside it.
- Nested binders need distinct Variable identities. Distinct Lambda and
  function-form TypeNode binders can still match by bound position.
- Context ownership, attached declared-type Relations, and names are
  implemented for inductive declarations. General Context assumptions and
  the Lambda declaration migration remain incomplete.
- Separate Parameters and LambdaBody nodes and the Lambda composition
  and their Context connections remain conceptual. The implementation still
  stores a single variable and domain directly on each Lambda.
- Cycles in executable expression structure or TypeNode descriptions
  are rejected. General graph cycles remain allowed by Layer 0.
- Universes are predicative with exact successor levels, not cumulative.
  `U(0)` is not Lean's `Prop`.
- Context is implemented inside the inductive builder, not as a general
  declaration API for arbitrary programs.
- Composite checks use an ordinary Relation parent with no primitive kind.
  Its combination node determines AND versus OR. There is no API for
  replacing the meaning of a primitive kind by supplying arbitrary children.
- Empty groups and circular Relation dependencies are rejected.
- There are no user-defined primitive checkers, external context typing,
  general recursive definitions, Layer 2 operations, or persistence yet.

The older experiments at the repository root are unchanged. This is a new,
small implementation on the actual Layer 0 library, not a claim that the
whole earlier experimental language has already been migrated.

## 10. Broader tests before building Layer 2

The next set of fixtures is in [lean_examples.py](./lean_examples.py), with
tests in [test_lean_examples.py](./test_lean_examples.py).
[lean_examples.lean](./lean_examples.lean) contains independently written Lean
counterparts. These are not a Lean parser or an automatic Lean-to-graph
translator: the graphs are built using the public Layer 1 API.

Run the graph examples and tests:

```sh
python3 -m layer1.lean_examples
python3 -m unittest -v layer1.test_lean_examples
```

The Lean counterparts were checked with an already installed Lean 4.35.0:

```sh
elan run leanprover/lean4:v4.35.0 lean layer1/lean_examples.lean
```

That command is an optional independent check; the Python tests do not require
Lean. No Mathlib or other packages are needed for the Lean file.

### What we tested

| Examples | What they exercise |
|---|---|
| Identity and constant | Binding, polymorphism, and returning an earlier parameter |
| Composition and argument flip | Higher-order functions and nested applications |
| Dependent application | A type family `B : A -> U(0)` and a function returning `B x` |
| Dependent composition | A family `C x y`, including result types depending on computed arguments |
| `Endo` and its identity function | A Lambda returning a function-form TypeNode; checking against a computed type |
| A local `let` expressed as Lambda application | Local definitions without adding a Let node |
| Church Booleans, selection, and negation | Defining Boolean behavior with Lambdas rather than new Boolean primitives |
| Church numerals, addition, and multiplication | Defining iteration and arithmetic without new number or arithmetic nodes |
| Church pairs and both projections | Defining simple data and its operations through functions |

All 20 supported fixtures type-check. Their matching Lean definitions compile.
Our `U(n)` corresponds to Lean's `Type n`, not `Sort n`: in particular,
`U(0)` is not Lean's special `Prop`.

The Python tests check more than acceptance:

- Boolean selection and negation compute to the correct alternatives.
- Addition and multiplication are checked for every pair of inputs from
  0 through 4: 25 sums and 25 products.
- The resulting Church numerals are compared with expected expressions and
  independently inspected to count the iteration steps. Two different values
  having the same type is not enough to pass.
- Pair projections select the correct component.
- Composition, argument flip, and the Lambda encoding of `let` give the
  expected results.
- Generated substitutions at depths 0 through 5 exercise all bound-result
  positions. Additional cases check typing before and after a beta step.
- Wrong argument order, wrong dependent result types, wrong pair types, and
  applying a value as a function are rejected.
- Renaming binder identities does not change a dependent example's type.
- A local view still cannot inspect unrelated examples or the program root.

The public `BetaReduces` Relation checks one step. For multi-step results,
these tests inspect the primitive checker's internal normalizer; they do not
add a new evaluation Relation or a new program node type.

The Lean file also checks representative Boolean, arithmetic, and pair
computations with `rfl`, and verifies that selected invalid declarations fail.
It does not independently compile all 50 Python arithmetic table entries.
The encodings demonstrate what can be built above the core; they are test
fixtures, not a finished Layer 2 library.

### Function eta equality: previously missing, now supported

Lean accepts:

```lean
def etaWitness (A B : Type) (D : (A -> B) -> Type)
    (f : A -> B) (value : D f) : D (fun x => f x) :=
  value
```

Lean treats `fun x => f x` as definitionally equal to `f` here. Our checker
now accepts the matching graph. The additional `etaArgument` example checks
this equality when matching an application argument's type, not just at the
final supplied-type comparison.

The equality computation beta-normalizes the types and then contracts
function eta forms. Contraction requires the parameter not to occur free
inside `f`, including within nested domains and bodies. Removing the binder
also shifts references to surrounding binders correctly. This is function eta
equality, not arbitrary functional extensionality.

Negative tests reject invalid contractions and arbitrary composition changes.
The primitive beta normalizer remains beta-only, and the public `BetaReduces`
Relation still checks a single beta step, not eta or complete equality.

### A practical limit: repeated expansion of shared graphs

A 12-level shared function-type graph has only 85 visible Layer 0 nodes in
this fixture, but decoding it exhausts the default 10,000-work-unit budget.
Each function type uses its predecessor as both domain and codomain.
The decoder expands those shared paths repeatedly into temporary terms.

The failure is reported as `CheckLimitError`, not false or successful typing.
This is a performance limitation, not an ill-typed example. Better handling
of sharing is needed before assuming that large, compact program graphs will
also be cheap to check.

The tests also confirm that increasing the budget can complete a separate,
well-typed chain of 40 applications. A work budget is not a wall-clock timeout
or a guarantee against Python recursion limits.

### Fixed universes in the data encodings

The test Church Boolean quantifies over `A : U(0)`. Passing `U(0)` itself
as `A` fails because `U(0) : U(1)`. The equivalent Lean use also fails.

This is an expected level restriction, not a checker bug. More reusable
Layer 2 encodings will need versions at appropriate levels or a design for
universe-polymorphic definitions. These encodings are also not substitutes
for every feature of Lean's inductive types and dependent eliminators.

### Readiness assessment

The tested expression core is a reasonable base for small Layer 2 experiments.
The tests found no new incorrect acceptance in these examples, but they are
not a proof of soundness, completeness, or agreement with all of Lean.

Before calling Layer 1 finished, the following still need attention:

1. Implement or deliberately revise the documented Variable-owner and Context
   declaration model. Closed Lambda examples do not test general declarations,
   imports, or assumptions.
2. Decide whether and how to decompose primitive typing rules into graph
   proof steps. The shared RelationAnd/RelationOr evaluator is now implemented,
   but `HasType` remains primitive.
3. Avoid repeatedly expanding shared expression graphs during checking.
4. Define any needed universe polymorphism, inductive declarations, and
   checked recursion rather than assuming Layer 2 can bypass missing rules.

The expression node forms are unchanged by eta conversion and the shared
AND/OR evaluator. The equality rule was deliberately extended to function eta;
the remaining limitations stay visible.

## 11. Graph-based AND/OR checks

```python
from layer1 import Program

q = Program()
v0, v1, v2 = (q.universe(n) for n in range(3))
right = q.relation("HasType", v0, v1)
wrong = q.relation("HasType", v0, v2)

choice = q.any_of(v0, v1, v2, relations=(wrong, right))
together = q.all_of(v0, v1, v2, relations=(right, choice))
rejected = q.all_of(v0, v1, v2, relations=(right, wrong))
checked = q.commit()
checked.require(choice)
checked.require(together)
assert not checked.check(rejected)

local = checked.view(together)
group = local.fields(together)["decomposition"]
assert local.kind(together) == "Relation"
assert set(local.fields(together)) == {"inputs", "decomposition"}
assert local.kind(group) == "RelationAnd"
assert local.operands(group) == (right, choice)
assert local.arguments(together) == (v0, v1, v2)
```

The graph is:

```text
Relation [v0, v1, v2]
    -> RelationAnd
        -> HasType [v0, v1]
        -> Relation [v0, v1, v2]
            -> RelationOr
                -> HasType [v0, v2]
                -> HasType [v0, v1]
```

### One operation, stored once

A decomposed parent is just a Relation. Its fields are `inputs` and
`decomposition`; there is no separate logical kind or operator field on it.
The decomposition must point to RelationAnd or RelationOr, and that node
alone determines the operation.

Primitive Relations instead have their provided `kind`, `first`, and
`second` fields. They cannot also have a decomposition. An unrelated true
child therefore cannot override a `HasType` node.

`relation(...)` constructs the provided primitive kinds. Use `all_of(...)`
or `any_of(...)` for composites. These return a parent Relation and create its
owned combination node, not an output Boolean node.
The constructor names are API conveniences, not additional Relation kinds.

Each child must be a Relation, never another bare combination node. Nesting
goes through a child Relation. The constructors reject empty operand
lists before allocating nodes.

### Explicit inputs are still required

The positional arguments to `all_of` and `any_of` are the parent's explicit
inputs. Every input of every direct child must occur in that parent input
list, even when it would be reachable through another input. The rule applies
at each level, so no child's logical input is introduced invisibly.

Input lists may repeat, reorder, or include unused expression nodes.
The child operands are supplied separately with `relations=...`.
Primitive checks still receive views narrowed to their own inputs, not the
broader parent input list.

### Validation and evaluation

Before evaluation, Layer 1 checks the reachable Relation topology, ordered
lists, kinds, ownership, and explicit-input rule. The constructors give each
combination one owner; validation also rejects two different owners sharing
one combination within the checked dependency graph.
This is not a scan of unrelated incoming links across the entire program.

Malformed relation topology is rejected even in an alternative that would
otherwise be skipped. Both dependency checking and evaluation use explicit
stacks, and the tests include 1,050 nested combinations.

Then operands are evaluated left to right:

- RelationAnd stops at the first false relationship.
- RelationOr stops at the first true relationship.
- A primitive relationship failure is an ordinary false alternative.
- An evaluated encoding error, work-limit error, or Python execution error
  propagates; it is not converted into false or hidden by another alternative.
- Skipped primitives are not run. Their expression checks and execution
  errors are therefore not observed in that request.

Results of shared child Relations are reused only within the current
validation request, against that fixed snapshot. No persistent success field
is written onto the graph. One work budget covers the whole request.

The engine rejects cycles in dependency lists and Relation decomposition.
Layer 0 continues to allow non-root cycles in general; a circular proof is
not a justification for a required relationship.

## 12. Quantifiers, existential-style packages, and Prop

These tests leave the shared-graph performance limitation unchanged.
They add fixtures and tests, not new production node kinds or checking rules.

- [logic_examples.py](./logic_examples.py): 14 graph examples built with the
  public Layer 1 API.
- [test_logic_examples.py](./test_logic_examples.py): checking, computation,
  incorrect witnesses, dependent indexes, and universe-boundary tests.
- [logic_examples.lean](./logic_examples.lean): independently written matching
  encodings and additional native Lean checks.

Run from the repository root:

```sh
python3 -m layer1.logic_examples
python3 -m unittest -v layer1.test_logic_examples
elan run leanprover/lean4:v4.35.0 lean layer1/logic_examples.lean
```

The final command uses the already installed Lean compiler and needs no
Mathlib. The Python examples do not require Lean. As in the earlier tests,
the comparison is not an automatic translator or a proof that the two
implementations always agree.

### Universal quantification already uses the function form

These two descriptions use the same dependent function type:

```text
(x : A) -> B(x)
forall x : A, B(x)
```

In Lean, the second is written `∀ x : A, B x`. No separate `Forall` graph
node is needed. A Lambda provides such a function; application specializes
it at a supplied argument.

The new graph examples reorder two quantifiers and check dependent evidence.
Wrong-index tests reject an attempt to use `f x : B x` as evidence for `B y`
when nothing makes those types equal.

### Existential-style packages can be encoded, with limits

For `A : U(0)` and `P : A -> U(0)`, our test uses:

```text
CExists(A, P) =
    (R : U(0)) -> ((x : A) -> P(x) -> R) -> R
```

A package stores its witness and evidence by accepting a handler:

```text
pack(x, evidence) =
    lambda R. lambda handler. handler x evidence
```

The fixtures check:

- Introducing a witness with evidence of `P(x)`.
- Applying a package to a result type and a handler.
- Extracting the witness by choosing `R = A`.
- Mapping evidence from `P(x)` to `Q(x)` while preserving the witness.
- Rejecting evidence for the wrong witness.

Computation tests confirm the actual supplied witness and transformed
evidence reach the correct handler; checking only the package's type would
not establish that.

This encoding lives in `U(1)`. It accepts result types `R : U(0)`, not types
at every universe level. Passing `U(0)` itself as `R` is rejected because
`U(0) : U(1)`. The equivalent Lean encoding has the same restriction.

**This is not Lean's native `Exists`.** It is a continuation-based package
using functions. In Lean, `Exists` takes a Prop-valued predicate and lives
in `Prop`.

The native Lean checks verify:

```lean
-- Allowed: eliminate an existential proof into another proposition.
Exists.elim value handler

-- Not generally allowed as a pattern-matching witness extractor:
-- (A : Type) -> (P : A -> Prop) -> (Exists P) -> A
```

By contrast, Lean's `Sigma` is a dependent data pair. It exposes a witness
`pair.1` and evidence `pair.2 : B pair.1`. The reference file checks those
native operations, but the Python fixtures do not implement primitive Sigma,
its dependent eliminator, or an equivalent full induction principle.

So successful witness packaging does not mean native Exists and dependent
pairs have already been implemented completely.

### Logical Or, validation alternatives, and "there exists"

For `P, Q : U(0)`, the Type-valued disjunction encoding is:

```text
COr(P, Q) = (R : U(0)) -> (P -> R) -> (Q -> R) -> R
```

It lives in `U(1)`. Tests check both introductions, correct handler selection,
and rejection of evidence from the wrong alternative.

Keep the following separate:

| Construct | Meaning and current status |
|---|---|
| Relation with `RelationOr` | Layer 1 validator accepts when at least one child relationship holds; implemented |
| Encoded `COr(P, Q)` | An expression whose inhabitants carry an alternative and support a handler; tested with functions |
| Lean `P ∨ Q` | A proposition with proof constructors and elimination rules; native reference examples only |
| Lean `∃ x, P x` | An existential proposition; native reference examples only |
| Lean `List.any` | A Boolean computation over a list; checked in the Lean reference file, not a primitive graph operation |

Neither a successful validation alternative nor a returned Boolean automatically
constructs evidence of an existential proposition.

### Equality evidence can also be encoded

The test equality is Leibniz-style transport over small type families:

```text
CEq(A, x, y) = (P : A -> U(0)) -> P(x) -> P(y)
```

The fixtures check reflexivity, substitution, symmetry, and transitivity.
Tests check that transporting along reflexivity returns the original
evidence. Symmetry and transitivity of reflexivity also compute as expected.
These operations are checked in Lean too.

This expression describes equality evidence. It is not the validator's
`HasType` relation or a new beta/eta conversion rule. It is also not a claim
that Lean's full native `Eq` eliminator has been implemented.

### Prop is not just another name for our U(0)

Lean uses the names:

```text
Prop   = Sort 0
Type n = Sort (n + 1)
```

Our current mapping is:

```text
U(n) behaves like Type n
```

The tests verify two differences that a simple rename would not fix:

1. **Quantifying a proposition can stay in Prop.** Lean accepts
   `∀ (A : Type 1), A -> True` as a Prop. The result is a proposition even
   though the quantifier ranges over a higher universe. This is part of
   Prop's impredicative function-type rule.
   Our current universe rule takes a maximum instead: `(A : U(1)) -> A -> A`
   has type `U(2)`, not `U(0)`.
2. **Proof irrelevance changes equality.** For `P : Prop` and `p q : P`,
   Lean treats those proofs as definitionally equal. The reference file
   checks that a value of `D p` can be used as `D q`. For a generic
   `P : U(0)`, our checker correctly does not identify arbitrary inhabitants.
   The corresponding Type-valued statement is rejected by Lean too.

The native Exists elimination restriction is another difference from
arbitrary data types. Exact Lean compatibility would need deliberately
specified Prop formation, equality, and inductive elimination rules, not
just a new printed name.

### Keep Universe primitive, separate from Variable

Our recommendation is to keep `Universe(n)` as a primitive expression.
It has fixed meaning and the successor rule `U(n) : U(n + 1)`.

`Sort n` is Lean's notation for a universe expression, not a binding owner.
A variable declared `A : Sort n` is a member of that universe; the owner
of `A` is a Context, including for parameters organized by a function,
function-type, or inductive declaration.

Declaring an ordinary variable `S : U(1)` does not make `S` a universe:
it could stand for any type in `U(1)`. In particular, declaring `A : S`
does not guarantee that `A` is itself a type. A negative fixture verifies
that it cannot then be used blindly as the domain of `lambda (x : A). x`.
Lean rejects the equivalent arbitrary-sort-variable example as well.

It is possible to implement Universe syntax through distinguished constant
nodes instead of a dedicated node kind. That is a representation choice,
but those constants would still require primitive universe-level checking
rules. Treating them as ordinary Variable declarations would not replace
those rules.

If we later add universe-level parameters such as Lean's `u`, they will be
parameters of the universe-level language, not ordinary term variables with
type `Sort n`. This experiment does not add universe polymorphism or Prop.

### What this adds to the design assessment

The current core handles many higher-order and dependent logical encodings
without new expression kinds. All 14 new supported fixtures type-check;
tests also verify their computations and reject specific invalid examples.

The remaining boundaries are real: native Prop semantics, inductive
definitions and eliminators, full Context declarations, and universe-level
polymorphism are not supplied automatically by lambda encodings. A limited
inductive declaration fragment is now implemented separately; its recursors
and induction rules are not yet implemented.

No sharing optimization, Prop special case, or universe-rule change was
made to make these examples pass.

## 13. Inductive declaration implementation

[inductive.md](./inductive.md) describes the staged Inductive/InductiveBody
builder, constructor Contexts, direct-positive recursive checks, and limits.
Run the example with:

```sh
python3 -m layer1.inductive_demo
python3 -m unittest -v layer1.test_inductive
```

Constructors remain ordinary Variable declarations; no Constructor node kind
was added. Their declared typing Relations are checked through the enclosing
inductive definition, not used as circular proofs.

## 14. Additional readiness cases and visual walkthrough

[test_additional_cases.py](./test_additional_cases.py) adds 15 more test
methods within the implemented fragment. [additional_examples.lean](./additional_examples.lean)
contains independent Lean counterparts and selected expected failures.

```sh
python3 -m unittest -v layer1.test_additional_cases
elan run leanprover/lean4:v4.35.0 lean layer1/additional_examples.lean
```

The added cases cover:

- Higher-order repeated application and returning another function.
- Type-valued functions given computed type arguments.
- A five-by-five table of nominal-type argument matches, including different
  declarations with the same display name.
- All six permutations of three distinct constructor field types.
- Inductive parameters including a dependent function family and evidence
  whose type is an application of that family.
- Dependent constructor fields, without adding indices or elimination.
- Larger-universe parameterized data.
- Multiple constructors sharing the same introduced type identity.
- Rejecting parameter reuse and evidence for the wrong witness.
- Mixed declaration and typing checks under graph AND/OR.
- All 54 source/result binder-position combinations at nesting depths
  1 through 4, including deliberately wrong beta results.
- Visibility boundaries between unrelated inductive definitions.

The tests assert actual results and rejection behavior, not just that a graph
can be committed. The independent Lean file compiles the new representative
cases; it is not a formal proof that the Python checker agrees with all Lean
programs.

The current implementation passed these tests without changes to production
checking rules. Two initial fixtures were corrected: one reused an enclosing
binder identity, and one supplied a type at the wrong universe level. Both
were invalid under the chosen rules, not reasons to relax checking.

[animation.html](./animation.html) explains the existing examples in ten steps:

1. Universe typing.
2. A function-form TypeNode as a type description.
3. A Lambda and its parameter/body connections.
4. Application without a stored result type.
5. A single checked beta step.
6. Rejection of a wrong supplied type.
7. Dependent substitution into a result type.
8. Common RelationAnd/RelationOr evaluation.
9. InductiveBody and constructor Contexts.
10. Constructor applications and the remaining boundaries.

The drawings omit marker and slot helpers and some auxiliary declaration
information. They describe the implemented graph concepts, not a complete
serialized graph. Dashed arrows show checked computation, not mutations of
the original nodes.

Universe/Prop indexing changes, the Lambda Parameters/LambdaBody migration,
case analysis, indices, and the shared-graph performance improvement remain
separate work. The added tests do not establish that Layer 1 is finished or
formally sound.
