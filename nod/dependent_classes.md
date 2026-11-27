# Class contracts, const, and constructors

Nod separates nominal class specifications, transparent checked type aliases,
stored values, and explicit implementations. Every function has a class owner.
Ordinary functions remain non-dependent; a complete dependent implementation
uses a named class-declared contract, not an anonymous source expression.
There is no source anonymous-function syntax or native Pi keyword.

## Structure, aliases, and order

```text
class Box : Sort(2) {
    const A : Type;
    TypeDef Value : A;
    value : Value;
}
```

Fields and aliases can depend only on earlier declarations. `TypeDef` checks
that its expression is a type and satisfies the containing universe bound.
It introduces no nominal identity: `Value` unfolds to `A`.
It is **not storage**: no constructor assignment, initializer entry, default
value, runtime member, or const-field slot exists for an alias. `const TypeDef`
is rejected. Exports list `aliases` separately from `fields`; source nodes carry
`alias`, `definition`, and universe annotations, not const-storage annotations.

Within its owner's declarations an alias uses its simple name. Elsewhere its
type name is qualified, e.g. `Box.Value`. Private aliases are inaccessible
outside their package and descendants; exported aliases use `public TypeDef`.
Public definitions and function signatures must not expose private types.
A public named contract implementation also requires a public contract.

Type dependencies require a const root and const fields throughout any path.
A const object binding fixes its reference, not all of its fields; unrelated
fields can remain mutable. Aliases cannot turn a mutable path into a stable one.

## Universes

`Prop` is `Sort(0)`, `Type` is `Sort(1)`, and `Sort(n):Sort(n+1)`.
An unannotated data class lives in Type. A stored `A:Type` therefore needs
at least `Sort(2)`. Data-field and alias universes must fit the declared bound.
Dependent arrows into Prop are impredicative; other arrow universes use the
maximum of domain and codomain universes.

`SortU` is only an admissibility marker for a statically established universe,
not a first-class universe of all universes. Unbounded constructor inputs
cannot justify a fixed data-class universe. No universe variables are added.
Evidence specifications may instead target a particular generated proposition.

## Ordinary functions and simple parameters

```text
class Functions {
    TypeDef Unary : Int -> Int;
}
static func Functions.increment(Int x) Int { return x+1; }
static func Functions.apply(Unary operation, Int x) Int {
    return operation(x);
}
```

Formal parameter annotations must be simple or qualified names, native scalar
types, or numeric `Sort(n)`. Inline arrows, applications, and complex annotated
types are rejected; declare a `TypeDef` for those contracts. Colon bindings with
simple annotations remain accepted. Parameters may be named or unnamed.

Ordinary `func Owner.name(params) ReturnType` has the conventional declared
return type and non-dependent interface. A static function has no receiver;
an instance method has `this`. Value-producing ordinary functions declare
their result type. Omitting it declares a procedure with no useful return:
`static func Functions.show(Int n){print(n);}`. There is no source `Void`
type, and a procedure cannot return a useful value.
Ordinary function results follow the parameter list; result-first declarations
are not accepted. Interfaces cannot depend on another
parameter or receiver, even through aliases or reducible type functions.

## Constructor-controlled creation

```text
class Cell { const Int value; }
constructor func Cell(Int n) Cell { this.value=n; }
constructor func Cell.special() Cell { this.value=9; }
Cell c=Cell(5);
Cell d=Cell.special();
```

There is at most one explicitly declared unnamed constructor, called `Cell(...)`.
The declaration is `constructor func Cell(params) Cell` for an unnamed
constructor or `constructor func Cell.name(params) Cell` for a named one.
The owner is a simple or fully qualified class path, and the result type is
mandatory. Neither `func Cell constructor(...)` nor the intermediate
`constructor func Cell name(...)` spelling is accepted.
It may coexist with named constructors. Constructors belong to their class's
package. Every stored field must be initialized, in declaration order, before
branching, reading unfinished fields, aliasing/passing the whole object, or
returning it. Finishing the body implicitly returns the completed object;
`return this` is also accepted. Const fields are initialized only once.

When constructors exist, literals, omitted/default construction, nil creation,
and implicit Copy cannot bypass them. The existing scalar and ordinary-object
default/typed-nil rules remain for uncontrolled data classes. Prop never admits
nil/default/literal proof creation or unrestricted proof-data extraction.

Constructor schema inference is deliberately different from ordinary parameters:

```text
class Any : Sort(2) {
    const A : Type;
    TypeDef B : A -> Prop;
    const b : B;
}
constructor func Any(A a, B b) Prop {
    this.A=a;
    this.b=b;
}
```

Here `A a` means that `a` has the **declared field type**, Type, not the
unknown value of field A. The checker maps schema A to parameter a. Parameter
`B b` uses the alias specialized by that earlier mapping. Reversed dependencies
are rejected. Unnamed field-name parameters remain supported where consistent
with these rules. Alias B is not a field: `this.B=...` is forbidden.
A constructor's mandatory result type names its own target type, or `Prop`
(equivalently numeric `Sort(0)`) for proposition generation. Finishing a
constructor body may implicitly return complete `this`; this does not make
the declared result type optional.

## Proposition generation and evidence

```text
class Truth : Prop {}
constructor func Truth() Truth {}
class Functions {}
static func Functions.always(Nat n) Prop { return Truth; }

const Prop P=Any(Nat,Functions.always);
class Evidence : P {
    TypeDef H : ((x:P.A)->P.b(x));
    const h : H;
}
constructor func Evidence(H h) P { this.h=h; }
static func H Evidence.prove { return Truth(); }
P proof=Evidence(Evidence.prove);
```

The preceding Any schema and this block form a complete example. `Any(...)`
returns a proposition description, not evidence and not an Any object.
Its metadata stores A and b, never B. Read `P.b(x)`, not `P.B(x)`.
`P.B` is available only as a specialized type alias (for example, the type
of a predicate variable, or `check P.B:Type`); it is not a callable runtime value.
`Evidence:P` targets that particular proposition instead of creating a new
nominal proposition. Its constructor returns P after checking h against H.
The result may be written `P` or the builder alias `Evidence`, which denotes
the same target. Writing the schema name `Any` instead would change the
meaning and is rejected. A data schema generator must explicitly return
`Prop`, not its owner class.
Synthetic generated propositions do not overwrite the source schema's universe.

The schema's stored fields must all be const. Generated metadata requires stable,
statically established information, not symbolic runtime inputs or effects.
Descriptions from different constructors or alpha/beta/delta-equivalent named
predicates can be semantically equal without sharing Node identity or a mandatory
interned representation. Arbitrary proof instances retain runtime identity.

## Named complete-contract implementations

`static func H Owner.name { ... }` has **no parenthesized parameter list**.
H must be a class TypeDef of a complete function type, and every arrow domain
must have a distinct named binder. Those binders supply parameters and dependent
codomains. The body is checked against the specialized final result.
This narrow extension does not relax ordinary function interfaces.
Qualified aliases may name a visible contract from another owner, including
an imported public contract. Its binders are rebound in the implementation scope.
Unbound schema fields require explicit capture binders rather than implicit receivers.

For nonconstant universal evidence:

```text
class Packed { const p:Prop; const h:p; }
constructor func Packed(p,h) Packed { this.p=p; this.h=h; }
class Proofs { TypeDef H:((x:Packed)->x.p); }
static func H Proofs.prove { return x.h; }
```

Constant Truth evidence fails this contract: `x.p` is not necessarily Truth.
Predicates can use `static func Functions.project(Packed x) Prop{return x.p;}`.
Any and Exists can both take `Packed` and `Functions.project`. For Exists the
evidence specification stores a witness followed by its matching proof:

```text
const Prop Some=Exists(Packed,Functions.project);
class SomeEvidence:Some {
    const witness:Some.A;
    TypeDef H:Some.b(witness);
    const h:H;
}
constructor func SomeEvidence(Some.A witness, H h) Some {
    this.witness=witness;
    this.h=h;
}
```

The witness is explicitly typed using the ordinary type-first convention:
`Some.A witness` (or colon-style `witness:Some.A`). There is no mixed
name-first `witness Some.A` form. Its name and checked field type associate
it with the schema's witness field, so the later alias H specializes
`Some.b(witness)` using that actual argument. A proof for a different witness
is rejected; constant predicates do not stand in for this dependent check.

`Exists` uses the same A/B/b schema and constructor pattern as Any.
Wrong proofs for the chosen witness are rejected. No eliminators or proof-data
extraction operations are introduced.

### Class-based dependent identity

Captures are explicit contract binders and stable partial applications:

```text
class Identity:Sort(2) {
    const A:Type;
    TypeDef Apply:A->A;
    TypeDef I:((T:Type)->(x:T)->T);
    const apply:Apply;
}
static func I Identity.identity { return x; }
constructor func Identity(A a) Identity {
    this.A=a;
    this.apply=Identity.identity(a);
}
const Identity natural=Identity(Nat);
const Identity boolean=Identity(Bool);
print(natural.apply(5));
print(boolean.apply(true));
```

Named contract partial application specializes dependent codomains, preserving
explicit captures. Stable function values can be stored and called; this does
not add anonymous implementations. Pure type-producing implementations require
a single return expression and reduce statically.

## Proof totality and formal checks

Proof-producing implementations cannot recurse, loop, print, mutate runtime
state, read unstable globals/paths, or use unchecked partial numeric operations.
Constructor field initialization is the permitted mutation. Unknown callbacks
cannot determine proofs unless their checked type is itself proof-producing.
Resource-budget exhaustion is an explicit error, never evidence.

`check Box:Sort(2);` and `check Identity.I:Sort(2);` check named declarations
with the runtime specification checker, without executing source effects.
The theory endpoint displays verified Annotation links to actual Sort/type nodes
and transparent alias definitions. Anonymous top-level checking demonstrations
are rejected. Source `axiom`, `def`, and `fun` declarations are not accepted;
unknown scalar names are errors, not assumptions.

Examples: [dependent_example.nod](./dependent_example.nod),
[proposition_example.nod](./proposition_example.nod), and
[theory_example.nod](./theory_example.nod).
The independent [Lean reference](./theory_reference.lean) is not executed by Nod.

```sh
.venv/bin/python -m unittest nod.test_generated_propositions nod.test_dependent_classes nod.test_language nod.test_objects nod.test_checking nod.test_stages nod.test_server
```
