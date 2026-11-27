# Nod: descriptions, static checking, and managed execution

Nod uses the [Node foundation](../node/readme.md). Every token occurrence and
grammar reduction constructs a fresh description node. **There are no
tokenizer/composer reuse modes or mandatory same-type node identities.**
Type equality is a semantic judgment, not a comparison of allocated IDs.

The [dependent-class extension](./dependent_classes.md) adds ordered colon
fields and parameters, arrow types, const, sort annotations, and explicitly
checked constructors. [dependent_example.nod](./dependent_example.nod) is a
complete example. There is no native Pi keyword; dependent field contracts
use `(x:A) -> B(x)`.
The same guide now covers explicit `Prop` generators and evidence specifications
targeting their results. [proposition_example.nod](./proposition_example.nod)
shows unnamed Any/Exists generators, generated propositions in Prop, and
universal/existential evidence introductions.

## Run

```sh
python3 -m venv .venv
.venv/bin/python -m pip install -r nod/requirements.txt
.venv/bin/python -m nod.server --port 8769
```

Open `http://127.0.0.1:8769/`. The [playground](./playground.html) automatically
checks and executes edits. Its package-example button loads an entry program
and two related package sources. Additional sources are editable as a JSON
map. A package selector inspects each package's actual description graph.
Opening the HTML directly with `file://` does not run the Python backend.
The **Dependent classes** button loads the new complete constructor/const
example. Class specifications and graph-node annotations show sorts,
const fields, and constructors.
The **Propositions / evidence** button shows the generator's Prop result,
immutable proposition metadata, and the evidence specification's target
separately from opaque runtime proof objects.
Runtime functions now require explicit class ownership; static helpers use
`static func Owner.name(...) ReturnType`. The dependent example constructs an
Identity class with a typed apply field and a named complete-contract implementation.

The [tokenizer](./tokenizer.html), [grammar explorer](./grammar.html), and
[type-theory explorer](./theory.html) remain separate stage views.

## Basic types and literals

```text
Nat count = 10;
Int offset = -5;
Bool ready = true;
Float ratio = 1.5;
```

These standard runtime types are available without importing a package.
Their names are ordinary type-name descriptions, not four unrelated syntax
productions. Lowercase scalar aliases are not accepted.

- Nat is an arbitrary-precision nonnegative integer; subtraction saturates
  at zero. Negative Nat literals are rejected.
- Int is an arbitrary-precision signed integer.
- Bool is `true` or `false`, never implicitly interchangeable with numbers.
- Float is finite IEEE 754 binary64-style arithmetic via the Python runtime.
  Nonfinite literals/results and division by zero are explicit errors.

An integer literal is interpreted at the expected numeric type. Unconstrained
integer expressions default to Int. Decimal/exponent literals have Float type.
Conversion of already typed values is explicit: `Int(n)`, `Nat(i)`, `Float(n)`.
Int/Nat conversion from Float truncates toward zero; converting a negative
value to Nat fails. Float conversion can lose precision. No implicit mixed
Nat/Int/Float arithmetic. Numeric division on integers truncates toward zero;
remainder satisfies `a = (a / b) * b + a % b`.

The mathematical types have no fixed bit width. The playground still imposes
resource budgets; exhaustion is an error, never wraparound. A budget is not a
new type. Float is approximate arithmetic, not a mathematical real-number type.

## Classes, aliases, and fields

```text
class Point {
    Int x;
    Int y;
}

Point p = Point{x:1, y:2};
Point q = p;
q.x = 9; // p.x is now 9
q = Point{x:3, y:4}; // rebinds q, not p
```

A class declaration introduces a nominal type. Two separately named classes
remain distinct even with identical fields. Supplied class fields must be
unique and type-compatible; omitted fields receive their type's default value.
Runtime instances have object
identity, independent of immutable syntax nodes.

### Default initialization and nil

```text
Bool flag;    // false
Int offset;   // 0
Nat count;    // 0
Float ratio;  // 0.0
Point fresh;  // allocates a new Point with scalar defaults
Point a = nil; // the shared Point(nil) object
Point b = Point(nil); // explicitly names the same typed object
print(a == b); // true
print(fresh == nil); // false

Point p = Point{x:5}; // y defaults to 0
Point empty = Point{}; // a real object, with both fields zero
a.x = 7;
print(b.x); // 7: typed nil is shared and mutable
```

Uninitialized local/global class declarations allocate fresh usable objects.
Scalar fields use zero/false defaults. Each omitted class-valued field
references its own type's shared mutable nil object, rather than recursively
allocating a new object. Self/mutually recursive types therefore produce finite
object graphs with shared references or cycles.

For each nominal class type X there is one **X(nil) object per execution**.
It starts with scalar defaults and references the appropriate typed nil objects
for nested class fields. `X x=nil;` means `X x=X(nil);`. Nil is not a separate
untyped value, null pointer, or vacant Node byte payload.

Bare `nil` requires an expected class type from a declaration, assignment,
argument, return, field initializer, or comparison with a typed class.
`X(nil)` explicitly supplies that type. `print(nil)`, `nil==nil`, scalar nil
assignments, and nil conditions are rejected. `print(X(nil))` prints `X(nil)`.
Different nominal types have different nil objects and do not become compatible.

Typed nil objects support ordinary field access, mutation, and method calls
(including default/custom Copy). Mutating X(nil) affects every alias to it,
including default nested X fields on other objects. A newly allocated outer
object still receives scalar defaults, not the nil object's mutated scalar
values. Default Copy makes a fresh non-nil outer object with copied fields;
nested references remain shared. A user override can instead return `this`.

The object table represents typed nil as an object reference with `"nil":true`,
not JSON null. Nil's identity remains stable after mutation. The singleton is
execution-local: separate server requests do not share mutable state. This is
a runtime object rule only, not a reintroduction of tokenizer/composer interning.

Partial initialization does not bypass visibility: explicitly supplied private
fields remain inaccessible outside their package/descendants. Omitted private
fields may receive defaults, but callers still cannot read or write them.

Basic values have value semantics; classes have managed alias semantics.
Nested class fields are references to other objects. No raw pointer type,
address arithmetic, or manual lifetime API is exposed.

### Implicit Copy method, with an optional override

Ordinary classes without constructors or a Prop annotation have an implicit
accessible `Copy()` instance method:

```text
Point c = p.Copy();
```

The default creates a **new outer object**, copying its fields. Scalar fields
are independent; nested class fields retain their aliases. It does not
recursively clone them. There is no builtin free function `Copy(p)`.

A method declared in the class's package can replace that default:

```text
class Inner { Int value; }
class Outer { Inner child; }

func Inner.Copy() Inner {
    return Inner{value:this.value};
}

func Outer.Copy() Outer {
    return Outer{child:this.child.Copy()};
}
```

This example deliberately copies the child too. An override may choose other
behavior, including returning `this`. It must have no explicit parameters
and return its receiver's type. Normal method visibility applies: a private
override cannot be invoked by unrelated packages. Overrides are unique per
receiver and must be defined in the class's declaring package. The default
Copy method is not a hidden language-level pointer or a type mutation.
Constructor-controlled and Prop classes require an explicit checked Copy
method; they do not inherit a default field-based creation bypass.

## Class-owned functions and external instance methods

```text
class Math {}
static func Math.add(Int a, Int b) Int { return a + b; }

func Point.sum() Int {
    return this.x + this.y;
}

func Point.move(Int dx, Int dy) Point {
    this.x = this.x + dx;
    this.y = this.y + dy;
    return this;
}

print(p.sum());
p.move(1, 2);
```

Class bodies contain ordered fields and checked `TypeDef` aliases; function
implementations are declared outside their explicit class owner.
`this` is an implicit parameter of the receiver type. It cannot be rebound,
but its fields may be changed. Methods can only be declared in the package
that declares their receiver type. Static functions also require a declared
class owner in that package, but have no `this` and are called as
`Math.add(1,2)`. A static function can itself be passed as a function value.
Standalone func declarations are rejected; no implicit owner is invented.
Ordinary functions put the result type after their parameters:
`func Owner.name(parameters) ReturnType { ... }`. Result-first declarations
are not accepted as an alternate form.
Colon-style `x:Int` and unnamed `Int` parameters are also supported.
Ordinary functions may omit their result type to declare a procedure with
no useful return value: `static func Math.show(Int n){print(n);}`.
Value-producing functions explicitly declare their trailing result.
There is no source `Void` type; procedure exports carry `returns:null` and
`procedure:true`, and graph annotations display `no-result`.
Function values can be supplied to parameters or stored in fields, but only
named implementations are source syntax. `TypeDef Unary:Int->Int;` supplies
a checked type name for an ordinary function parameter; inline complex
parameter annotations are rejected. A complete dependent contract such as
`TypeDef H:((x:Packed)->x.p);` is implemented by
`static func H Owner.prove { return x.h; }`, without a parameter list.
Its named arrow binders declare parameters and specialize the result type.
H describes the complete function contract, not only its result; this
distinct contract implementation form does not repeat a parameter list.
There is no anonymous source implementation or native Pi keyword.
Ordinary function/method signatures cannot depend on other parameters or
on this's field values: accept and return a named class containing those
relationships. A fixed Type-returning function may still compute a type value
without having an argument-dependent result type. Constructor `A a` uses schema field A's declared type, not its unknown value.
`B b` uses a class TypeDef specialized by earlier schema bindings, mapping
A to a. Aliases have no runtime/default/const storage and cannot be assigned
through `this`. This ordered schema exception does not apply to ordinary funcs.
See [ordered contracts](./dependent_classes.md) for complete examples.

Functions and methods are registered before checking bodies, allowing forward
calls and recursion. Runtime globals of their package/ancestors are accessible
under visibility rules. Referencing a global before initialization is a runtime
error. Parameters and locals have lexical scope; block locals may shadow outer
names. Every function must return a compatible value on every structurally
reachable path. Loops do not by themselves prove a guaranteed return.
Procedures and constructors can complete without an explicit return;
ordinary constructors return their fully initialized this instance.
`constructor func X(...) X` declares an unnamed constructor called as `X(...)`;
`constructor func X.name(...) X` declares a named constructor called as
`X.name(...)`. Constructor result types are mandatory: use the object target,
`Prop` for a data-schema proposition generator, or the generated proposition
(or equivalent builder alias) for evidence. Body completion may still
implicitly return complete `this`; an implicit result **type** is never allowed.
It can coexist with named constructors, but only one unnamed constructor is
permitted. Its presence does not restore default/literal/nil creation or
implicit Copy for controlled classes.
An explicit Prop generator returns an immutable proposition description;
an evidence specification's constructor returns its named target proposition's
proof, not a separate nominal evidence-specification type.
Constructors may explicitly annotate their own target or `Prop` after the
parameter list; this constructor-only annotation is not ordinary function syntax.

## Packages and visibility

```text
package geometry;

public class Point { Int x; Int y; }
public class Functions {}
static func Functions.helper() Int { return 42; } // private
public func Point.sum() Int { return this.x + this.y; }
```

```text
package geometry.tools;
public class Functions {}
public static func Functions.label() Int {
    return geometry.Functions.helper(); // parent-private access
}
```

```text
package app;
import geometry;
import geometry.tools;
```

Header semicolons are optional; ordinary statements and fields require them.
Packages are exact dot-separated namespaces, not textual prefix matches.

- All declarations and fields are private by default.
- Private names/fields are visible in their package and descendant packages.
- Child packages automatically see ancestor declarations, including private ones.
- Parents and siblings have no automatic access to child/sibling declarations.
- An unrelated package must import the exact declaring package and can use
  only its public declarations.
- Importing `geometry` does not import `geometry.tools`, or vice versa.
- Imported names are not automatically re-exported. Qualified spelling does
  not bypass an import or privacy requirement.
- Conflicting unqualified imported names are an error; use their full names.
- Package dependencies initialize in order. Missing imports, duplicate packages,
  and dependency cycles are errors.

A public class does **not** make its fields public. A public method can use
its private fields internally. Every parameter, return, receiver, and static-owner type in
a public function signature must be public. Implementation-local helper types
can remain private. Function-type signatures recursively check domains and codomains. Retained
dependent signature paths cannot expose private fields or declarations.

### Supplying multiple packages

`run_source(entry, packages)` and `POST /api/run` accept:

```json
{
  "source": "package app; import math; print(math.Operations.answer());",
  "packages": {
    "math": "package math; public class Operations{} public static func Operations.answer() Int{return 42;}"
  }
}
```

Every supplied source must declare the corresponding package name. No host
filesystem imports occur. The browser's package-source map has the same shape.
The result includes `packageGraphs`, runtime variables and an object table.
Aliased variables/fields refer to the same object-table ID.
Integers outside JavaScript's exact range are exported as decimal strings
so the browser does not round their values; very large ones use an explicit
bit-count display. Their language type remains Nat or Int.

## Description and checking stages

1. The tokenizer reads characters and stores raw UTF-8 bytes in token nodes.
2. Lark's LALR grammar actions construct category nodes directly.
3. Semantic checking resolves packages, types, fields, functions, and methods.
4. The runtime interprets checked descriptions with separate variable frames
   and class objects.

Grammar wrappers are explicit: no leading `?` inlining. The final Program
reaches both syntax and TokenSequence. All Node output slots are bound.
Logical children use real output slots; repeated targets, where needed, use
one physical link with an explicit logical-slot map. No interning chooses
whether two different occurrences must be the same node.

Bindings and inferred types are exported checker metadata, not extra
backward-only syntax edges. Cross-package bindings are resolved by semantic
declarations, not by assuming graph-local IDs are globally unique.

The stage explorers show rules projected from actual Lark definitions.
Rule-definition category symbols can be shared as visualization metadata;
that is not a tokenizer/composer reuse mode or a type-identity restriction.
Tokenizer-only inspection does not require grammar validity; grammar-only
inspection does not run typing or runtime.

## Formal named specification checking

[theory.md](./theory.md) describes the formal view of the same runtime
specification checker. `run_source(source, check_only=True)` and `/api/theory`
check named classes, TypeDef aliases, and their implementations without executing
source effects. A source `check` command also selects check-only behavior.
The theory page accepts a single source; package execution remains available
through the main playground.

The source graph retains fresh occurrence descriptions. The formal graph encodes
verified named judgments and transparent alias definitions. Alpha-equivalent or
computed-equal types may have distinct IDs; semantic Pi/static-lambda
normalization supports named implementations and explicit partial captures.
There is no source `fun`, `axiom`, or `def` syntax, and no unknown-name assumption
fallback. Canonical scalar types remain the same primitive-backed runtime types.
Reusable dependent functions are typed class fields established by constructors.
Checking descriptions in Prop does not construct evidence or introduce eliminators.

## Errors, bounds, and tests

All packages are parsed and type-checked before any execution. Every request
is private; no graph or buffered output is returned unless it succeeds.
The editor preserves and explicitly labels the previous successful result
after a rejected edit.

Playground budgets: 32000 characters per source, 32 additional packages,
128000 additional-source characters, 5000 tokens per source, 80 source nesting
levels, 1024 characters per numeric literal, 20000 graph nodes per source,
20000 execution steps, 64 call frames, 2000 print lines, and 100000 bits per
integer result. Very large displayed integers may use a bit-count placeholder.
These are resource limits, not mathematical overflow rules. There is no host
I/O, runtime code evaluation, raw pointers, or arbitrary filesystem imports.

```sh
.venv/bin/python -m unittest node.test_layer0 node.test_animation nod.test_language nod.test_objects nod.test_dependent_classes nod.test_generated_propositions nod.test_stages nod.test_server nod.test_checking
elan run leanprover/lean4:v4.35.0 lean nod/theory_reference.lean
```

Examples: [example.nod](./example.nod), [package_example.json](./package_example.json),
and [theory_example.nod](./theory_example.nod), plus [dependent_example.nod](./dependent_example.nod)
and [proposition_example.nod](./proposition_example.nod).
Not implemented: full Lean elimination/induction, symbolic universe levels,
symbolic generator fields with unresolved runtime arguments,
arbitrary type-level effects, full dependent constructor flow inference,
collections, implicit conversions, `for`, global type aliases, package import aliases,
and native inductive/theorem declarations.
