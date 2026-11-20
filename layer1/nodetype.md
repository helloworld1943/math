# Layer 1: initial node types

[Layer 0](../layer0/layer0.md) gives us nodes, directed links, a root, and
visibility. Layer 1 gives meanings to arrangements of those nodes.

Layer 1 provides a fixed, limited set of relation kinds and their checking
rules. Users choose from those kinds and supply arguments. They do not define
new relation kinds or provide their own Python checkers in the target language.

The initial node types are listed below.

| Node type | Meaning |
|---|---|
| `Relation` | A check with explicit inputs, using a primitive kind or a graph decomposition |
| &nbsp;&nbsp;`HasType` (Type relation) | A Relation kind: node `x` has supplied type `T` |
| &nbsp;&nbsp;`BetaReduces` | A Relation kind: an application reduces to the supplied result in one beta step |
| &nbsp;&nbsp;`ValidInductive` | Checks an inductive declaration and all its constructor signatures |
| `RelationAnd` | Combines child Relations: all must hold |
| `RelationOr` | Combines child Relations: at least one must hold |
| `Context` | Groups information and owns Variable declarations; relevant constructs explicitly use a Context |
| `Universe` | A primitive universe with a non-negative integer level `n` |
| `TypeNode` | A reusable type description with a function, variable, or application form |
| &nbsp;&nbsp;`function` form | A parameter, domain, and possibly dependent codomain |
| &nbsp;&nbsp;`variable` form | A reference to a Variable standing for a type |
| &nbsp;&nbsp;`application` form | A reference to an ordinary Application describing a type |
| `Variable` | A declaration owned by one Context, with a Layer 0 identity, associated `HasType` Relation, and optional display name |
| `Parameters` | Organizes ordered Variable declarations and the Context they establish |
| `LambdaBody` | Connects an available Context to the expression describing a Lambda's computation |
| `Lambda` | A function expression connecting a Parameters node and a LambdaBody node |
| `Application` | A function expression applied to an argument expression |
| `Inductive` | Introduces a type identity, shared Parameters, declared type, and InductiveBody |
| `InductiveBody` | Points to the Context declaring this inductive's constructors |

The indented rows describe Relation kinds or TypeNode forms.
Parameters and LambdaBody are separate node types, not forms of Lambda.
The name Parameters stays general because inductive declarations can reuse
the parameter-list structure.

These are still nodes in the Layer 0 graph. This document defines their
meaning. The first implementation and its graph encoding are described in
[layer1.md](./layer1.md). A [visual walkthrough](./animation.html) shows the
implemented examples separately from design-only concepts.
AND/OR evaluation is implemented through Relation
parents and their combination nodes. Context-owned declarations and Parameters
are implemented for the inductive fragment described below. General Context
declarations and the Lambda migration remain unfinished; the existing Lambda
API still has one identity-only variable, domain, and body. LambdaBody is
still conceptual.

## 1. Relation

A Relation is a node with:

```text
Relation
    identity:  already provided by Layer 0
    arguments: an ordered list of links to nodes

    check:
        primitive kind identifying its Python checker
        OR decomposition pointing to RelationAnd / RelationOr
```

The parent has no extra AND/OR kind or operator field. The combination node
alone identifies the logical operation. Primitive Relations retain their
provided kind names, such as `HasType`.

It has no graph output. When we require the relation, we mean that it must
be true.

For example:

```text
r1: Relation
    kind = HasType
    arguments = [x, A]
```

This says: `x` must have type `A`.

The node states the requirement; it does not make the statement true without
checking it.

### HasType: the Type relation

`HasType` is our first provided Relation kind. It is not a separate basic
node type: a Type relation is a Relation node whose kind is `HasType`.

It has exactly two arguments, in this order:

```text
HasType [x, T]
```

| Input | Meaning |
|---|---|
| `x` | The node whose type we are checking |
| `T` | A supplied TypeNode, or a type expression used directly |

This asserts: "x has type T." Both `x` and `T` are supplied.
The relation checks the proposed type; it does not find a type or produce
an output node.

There are two different things here:

```text
T: TypeNode
    form = function, variable, or application
    ...connections for that form...

r: Relation
    kind = HasType
    arguments = [x, T]
```

`T` is an object that can be referenced and passed around. `r` is the check
that `x` has the type described by `T`. Creating `T` does not prove that the
expression it contains is a valid type or that the relation holds.

The checker interprets the TypeNode's form when checking. Universe nodes and
ordinary type-valued expressions can also be supplied directly.

Type comparisons use beta reduction and function eta equality. In a
well-typed comparison, `lambda x. f x` equals `f` if `x` does not occur free
in `f`. The check accounts for binding and adjusts outer references when
removing the extra binder. This equality is used both when comparing a
supplied type and when matching an application argument to a domain.
It does not change `BetaReduces` into a general equality Relation.

```text
r: Relation
    kind = HasType
    arguments = [x, T]
```

These are argument positions, not new Layer 0 link labels. The checker uses
Layer 0's visibility rule for the supplied nodes.

The first checking case is the Universe rule:

```text
HasType [U(n), U(n + 1)]
```

For supplied Universe nodes, their levels must differ by exactly one:

```text
HasType [U(0), U(1)]   holds by the Universe rule
HasType [U(0), U(0)]   fails
HasType [U(0), U(2)]   fails under this rule
```

We have not added a rule allowing a universe to be assigned any higher level.
This case needs no Context. TypeNode is described in section 10, Variable
declarations in section 11, and functions and applications in section 12.

Being a type is not a permanent separation between two groups of nodes.
For example, `U(0)` is a type and also has type `U(1)`. A function application
may also be used as a type when its type is a Universe.

For a Variable declaration, an associated `HasType [x, A]` records its declared
type. This is different from proving a later typing claim using that
declaration. The declaration must be allowed by its binding owner, and `A`
must be a valid type there. Following a link to the same Relation is not a
proof that it holds. The declaration checks are described in section 11;
the complete rules for Context assumptions still need to be specified.

### BetaReduces: checking one computation step

```text
BetaReduces [application, suppliedResult]
```

The application must directly apply a Lambda. The supplied result must be its
body with the argument substituted for that Lambda's variable, preserving
other bindings:

```text
Apply(Lambda(x, A, body), argument)
    -> body[x replaced by argument]
```

Both expressions are supplied graph nodes. The Relation produces no output
node and does not change the original Lambda or Application.

This checks one beta step, not complete evaluation or typing. A beta step can
be structurally correct even when the application is ill-typed; use `HasType`
to check typing separately.

Variable-form and application-form TypeNodes follow their referenced
expressions in this comparison. That does not count as another beta step or
compute away further applications. A function-form TypeNode retains its
parameter, domain, and codomain structure. `BetaReduces` alone does not
certify the validity of type descriptions.

### Graph composition

```text
Relation                         Relation
    inputs -> explicit nodes         inputs -> explicit nodes
    decomposition                    decomposition
        -> RelationAnd                   -> RelationOr
            -> child Relations               -> child Relations
```

RelationAnd requires every operand Relation to hold; RelationOr requires at
least one. Each child may be a primitive Relation or another decomposed
Relation. There are no separate parent relation kinds repeating AND or OR.

The parent explicitly lists all input nodes needed by its children. The
checker requires each child's input list to use only nodes listed in that
parent's inputs. The parent may list extra inputs, repeat inputs, or reorder
them; no new child input is silently discovered.

The parent inputs are expression nodes in this implementation. Child
Relations are separate decomposition operands, not expression inputs.

```python
choice = program.any_of(x, A, B, relations=(r1, r2))
both = program.all_of(x, A, B, relations=(r3, choice))
```

`all_of(...)` and `any_of(...)` are convenience constructor names. Both
return ordinary Relation parents and create the corresponding combination
node. They do not define additional relation kinds or compute a Boolean
result while building.

`HasType` and `BetaReduces` remain primitive. Attaching an AND/OR group to
either does not redefine it and is rejected as malformed structure.
Decomposing their internal typing or reduction rules into graph proofs is
future work; combining existing checks is implemented now.

## 2. Layer 1 supplies the kinds and checking rules

The kind identifies a checking rule supplied by Layer 1:

```text
HasType     -> checking rule for HasType
BetaReduces -> checking rule for a single beta step
```

Decomposed Relations instead use the shared Layer 1 logic of their
RelationAnd or RelationOr node. No additional primitive kind is needed.

`SameNode` would be another possible kind with a primitive Python check;
we have not defined its details here.

A kind name uniquely identifies its rule within the checking system.
Different nodes can have the same kind:

```text
r1: HasType [x, A]
r2: HasType [y, B]
```

`r1` and `r2` are different node identities. `HasType` is the kind they share,
not a unique name for each particular node.

The system supplies the meaning of each kind. Its check can be expressed by
a graph decomposition or, when not decomposed, an associated primitive Python
computation. Users cannot replace that meaning, attach arbitrary Python code,
or introduce a new kind just by writing a new name. An unknown kind is an error.

There is no user-facing `RelationDefinition` or `RelationUse` node type.
Users simply create a `Relation` of a provided kind and connect its arguments.
The rule for that kind belongs to the Layer 1 implementation.

The implementation provides `HasType` and `BetaReduces` as primitives and
supports graph decompositions with RelationAnd and RelationOr.
Adding another built-in kind means extending Layer 1,
not declaring a new relation inside a user's program.

## 3. Inputs

The argument list can have any finite length. A particular kind can require
a particular number of arguments or specify which lengths it accepts.
`HasType` and `BetaReduces` each require exactly two.
Decomposed Relations accept explicit input lists of varying length. Their
decomposition operand lists must be nonempty.

Order and repetition matter:

```text
R [nodeA, nodeB]
R [nodeB, nodeA]
R [nodeA, nodeA]
```

The last example has two positions pointing to the same node. It does not
collapse into one argument.

Layer 0 has unordered links and does not store duplicate links. Layer 1 must
therefore represent argument positions explicitly.

## 4. No graph output, but a Boolean checking result

Checking a Relation, either through its decomposition or through a primitive
computation, answers:

```text
True  -> the relationship holds
False -> the required relationship fails
```

This Boolean is a result used by the validator. It is not an output node or
a value passed to other expressions in the target program.

A Python exception, timeout, or computation that never finishes is not a
false result. Execution errors must be reported separately.

## 5. Visibility

A checker may read its explicit argument nodes and all their outgoing
descendants. It may not read unrelated nodes, change the graph, or depend on
hidden outside information such as the clock or randomness.

The same fixed graph, arguments, and checking rule should give the same
answer whenever the check finishes.

The kind's association with Python code does not grant whole-graph access.
A context, if needed, is an explicit argument rather than a hidden environment.

## 6. Context

A Context is a node with:

- A parent connection.
- Multiple outgoing connections to nodes.

```text
parent
    -> Context
        -> node A
        -> node B
        -> ...
```

The outgoing connections group nodes; they are not computed return values.
The parent does not have to be another Context, and the outgoing connections
are not limited to declarations.

### Nodes that require a Context

Context is already a node type. We do not need a new Plain node type or
make the root itself a Context.

Layer 1 requires Context connections for these structures:

| Structure | Required Context |
|---|---|
| The designated root | A global Context for program declarations |
| `Parameters` | A Context for its ordered parameter declarations |
| `LambdaBody` | The Context available to its body expression |

```text
root       -> global Context
Parameters -> parameter Context
LambdaBody -> available Context
```

These are outgoing connections from the structures to Context nodes.
"Under" a node means connected this way, not a reverse link from the
Context to the root or a new Layer 0 node kind.

This does not mean creating a separate copy of every declaration for each
use. LambdaBody can point to the Context established by Parameters, or to
an extended Context if the body has additional declarations.
Other structures may require Contexts as their rules are defined.
We do not add one automatically to every graph node.

The root's Context connection is a Layer 1 requirement. Layer 0's root
continues to be just a designated graph node with no incoming links.
Parameters and InductiveBody now have checked Context connections in the
inductive fragment. The global-Context root convention and LambdaBody Context
API are not implemented yet.

Visibility follows Layer 0's rules. Context adds no separate visibility or
inheritance rules.

A Relation can take a Context as an ordinary explicit argument. There is no
hidden "current context."

A Context does not automatically prove that its connected information is
valid or true. Typing, assumptions, and variable scope need their own checks;
they are not built into this basic Context structure.

A Context is the sole declaration owner of a Variable. Lambda, Parameters,
LambdaBody, function-form TypeNode, and inductive declarations do not directly
own Variables; they use Contexts containing the declarations they need.

```text
C: Context
    -> x: Variable
        -> r: Relation
               kind = HasType
               arguments = [x, A]
```

This declares `x : A` in `C`. `A` is a supplied type expression, not
necessarily a Universe node. For example, a Context may declare `A : U(0)`
and then `x : A`, without supplying a value for either variable.
The relationship to an owner must be identified explicitly; merely being
reachable from a Context does not make every descendant its declaration.

### Declaration owner versus available Context

Each Variable is declared in one Context. Another Context may include that
earlier Context without taking ownership of its declarations:

```text
C1 -> earlier Context C0
 |
 -> new declaration x
```

`x` is owned by `C1`. Declarations owned by `C0` remain owned by `C0`.
References to a Variable also do not change its owner.

This organizes information using Layer 0 links; it adds no separate
visibility rule. The checking rules still decide which declarations can
legally be used. A link to a Context is not proof that every reference in an
expression is allowed.

Relevant constructs explicitly use an available Context. Not every node
needs a Context field:

```text
LambdaBody
    context    -> available Context
    expression -> body expression
```

Parameters establishes the Context for a LambdaBody. A function-form TypeNode
uses a parameter Context when checking its codomain. An inductive declaration
can similarly use a Context for its parameters and constructor signatures.
The exact encodings and validation rules for these Context uses remain to
be implemented.

## 7. Two ways to check a Relation

### Graph decomposition

A composite Relation is decomposed into smaller Relations using `RelationAnd`
and `RelationOr`. The parent is an ordinary Relation without a primitive kind.
The decomposition is expressed in the graph, not hidden inside a separate
Python checking program for that parent Relation.

```text
R: Relation
    -> RelationAnd
        -> R1: Relation
        -> R2: Relation
            -> RelationOr
                -> R3: Relation
                -> R4: Relation
```

This means `R` requires `R1 AND R2`, and `R2` requires `R3 OR R4`.
The argument connections are omitted from this picture for clarity.

Every argument in the decomposition must come from the outer parameters.
If a smaller relationship needs another object `d`, include `d` in the
outer interface. We do not search for a missing witness.

### Primitive computation

When a Relation is not decomposed, its associated primitive Python computation
checks it. "Primitive" means we stop decomposing at this point, not that the
Python computation has no smaller steps.

```text
Relation
    either:
        graph decomposition using RelationAnd / RelationOr
    or:
        associated primitive Python check
```

Layer 1 provides the common AND/OR evaluation rules once. We do not write a
custom Python program for each parent Relation just to combine its children.
The Layer 1 engine may itself be written in Python; that is different from
hiding each decomposition inside a primitive computation.

## 8. RelationAnd and RelationOr

Within the decomposition structure:

- A `RelationAnd` or `RelationOr` has a parent of type `Relation`.
- Its outgoing operand connections point only to Relations.
- There are no direct operand connections from `RelationAnd` or `RelationOr`
  to another `RelationAnd` or `RelationOr`.
- Nested combinations go through a child Relation, as in the picture above.

The constructors create one combination node per parent. Within a checked
decomposition, the checker rejects a combination shared by two different
owners. A Relation operand may itself be reused.
These are semantic connections; ordinary root links and encoding helper
nodes do not become additional decomposition parents or operands.

```text
Relation                    Relation
 -> RelationAnd              -> RelationOr
     -> Relation A               -> Relation A
     -> Relation B               -> Relation B
```

The common Layer 1 rules are:

```text
RelationAnd: every child Relation must hold.
RelationOr:  at least one child Relation must hold.
```

These nodes have no Boolean output connections in the program graph. Their
operand links describe required checks, not computed output values.

Requiring a parent with a `RelationOr` decomposition does not mean requiring
all the alternatives separately. An unsuccessful alternative is allowed if
another alternative succeeds.

The decomposition must still describe the parent's provided relationship;
attaching an unrelated true Relation must not change the parent's meaning.
This does not require a separate Python program to perform each AND/OR
combination. A decomposed parent must point to a RelationAnd or RelationOr;
that node is the sole choice of AND versus OR. A primitive parent cannot
have a decomposition attached as a substitute for its provided checking rule.

The implementation stores operand lists in order and preserves repetitions.
It checks the reachable Relation topology and explicit input lists before
running primitive checks, including topology in alternatives that may later
be skipped. Empty combinations, cycles in list structure, and cycles in
Relation dependencies are errors, not successful proofs.

Evaluation then proceeds left to right with short-circuiting. RelationAnd
stops at the first false child; RelationOr stops at the first true child. A shared Relation
is evaluated at most once per validation request. Primitive checks in skipped
branches are not run, so their expression checks and possible execution
errors are not observed in that request.

An evaluated primitive returning a false relationship can be an unsuccessful
alternative. An evaluated primitive raising an encoding error, execution
error, or work-limit error does not count as false: the error propagates.
One work budget covers topology checking and evaluation.

## 9. Universe

A Universe is a primitive Layer 1 node type:

```text
Universe
    n: a non-negative integer
```

We write the universe at level `n` as `U(n)`:

```text
U(0), U(1), U(2), ...
```

The level can be any non-negative integer. There is no fixed upper bound,
but each level is finite: infinity is not a level value.

A universe is a type whose elements are types. The basic typing rule is:

```text
U(n) : U(n + 1)
```

For example:

```text
U(0) : U(1)
U(1) : U(2)
```

Using the Type relation, this is expressed as:

```text
HasType [U(n), U(n + 1)]
```

The two universe nodes are supplied explicitly. The checker verifies their
levels; it does not produce the next universe as a graph output.
`U(n) : U(n)` is not allowed by this rule.

Supporting an unbounded range does not require infinitely many nodes in a
program. A finite program graph contains only the universe nodes it needs.

The level `n` belongs to Layer 1, not to the Layer 0 node object. The first
implementation stores it as a finite binary chain of helper nodes.

### Universe versus Variable, and Lean's Prop

We currently keep Universe primitive, not a form of Variable.
Its level has fixed meaning: `U(n) : U(n + 1)`.

A Variable `A : U(n)` is an object in that universe. The universe is its
declared type, not its binding owner. Its declaration owner is a Context,
including when it is used as a function or inductive parameter.

In Lean, `Prop = Sort 0` and `Type n = Sort (n + 1)`. Our `U(n)` currently
behaves like `Type n`, not `Sort n`. Thus our `U(0)` is not already Prop.
Lean gives Prop special function-type, proof-equality, and inductive
elimination behavior. Renaming `U(0)` would not implement those rules.

The [quantifier and universe examples](./layer1.md#12-quantifiers-existential-style-packages-and-prop)
show these differences using independently compiled Lean examples and
matching graph tests. This is a recommendation to retain the current
primitive Universe for now, not a decision to add Prop or change its rules.

## 10. TypeNode and type checking

A TypeNode describes a type using one of three forms:

```text
TypeNode
    form = function
        variable -> x
        domain   -> A
        codomain -> B

    OR form = variable
        variable -> A

    OR form = application
        expression -> an ordinary Application
```

A TypeNode has its own Layer 0 identity. Other nodes can share it. The form
names are provided by Layer 1, not user-defined node kinds.

There is no longer a separate `FunctionType` graph node kind. Its structure
is now the function form of TypeNode. There is also no generic wrapper
around an arbitrary expression.

### A type object versus a checking computation

```text
TypeNode:
    an explicit object describing a type

HasType:
    a Relation whose computation checks a supplied typing claim
```

The TypeNode is not a checker or a proof, and the checking result is not a
TypeNode. Type checking runs in Layer 1; from the target language's point of
view, it can still be a static check before program execution.

### Function form

```text
T: TypeNode
    form = function
    variable -> x
    domain   -> A
    codomain -> B
```

This directly describes `(x : A) -> B`. `B` may refer to the parameter `x`.
It describes a function type, not an executable Lambda.

### Variable form

```text
T: TypeNode
    form = variable
    variable -> A
```

`A` must be a Variable standing for a type, such as a parameter declared as
`A : U(0)`. A Variable holding an ordinary function value does not qualify.
Creating this form does not prove that `A` is in scope or has a Universe
type; the check must establish those facts.

### Application form

```text
T: TypeNode
    form = application
    expression -> Apply(F, a)
```

This explicitly describes a type using computation, such as `F a`. The
referenced Application must have a Universe as its type. An application
returning an ordinary value does not become a type merely because a
TypeNode refers to it.

The form points to an existing Application; it does not duplicate its
function and argument links or introduce different application rules.
The result need not first be given a Variable name.

### Universe stays primitive

`U(n)` remains a Universe node, not a fourth TypeNode form. It can be
referenced or passed directly wherever that universe is a valid type
expression:

```text
HasType [U(0), U(1)]   holds
HasType [U(0), U(0)]   fails
```

TypeNode forms must also describe types with Universe types when checked.
Cycles in expression/type-description structure are invalid here, even though
Layer 0 allows graph cycles in general.

### Reusing and passing types

A TypeNode can be used as a function domain or codomain, as a supplied type
in a Relation, or as an argument when the function accepts that type object.

```text
T: TypeNode
    form = function
    variable -> x
    domain   -> U(1)
    codomain -> U(1)

function f's domain -> T
function g's domain -> T
HasType [someExpression, T]
```

There is no need to copy the type expression for each use.
Outgoing visibility follows the TypeNode's fields and their descendants, not
backward to all its users.

### No mandatory type field on Lambda or Application

An Application still has only function and argument connections. A Lambda
conceptually connects to Parameters and LambdaBody nodes. The parameter types belong
to the declarations in Parameters, rather than separate outer Lambda fields.
Neither expression needs an attached
result-type field or an automatically created `HasType` Relation.

When checking a particular result type matters, supply the type object and
the Relation explicitly:

```text
HasType [lambdaExpression, functionTypeObject]
HasType [applicationExpression, resultTypeObject]
```

Layer 1 must check that the function and argument fit. It may compute a
temporary result type on demand, but automatic inference is not a requirement
of these graph node definitions. The current primitive checker does use
internal inference to verify the supplied claim. It does not publish an
inferred type node or add one to the graph.

### Construction and validation

```python
function_type = program.function_type(variable, domain, codomain)
variable_type = program.type_node(type_variable)
computed_type = program.type_node(type_application)
```

`function_type(...)` now returns TypeNode with `form = function`.
`type_node(variable)` and `type_node(application)` create the other forms.
`type_node(existingTypeNode)` and `type_node(universe)` return the same
existing node; they add no wrapper or new form. `type_node(lambda)` is
rejected because a Lambda describes a function value, not a type.

Constructors check input node kinds. Commit checks Layer 0's root rules,
not whether every type description is valid. Use `HasType` to check a
supplied type claim. For example, an application form referring to an
application returning a function value can be stored, but fails a typing
check as a type description.

## 11. Variable

The fuller Variable design is:

```text
Variable declaration
    declaration owner: Context
    identity:      provided by Layer 0
    declared type: associated HasType Relation
    display name:  optional
```

`Variable` is the node's kind. Its declared type can be a TypeNode in one of
the three forms, a Universe, or a directly supplied type-valued expression.
The type object is separate from the Variable's node kind.

### Declaration owner

Each Variable declaration belongs to exactly one Context. Other constructs
refer to that Context, or a later Context that includes it.
Parameters organizes parameter declarations; LambdaBody uses the available
Context. Neither becomes the declaration owner.

For example:

```text
Lambda
    parameters -> Parameters
                      context -> C
    body -> LambdaBody
                context -> C
                expression -> expression using x

C: Context
    declaration -> x: Variable

x: Variable
    declared typing -> r: Relation
                           kind = HasType
                           arguments = [x, T]

T: TypeNode
    form = variable
    variable -> A
```

For a Lambda, the parameter's required type comes from its declaration in
the Context established by Parameters. The current code still stores a
domain directly on Lambda and must eventually be migrated to this structure.
For a function-form TypeNode, the parameter's Context declaration and the
function domain must agree.

A function-form TypeNode is not an executable function, but it can still bind a
parameter:

```text
(x : A) -> B x
```

This describes a function type whose result type depends on its argument.
`B x` refers to the parameter `x` declared in the Context used by that
TypeNode. Compare:

```text
TypeNode, function form: (x : A) -> B x
Lambda:                  lambda (x : A). body
```

Both create a scope using Context declarations: the first uses `x` in a
codomain; the second uses `x` in a body. Their parameter declarations are
normally separate even if both are displayed as `x`.
Matching a Lambda to its function type matches those bound positions; it
does not require sharing the declaration node.

The owner is a particular Context declaration relationship, not every incoming link.
A reference to `x` points to the same Variable identity without becoming
another owner.

The exact encoding of the owner association is still open. In particular,
we do not automatically add `Variable -> owner`: such a link would grant
access to the owner and its descendants under Layer 0. No automatic reverse
link or new visibility rule is implied by the word "owner."

### Identity and display name

Layer 0 already gives the Variable a unique node identity. We do not need a
second mandatory ID within its Context.

The optional display name, such as `x`, is for people. Different declarations
can have the same display name without being the same variable. References
use node identity, not text matching.

### Associated HasType Relation

Each Variable declaration has a designated typing Relation:

```text
x -> r

r: Relation
    kind = HasType
    arguments = [x, T]

T: TypeNode
    form = variable
    variable -> A
```

The first argument must be that same Variable `x`; the second is its declared
type object `T`, which describes `A`. This gives access to the declared type
through the Variable's outgoing descendants. It does not store a runtime
value in `x`.

The argument link back to `x` makes a cycle, `x -> r -> x`. Layer 0 allows
that cycle. It is metadata about a declaration, not a circular proof or a
recursive expression body.

### Declaration versus checking

A declaration introduces a variable with a type; it does not have to supply
a value. For example:

```text
A : U(0)
x : A
```

Later checks may use these declarations only where the language allows them.
They must not justify `HasType [x, A]` merely by revisiting that same Relation.
The declaration must have an allowed Context owner and a valid type expression.
If a value is supplied by another construct, that value must also be checked
against the declared type.

For a Lambda, a parameter's declared type is checked using the Context
available before that declaration. It may refer to earlier parameters in
the list. The body uses the Context established by the completed list.
A function-form TypeNode likewise checks its domain before extending the
Context and checks its codomain with that parameter available.
A reference can occur beneath more nested
binders, but it cannot use another function's private parameter just because
there is a link to it. Context declarations need corresponding scope and
assumption checks, which are not yet defined.

Applying a Lambda substitutes its argument into the body; it does not mutate
the Variable to store a current value. A Variable `x : A` is not the identity
function `lambda (x : A). x`, whose type is `(x : A) -> A`.

### Current code versus this design

The current `variable()` API creates only an identity and a Variable marker.
For inductive declarations, the staged builder now adds a Context owner,
an associated HasType Relation, and a name for the introduced type and its
constructors. Shared inductive parameters receive Context ownership and
declared typing too. The existing Lambda and function-type constructors
still supply the domain separately and use identity-only binder nodes.
Existing Lambda examples may reuse a Variable node between a Lambda and its
function type; they demonstrate the earlier representation.

The current checker accepts only closed expressions, deriving local binding
information from enclosing Lambdas and function-form TypeNodes. It rejects a standalone
Variable or an out-of-scope reference. Inductive identities are additionally
checked as nominal constants introduced by validated declarations. This does
not provide general Context assumptions or the new Lambda declaration model.

### Parameters: a shared declaration structure

A Parameters node organizes an ordered list of Variable declarations and
the Context made available by those declarations:

```text
Parameters
    0 -> A: Variable, declared type U(1)
    1 -> x: Variable, declared type A
    2 -> h: Variable, declared type B x
```

Each entry's identity and associated HasType Relation are described above.
The right side of each declaration is a type description, not a value for
that parameter. Later declarations may refer to earlier ones.

For example, the first two entries establish:

```text
C0: earlier Context
C1: includes C0 and declares A : U(1)
C2: includes C1 and declares x : A
```

Check the declared type of `A` using `C0`, and that of `x` using `C1`.
The LambdaBody uses `C2`. This avoids using a parameter to justify its own
declaration. Each declaration stays owned by the Context that introduced it.
This prefix-Context structure is conceptual, not an implemented API. The
inductive builder instead stores one ordered parameter Context and validates
each entry with only the earlier entries bound in its temporary checking
environment.

The numbers illustrate list positions; they do not add numbered links to
Layer 0. The final encoding of the list is not yet chosen.

Parameters is not an expression with its own function type. It organizes
bindings and their Contexts; it does not replace their Context owners.
The construct using Parameters determines how the resulting Context is used.
The parameter-list structure can later be reused by function-form TypeNodes
and inductive declarations, with their own validation rules. Reusing the
structure does not mean sharing one Variable declaration between owners.
Inductive Parameters is implemented in the limited fragment below. Lambda
and function-type integration with this Parameters structure remains future work.

## 12. Lambda, function-form TypeNode, and Application

These have different roles:

```text
Lambda                         TypeNode, form = function
    parameters -> Parameters       variable -> x declared in C
    body       -> LambdaBody       domain   -> A
                                   context  -> C for the codomain
                                   codomain -> type expression B

Application
    function -> expression f
    argument -> expression a
```

These role names describe arrangements of plain Layer 0 links, not changes
to Layer 0 itself. The parameter's declaration is described in section 11.
Type descriptions in parameter declarations and function-type domains and
codomains can use the forms discussed above. Direct type expressions remain
accepted by the current API.

### Lambda is composed of two parts

```text
Lambda
    parameters -> Parameters node
    body       -> LambdaBody node
```

Parameters holds the declarations. LambdaBody points to the expression that
describes what to compute:

```text
LambdaBody
    context    -> Context established by Parameters
    expression -> Variable, Application, Lambda, or another allowed expression
```

The Context contains the declarations available to the expression.
LambdaBody does not introduce or take ownership of the Variables it uses.
LambdaBody does not duplicate that expression or add a computation rule. Parameters
and LambdaBody are explicit parts connected by Lambda. Layer 0 determines visibility
through these connections.

For example:

```text
Lambda
    parameters -> [A : U(1), x : A], establishing Context C
    body       -> LambdaBody
                      context    -> C
                      expression -> x
```

This describes `lambda (A : U(1)) (x : A). x`. A suitable function type is
`(A : U(1)) -> (x : A) -> A`, represented by the current nested function
forms. The checking rules relate the parameter declarations, body, and
supplied function type.

This change only separates the conceptual structure. Empty lists,
partial application, and the final graph encoding need explicit rules before
we migrate the current single-parameter Lambda implementation.

### Lambda and function-form TypeNode

```text
lambda (x : A). body
```

describes the function, whereas:

```text
(x : A) -> B
```

describes its type. `B` may refer to `x`; this is a dependent function type.

Each Lambda parameter must have a valid declared type. Its body must have
the codomain specified by the supplied function type, under the corresponding
bindings.

For a function-form TypeNode, if its domain has type `U(i)` and its codomain
has type `U(j)` under its binder, the TypeNode has type `U(max(i, j))`.
This is a simple predicative universe rule, not Lean's special `Prop` rule.

### Application

If `f` has type `(x : A) -> B`, then `a` must have type `A`, and the
application has type `B` with `a` substituted for `x`.

The function connection can point to another Application that returns a
function; it need not point directly to a Lambda.

There is one Application node kind, whether its result is a type, function,
or other value. It has no type field and needs no mandatory attached typing
Relation. When a result type is supplied for checking, it can be an explicit
TypeNode or a directly supplied type expression. There is no separate node
kind named "suppliedResultType."

## 13. First implementation

Run from the repository root:

```sh
python3 -m layer1.demo
python3 -m unittest -v layer1.test_core
python3 -m unittest -v layer1.test_type_node
python3 -m layer1.composition_demo
python3 -m unittest -v layer1.test_eta layer1.test_composition
python3 -m layer1.inductive_demo
python3 -m unittest -v layer1.test_inductive
```

This version implements the three TypeNode forms, Lambda, Application, Universe, the
identity-only Lambda variables and Context-owned inductive declarations,
three primitive Relations, and graph-decomposed
Relations using RelationAnd / RelationOr. A check
reads actual Layer 0 views restricted to its arguments and their descendants.

The implemented Lambda still stores one `variable`, `domain`, and `body`.
It does not yet store Parameters, LambdaBody, or their Context connections.
The implemented function-form TypeNode also lacks its conceptual Context.
Current executable
examples therefore use the old single-parameter API; the two-part Lambda
description above is the conceptual design, not an implemented feature.

The primitive `HasType` checker computes temporary type expressions and
performs beta/eta conversion internally. It does not create graph nodes, return
an inferred type, or silently supply a Context. `BetaReduces` checks a supplied
result with binding-aware substitution.

`function_type(...)` creates a function-form TypeNode directly.
`type_node(variable)` and `type_node(application)` create the other forms.
Typing checks validate their meaning. Substitution works through type
descriptions while preserving binding. The demo shows all three forms,
passes a type as an argument, and uses an Application as a type description.

For broader examples, run:

```sh
python3 -m layer1.lean_examples
python3 -m unittest -v layer1.test_lean_examples
```

These test higher-order functions, dependent families, type constructors,
and Church-encoded Booleans, arithmetic, and pairs. Matching examples in
[lean_examples.lean](./lean_examples.lean) were checked with Lean 4.35.0.
They do not require more graph node kinds.

The previously exposed function eta gap is now fixed and checked against the
matching Lean examples. Repeated expansion of shared graph structure can
still exhaust the work budget on a small graph.
See the [implementation guide](./layer1.md#10-broader-tests-before-building-layer-2)
for the tested cases, remaining limits, and readiness assessment.

The additional [logic examples](./logic_examples.py) test universal
quantification, existential-style packages, disjunction, and equality
transport using existing expressions. They are Type-valued encodings, not
implementations of native Lean `Prop`, `Exists`, `Or`, `Sigma`, or `Eq`.
The [Lean reference file](./logic_examples.lean) checks both the encodings
and native features so the difference stays explicit.

```sh
python3 -m layer1.logic_examples
python3 -m unittest -v layer1.test_logic_examples
```

The common graph decomposition engine and `RelationAnd` / `RelationOr` are
implemented with ordinary Relation parents. Inductive Contexts and declaration
metadata are now implemented, but general Context construction and the Lambda
Variable migration remain future work. This version does not claim that
primitive typing has been decomposed into graph-stored proof steps.

## 14. Inductive and InductiveBody

These nodes separate the declaration header from its construction rules:

```text
Inductive
    identity   -> Variable identifying the introduced type
    parameters -> Parameters
    type       -> full type-family signature
    context    -> Context declaring that type identity
    body       -> InductiveBody

InductiveBody
    context -> constructor Context
```

The body Context lists its constructor declarations and points to the
parameter Context. Each constructor is a Variable, with a name, a Context
owner, and an associated `HasType [constructor, signature]` Relation.
There is no new Constructor node type. Its role comes from membership in
this particular body's declaration list.

References to the introduced type use the variable form of TypeNode.
Applied type families use the application form. These references can create
cycles through the declaration. The checker treats them as nominal references,
not expression bodies to expand indefinitely. They do not mean that a type
has itself as its own type.

### Staged construction

```python
p = Program()
d = p.inductive("Nat", p.universe(0))
nat_type = p.type_node(d.identity)
zero = d.constructor("zero", nat_type)
x = p.variable()
succ = d.constructor("succ", p.function_type(x, nat_type, nat_type))
definition = d.finish()
```

`d.identity` is available while building signatures. `finish()` creates the
Parameters and Context structures and seals the declaration's fields.
It does not prove the declaration valid:

```python
claim = p.relation("ValidInductive", definition)
snapshot = p.commit()
snapshot.require(claim)
```

`ValidInductive` has one explicit argument. HasType also validates a
constructor's entire inductive definition before using its signature.
The attached HasType Relation is never accepted merely because it says
the constructor is well-typed.

### First supported fragment

- Finite parameter telescopes ending in a Universe.
- Named constructor declarations, including zero-argument constructors.
- Empty inductive types.
- Constructor arguments with dependent types and ordinary function types.
- Direct positive recursive fields such as `Nat` or `List A`.
- Unchanged shared parameters in recursive fields and constructor results.
- Constructor applications through the existing Application nodes.
- Computed signature types when they reduce to the supported structure.

The checker validates Context ownership, parameter ordering, signature types,
constructor names, result identity, and the field-universe size. A field's
type must live in a universe no higher than the result universe.
Negative recursive occurrences are rejected. Positive recursive function
fields and other recursion outside the direct fragment raise
`UnsupportedInductiveError`.

The introduced identities are nominal: two separate inductive declarations
with the same display name are not interchangeable.
Constructors do not have Lambda bodies and do not beta-reduce.

### Limits

There is no case analysis, recursor, induction rule, general indexed signature,
nested or mutual recursion, general Context assumption API, or inductive
universe polymorphism yet. This is declaration and constructor-application
support, not complete Lean inductive support.

The code still indexes `U(n)` as Lean `Type n`, so the example above uses
`U(0)` for a small data type. The agreed Sort/Prop indexing and universe-form
TypeNode migration are separate pending changes, not implemented by this
fragment. Layer 0 and the shared-graph performance limitation are unchanged.

See [inductive.md](./inductive.md) for complete examples, implementation
details, and the independent Lean counterparts.

## 15. What we still need to decide

- Which other relation kinds Layer 1 provides and which arguments each accepts.
- How to migrate to the agreed Sort/Prop universe indexing and universe
  TypeNode form, and implement Prop's special rules.
- How to extend the implemented inductive declarations with indices,
  additional recursion forms, case analysis, recursors, and induction.
- How to avoid repeated expansion of shared expressions during type checking.
- How to build Context, its declaration ownership, and the available-Context
  connections of relevant constructs using the encoding.
- How to encode Parameters and LambdaBody and migrate Lambda to those two parts,
  including rules for empty lists and partial application.
- How to encode a Variable's Context owner and optional display name, and
  implement its associated typing Relation.
- The complete rules for validating declarations and using Context assumptions
  without circular justification.
- Whether and how to decompose the provided primitive typing rules beyond
  the now-supported RelationAnd / RelationOr combination of checks.
- Whether to support recursive relation specifications with finite evidence.
  Circular Relation dependencies are rejected by the current evaluator.
- How a graph-stored relation requests global access. Layer 0 forbids links
  into the root, so an ordinary argument link cannot point to it. The host
  API can explicitly call `snapshot.view(snapshot.root)`, but the graph form
  of that request still needs a design.

External typing contexts, general recursion, and Layer 2 operations remain
outside this first version. We should not add fields for them, outputs, or
cached results to every Relation in advance.
