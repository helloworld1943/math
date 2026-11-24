# Layer 2: small language, imported operations

This is a discussion draft, not an implemented parser or a final keyword list.

Our goal is to keep Layer 2 small. It provides the common ways to write
declarations, expressions, imports, and control flow. Libraries provide most
types, values, and operations.

For example, importing `math` makes `math.Float` and its exported arithmetic
available. Layer 2 understands the spelling `+`; the imported library provides
the applicable addition operation.

The graph foundation is described in [Layer 0](../layer0/layer0.md) and
[Layer 1](../layer1/nodetype.md). Some of their conceptual designs are still
pending implementation. This draft does not add those missing features.

## 1. The boundary

| Layer 2 provides | An imported library provides |
|---|---|
| `import` syntax and rules for using imported names | Module exports such as `math.Float` |
| Variable declarations and assignment syntax | The types and values used by those declarations |
| Common operator notation and precedence | The operations that the notation refers to |
| Control-flow forms such as `while` | Applicable comparison operations and condition values |
| Function-writing and application notation | Particular functions such as addition or differentiation |

We do not silently import a mathematical library. A type or operation is
available only if declared locally or made available by the import rules.

Importing a library does not let it bypass Layer 1's checks or redefine
the basic meaning of control flow.

## 2. A small example

This illustrates the intended style; it is not runnable yet:

```text
import math;

x : math.Float = 0;
while (x < 10) {
    x = x + 1;
}
```

Layer 2 supplies:

```text
import
declaration and assignment forms
while
operator notation
blocks and statement separators
```

The imported module supplies:

```text
Float
applicable addition and comparison operations
construction of the literal values required by those types
```

We initialize `x` before reading it. Merely declaring `x : math.Float`
does not provide an initial value.

## 3. Keywords discussed so far

These are words with language meaning, unlike names exported by a library.

| Keyword | Role | Status |
|---|---|---|
| `import` | Make selected module exports available | Requested |
| `while` | Repeat a block while a condition holds | Requested |
| `if` | Select a branch using a condition | Recommended for the first version |
| `else` | Provide the other branch | Recommended with `if` |

The exact import form, condition rules, and lowering of loops are not yet
defined. The table is a starting point, not a promise that all four features
already work.

## 4. Possible keywords, not decided

| Candidate | Why it might be useful | Why it can wait |
|---|---|---|
| `break` | Exit a loop early | We can first define a simple while loop |
| `continue` | Start the next loop iteration | Needs precise loop behavior |
| `for` | Convenient iteration | May be shorthand over a smaller iteration mechanism |
| `return` | Exit a function with a value | We may initially use expression-bodied functions |
| `fn` or `fun` | Introduce a function | The function-writing form needs a separate decision |
| `match` or `switch` | Select by a value or constructor | Layer 1 does not yet supply general inductive case analysis |
| `as` | Give an imported module or name an alias | We can initially use qualified names |

Do not reserve several words for the same purpose in advance. For example,
we should decide whether `match` or `switch` is needed rather than adding both.

We do not yet need keywords for `Float`, `Nat`, `Matrix`, `add`, `sin`,
or `differentiate`. Those can be library names.

## 5. Common notation, not additional keywords

| Notation | Proposed role | What it does not imply |
|---|---|---|
| `:` | A declaration's supplied type | Does not introduce a built-in numerical type |
| `=` | Initialization or assignment | Does not mean mathematical equality |
| `;` | End a statement | Does not define a value or operation |
| `.` | Qualify a name, as in `math.Float` | Member access beyond module names is not decided |
| `(...)` | Group an expression or supply function arguments | Calling syntax does not define the function |
| `{...}` | A block of statements | The block's scope and value rules still need defining |
| `,` | Separate arguments or parameter entries | Does not provide hidden arguments |
| `+`, `-` | Addition/subtraction notation, including possible unary forms | Need applicable visible library operations |
| `*`, `/` | Multiplication/division notation | Need applicable visible library operations |
| `<`, `<=`, `>`, `>=` | Comparison notation | Need applicable visible comparison operations |
| `==`, `!=` | Value comparison notation | Not automatically the type checker's definitional equality |

Operator precedence and associativity belong to the language specification.
The operation selected for those operands comes from the visible definitions.

For example:

```text
x + y
```

may resolve to an imported addition function. This does not hard-code the
definition of integer, matrix, or symbolic addition into the grammar.

Recognizing an operator token without an applicable operation should be an
explicit error, not a silent fallback to built-in mathematics.

## 6. Numbers and symbolic notation

The parser can recognize spellings such as `1` and `1.5` without deciding
that every number is a built-in Float or Nat.

We still need a rule for selecting the imported type and operation that
constructs a literal. In a declaration such as `x : math.Float = 1`, the
supplied type can guide that selection. Untyped literals and conflicting
literal providers need an explicit policy.

Similarly, an unknown name is not automatically a mathematical symbol.
A symbolic library may provide an explicit way to create the symbol `x`.
If we later offer more convenient symbolic notation, its interpretation
must be specified instead of silently disabling name checking.

## 7. Import and operator questions

Before implementing, decide:

- Does `import math` expose only `math.name`, or also selected unqualified
  names and operators?
- How does an imported library make an operation applicable to `+` or `<`?
- What happens when two imports provide applicable operations?
- How are literal values constructed when the expected type is known or unknown?
- Which exports are public, and which remain private to their module?

Using `math.Float` as a declaration type must not implicitly import arbitrary
unrelated modules. Mathematical operations should remain tied to explicit
visible definitions.

Package downloading, version selection, and caching are tool concerns;
they do not each need a new keyword in the source language.

## 8. Control flow needs meaning, not just spelling

`while` is a language construct. Its condition may call imported comparisons,
but the language must specify what it means for the condition to hold.
An arbitrary number or symbolic expression should not silently be treated
as true or false without an agreed rule.

We also need to specify assignment and state changes. The current Lambda
core does not by itself provide mutable storage or unrestricted execution
loops. A loop in an executable program must not accidentally run forever
inside the logical type checker.

These are required design decisions before implementation, not reasons
to add many keywords.

## 9. Suggested first discussion order

1. Agree on the import and qualified-name rules.
2. Define declaration, initialization, and assignment.
3. Define the function-writing and application forms.
4. Define how imported operations and literals are selected.
5. Define conditions, `if` / `else`, and a basic `while`.
6. Add another keyword only when a concrete example needs it.

The principle is:

> Layer 2 supplies a small set of writing and control-flow rules.
> Imported libraries supply the types and particular computations.
> Common notation makes those library operations convenient to use.
