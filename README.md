# SMTLib-to-Lean

A tool to connect SMT-based frontends to Lean4.

## Feature tour

[demo.smt2](demo.smt2) covers the supported SMT feature families in five queries:
functions, Boolean operators, integer arithmetic, definitions, aliases, let bindings,
quantifiers and hints, named assertions, and push/pop scopes.
[demo-chc.smt2](demo-chc.smt2) adds recursive Horn rules, multiple relation premises,
mixed Bool/Int arguments, and safety clauses in three queries.

```sh
lake exe smt2lean demo.smt2 --out demo-output
lake env lean demo-output/Query.lean
lake exe smt2lean demo-chc.smt2 --out demo-chc-output
lake env lean demo-chc-output/Query.lean
```

Choose fresh output directories. Each file explains its queries and which goals
can hold; typechecking the generated `sorry` templates does not prove them.

## Translate a Boolean query

From the repository root, after installing the development tools below:

1. **Generate the Lean file.** Choose a new output directory:

   ```sh
   lake exe smt2lean tests/translation/bool/contradiction.smt2 --out boolean-demo
   ```

   This creates `boolean-demo/Query.lean`: **Statements** first, then **Proofs**
   with `sorry`. Compare it with the [expected output](tests/translation/bool/expected/Query.lean).

2. **Open `boolean-demo/Query.lean` in your Lean editor.** Check it from the terminal:

   ```sh
   lake env lean boolean-demo/Query.lean
   ```

   The `sorry` warning is expected: the statement is well-typed, but its proof is unfinished.

3. **Complete the proof.** Replace the Proofs section with:

   ```lean
   -- Proofs

   theorem refutation : Refutation := by
     intro p h
     exact h.2 h.1
   ```

   Here `h.1` proves `p`, and `h.2` proves `¬p`. Run the same Lean command again;
   it now succeeds without the `sorry` warning.

The file uses Lean core, without cvc5 or translator dependencies. This proof is for
the contradiction example; translation alone does not establish every query's refutation.

The output directory must be new, and its parent must exist. Existing proof work
is never overwritten. The translator validates the whole input and kernel-checks
the in-memory statement before writing the file. It does not solve the query or
prove the theorem.

Use `lake exe smt2lean --help` for usage. Exit codes are `0` for generation/help,
`2` for invalid arguments, and `1` for input, translation, or output errors.
The supported Bool/Int fragment is listed below.

Boolean operators follow [SMT-LIB Core](https://smt-lib.org/theories-Core.shtml).
`xor` accepts two or more Boolean operands and means an odd number are true.
`distinct` accepts two or more Bool operands or two or more Int operands and
compares every pair. Both work inside quantified formulas and CHC theory guards.
Generated files define each used operator helper once, above the query statement:

```lean
def SMT.xor (p q : Prop) : Prop := (p ∧ ¬q) ∨ (¬p ∧ q)
def SMT.distinct3 {α : Sort u} (x y z : α) : Prop := x ≠ y ∧ x ≠ z ∧ y ≠ z
```

The query then uses `SMT.xor p q` and `SMT.distinct3 x y z` directly.
`distinct2`, `distinct3`, etc. cover each argument count used in the input;
the same helper works for Bool and Int. Multi-operand xor uses nested calls.
Unused helpers are omitted. Definitions and calls remain in the same `Query.lean`,
importing only Lean core.

`(ite condition yes no)` supports Bool or Int branches of the same sort, including
nested conditionals, arithmetic, function arguments, and quantified SMT conditions.
It becomes Lean `if condition then yes else no`. CHC conditions remain relation-free
and quantifier-free, like other theory guards.

When a condition needs classical decidability, the generated definition uses
`noncomputable def` with a local `classical` block. Its only permitted axiom
dependencies are Lean's `propext`, `Classical.choice`, and `Quot.sound`.
Statements still reject `sorry` and query-specific axioms; classical decidability
adds no assumption about the SMT query and does not prove its theorem.

Run the automated demo checks with Python 3 installed:

```sh
tests/translation/run-demo.sh
```

The script checks the Boolean, integer, function, and quantifier demos: expected outputs, metadata
variants, standalone statements and templates, and the completed proofs shown here.
It also checks rejection cases and overwrite protection, using temporary
directories that are removed afterwards. CHC checks compare lh_sum_rec with its
expected output and compile the combined clause fixture. Source-location checks
cover multiline input, quoted text, and malformed tails.

## Translate integer queries

Translate contradictory integer bounds with the same command:

```sh
lake exe smt2lean tests/translation/int/bounds.smt2 --out integer-demo
lake env lean integer-demo/Query.lean
```

SMT `Bool` declarations become Lean `Prop` parameters; `Int` declarations become
Lean `Int` parameters. Literals keep their exact values, including values beyond
64 bits. The generated file still uses only Lean core, with statements followed
by an unfinished proof. This example states `∀ x : Int, (x ≥ 0 ∧ x < 0) → False`.

Open `integer-demo/Query.lean` and compare it with the
[expected output](tests/translation/int/expected/Query.lean).
Replace the Proofs section with:

```lean
-- Proofs

theorem refutation : Refutation := by
  intro x h
  exact Int.not_lt_of_ge h.1 h.2
```

Here `h.1` says `0 ≤ x`, which contradicts `h.2 : x < 0`. Run the same Lean
command again; the proof now checks without `sorry`.

The integer fragment follows [SMT-LIB Ints](https://smt-lib.org/theories-Ints.shtml):

| SMT-LIB operator | Operands | Result | Lean meaning |
| --- | --- | --- | --- |
| Numeral | None | `Int` | Exact integer value |
| Unary `-` | One `Int` | `Int` | `-x` |
| `+`, `-`, `*` | Two or more `Int` | `Int` | Fold left; e.g. `(- x y z)` becomes `(x - y) - z` |
| `abs` | One `Int` | `Int` | `if x < 0 then -x else x` |
| `=` | Two or more of the same supported sort | `Bool` | Conjunction of adjacent equalities |
| `distinct` | Two or more of the same supported sort | `Bool` | Conjunction of all pairwise inequalities |
| `ite` | A `Bool` condition and two `Int` branches | `Int` | `if condition then yes else no` |
| `<`, `<=`, `>`, `>=` | Two or more `Int` | `Bool` | Conjunction of adjacent comparisons |

SMT `Bool` results become Lean propositions. All generated code uses Lean core;
`div` and `mod` remain unsupported.

The combined [arithmetic fixture](tests/translation/int/arithmetic.smt2) covers
these operators, nested absolute values, large integers, and comparison chains.

## Translate let bindings

`let` gives expressions local names. Every binding expression uses the outer
scope; the new names are available together in the body. For a declared Int `x`:

```smt2
(assert (let ((x 1) (y x)) (= y x)))
```

This asserts `outer_x = 1`: `y` receives the original `x`. Without an outer
declaration for `x`, the reference in `(y x)` is rejected. cvc5 expands the bindings
before Lean reconstruction, so the output contains the expanded proposition.

Run the combined Bool/Int example from the repository root, choosing a new output directory:

```sh
lake exe smt2lean tests/translation/bindings/simultaneous.smt2 --out let-demo
lake env lean let-demo/Query.lean
```

The fixture covers simultaneous and nested bindings, repeated expressions,
quantifier shadowing, scope restoration, and local names that change sort.
The [CHC fixture](tests/translation/chc/clauses.smt2) also uses let aliases in
relation premises, guards, and relation arguments. Expanded terms retain the
same operator and CHC restrictions. The `sorry` warning is expected for the
unfinished proof template.

## Translate definitions and sort aliases

Nonrecursive `define-fun` supports Bool/Int results and parameters, including no
parameters. Bodies can refer to earlier declarations and definitions and use the
supported operators, `let`, `ite`, and quantifiers.

```smt2
(define-sort I () Int)
(declare-const x I)
(define-fun next () I (+ x 1))
(define-fun bump ((n I)) I (+ next n))
(assert (= (bump 2) 7))
```

The assertion becomes `x + 1 + 2 = 7`. Only `x` becomes a Lean parameter;
`next` and `bump` are expanded using their bodies. Globals keep their original
bindings even when callers reuse their names. Substitution also prevents a
quantifier inside a definition from capturing a caller's variable.

`define-sort` supports Bool/Int aliases, chains, and parameterized aliases such as
`(define-sort Id (T) T)`. Resolved sorts must be Bool or Int; aliases introduce no
new Lean types. They work in declarations, definition signatures, and binders.

Every definition body is checked when declared, including unused definitions.
Recursive definitions, forward references, unsupported bodies/signatures, and
unsupported alias bodies are rejected at their source command. cvc5 checks
argument sorts and alias arity. Definition equations stay internal; they are
never added to the translated query as extra assertions.

```sh
lake exe smt2lean tests/translation/bindings/definitions.smt2 --out definitions-demo
lake env lean definitions-demo/Query.lean
lake exe smt2lean tests/translation/chc/definitions.smt2 --out definitions-chc-demo
lake env lean definitions-chc-demo/Query.lean
```

CHC helpers expand before Horn validation. Only declared relations become
existential parameters; helper predicates add none. The expanded clauses must
still satisfy the supported Horn shape. Both demos have unfinished `sorry` proofs.

## Named assertions

`:named` gives a closed term a reusable name. For a declared Int `x`:

```smt2
(assert (! (> x 0) :named positive))
(assert (not positive))
```

The Lean assertions are `x > 0` and `¬(x > 0)`. The name adds no parameter;
its body is expanded, including references to earlier `define-fun` definitions.
Generated source comments retain each label and its command location, including
quoted labels and different names for the same formula. Errors include those labels.

```sh
lake exe smt2lean tests/translation/bindings/named.smt2 --out named-demo
lake env lean named-demo/Query.lean
```

Named Int subterms and later references within the same command also work.
Every named body is validated, even when a surrounding `let` discards it.
Names must be fresh. The pinned cvc5 parser rejects naming inside binders;
place `:named` around the whole quantified assertion instead. Annotated CHC
clauses follow the same rules and still undergo Horn validation after expansion.
Quantifier hints are supported as described below; other attributes remain rejected.

## Quantifier hints

`:pattern`, `:no-pattern`, and `:qid` guide the SMT solver without changing the
formula. For example, both assertions below translate to `∀ x : Int, P x`:

```smt2
(assert (forall ((x Int)) (! (P x) :pattern ((P x)) :qid rule)))
(assert (forall ((x Int)) (P x)))
```

cvc5 checks the hint syntax, names, and term types. The translator removes these
hints before checking and translating the body, preserving its binders. This also
works inside definitions and named assertions, and before CHC validation. Original
hints remain in the recorded command text; they add no Lean parameters or assumptions.
Operators used only in discarded hints need no Lean translation.

`:weight` remains rejected: the pinned parser silently ignores it rather than
validating its value. Unknown and semantic attributes are also rejected.

```sh
lake exe smt2lean tests/translation/quantifiers/hints.smt2 --out hints-demo
lake env lean hints-demo/Query.lean
```

The combined fixture contains five annotated/plain pairs covering nested binders,
shadowing, shared terms, definitions, and named assertions. The proof is unfinished.

## Translate functions and predicates

Functions can take any mixture of `Bool` and `Int` arguments and return either
sort. Each declaration becomes a Lean parameter; `Bool` becomes `Prop`, including
when used as an argument.

| SMT-LIB declaration | Lean parameter type |
| --- | --- |
| `(declare-fun f (Int Int) Int)` | `Int → Int → Int` |
| `(declare-fun P (Int) Bool)` | `Int → Prop` |
| `(declare-fun g (Bool Int) Int)` | `Prop → Int → Int` |
| `(declare-fun b (Bool) Bool)` | `Prop → Prop` |

The small congruence demo asserts `x = y` and `f(x) ≠ f(y)`:

```sh
lake exe smt2lean tests/translation/functions/congruence.smt2 --out function-demo
lake env lean function-demo/Query.lean
```

Open `function-demo/Query.lean` and compare it with the
[expected output](tests/translation/functions/expected/Query.lean).
Replace its Proofs section with:

```lean
-- Proofs

theorem refutation : Refutation := by
  intro f x y h
  exact h.2 (congrArg f h.1)
```

`congrArg f h.1` derives `f x = f y` from `x = y`, contradicting `h.2`.
Run the same Lean command again; the proof checks without `sorry` or axiom
dependencies. The generated file uses only Lean core.

The combined [applications fixture](tests/translation/functions/applications.smt2)
covers nested functions and predicates, compound Boolean arguments, argument
order, unused parameters, and quoted names matching `Int.add` and `True`.
Only first-order Bool/Int signatures are supported.

## Translate quantified queries

`forall` and `exists` can bind `Int` and `Bool` variables. Boolean variables become
Lean `Prop`, including when passed to functions. Nested scopes, shadowed names,
and unused binders are preserved.

This demo asserts that every integer satisfies `P`, and that some integer does not:

```sh
lake exe smt2lean tests/translation/quantifiers/quantified.smt2 --out quantifier-demo
lake env lean quantifier-demo/Query.lean
```

Its [expected output](tests/translation/quantifiers/expected/Query.lean) states:

```lean
∀ P : Int → Prop, ((∀ x : Int, P x) ∧ (∃ x : Int, ¬P x)) → False
```

Replace the Proofs section with:

```lean
-- Proofs

theorem refutation : Refutation := by
  intro P h
  exact h.2.elim (fun x hx => hx (h.1 x))
```

The existential supplies `x` and `¬P x`; the universal supplies `P x`.
Run the same Lean command again to check the completed proof using only Lean core.

Use `UF`, `LIA`, `NIA`, `UFLIA`, `UFNIA`, `ALL`, or omit `set-logic` for quantified
input. Quantifiers in `QF_*` logics and unsupported binder sorts are rejected.
The combined [scope fixture](tests/translation/quantifiers/scopes.smt2)
checks alternating binders, name collisions, and Boolean formulas used as arguments.

## Solver options and metadata

These `set-option` commands are accepted, including between checks:

| Option | Accepted value |
| --- | --- |
| `:produce-models`, `:produce-proofs`, `:produce-unsat-cores`, `:print-success` | `true` or `false` |
| `:random-seed` | An SMT-LIB numeral: `0` or digits starting with `1`–`9`, with no size limit |

The translator records their original text and source locations without executing
them. They do not change the Lean proposition or enable model/proof queries.
Strings such as `"true"`, negative seeds, and unknown options are rejected.
Semantic options such as `:global-declarations` remain unsupported, including when
set to `false`. Commands after `exit` are rejected.

Metadata support remains `:smt-lib-version 2.6`, `:source`, `:category`, `:license`,
`:notes`, and `:status`. Status values `sat`, `unsat`, and `unknown` never select
or prove the goal. Metadata can follow `check-sat`, before the optional final `exit`.
See the [SMT-LIB 2.6 reference](https://smt-lib.org/papers/smt-lib-reference-v2.6-r2024-09-20.pdf),
sections 4.1.7 and 4.2.9, for the options and metadata conventions.

```sh
lake exe smt2lean tests/translation/bool/options.smt2 --out options-demo
lake env lean options-demo/Query.lean
```

This combined example exercises all five options and six metadata fields. It
produces the same `∀ p : Prop, (p ∧ ¬p) → False` statement as the contradiction demo,
with an unfinished `sorry` proof.

## Translate sessions with push/pop

Every `check-sat` captures the assertions and declarations active at that point.
`push n` opens scopes; `pop n` removes their assertions, declarations, definitions,
sort aliases, and named bindings. Popped names can be declared again with different
sorts or signatures. Zero is a no-op; popping past the base scope is an error.
Counts must be SMT-LIB numerals within cvc5's unsigned 32-bit range.
These are the default local declaration lifetimes from
[SMT-LIB 2.6](https://smt-lib.org/papers/smt-lib-reference-v2.6-r2024-09-20.pdf), section 4.2.

```smt2
(set-logic QF_UF)
(declare-const p Bool)
(assert p)
(check-sat)
(push 1)
(assert (not p))
(check-sat)
(pop 1)
(check-sat)
```

This produces three independent goals in one file:

```lean
import Init

-- Statements

def Refutation_1 : Prop := ∀ p : Prop, p → False
def Refutation_2 : Prop := ∀ p : Prop, (p ∧ ¬p) → False
def Refutation_3 : Prop := ∀ p : Prop, p → False

-- Proofs

theorem refutation_1 : Refutation_1 := by sorry
theorem refutation_2 : Refutation_2 := by sorry
theorem refutation_3 : Refutation_3 := by sorry
```

Only the middle refutation is provable in this example. Translation preserves each
goal without claiming it holds. HORN sessions use `Problem_1`, `Problem_2`, etc.,
asking for satisfying relations separately at each check. A script with just one
check keeps the original `Refutation`/`refutation` or `Problem`/`problem` names.
Source comments identify each query and its active assertions or clauses.
Operator helpers are shared once across the file.

Run the combined examples: eight SMT checks and six CHC checks with nested scopes
and reused names.

```sh
lake exe smt2lean tests/translation/sessions/smt.smt2 --out session-demo
lake env lean session-demo/Query.lean
lake exe smt2lean tests/translation/sessions/chc.smt2 --out chc-session-demo
lake env lean chc-session-demo/Query.lean
```

The whole script must succeed before any output is written. A later invalid
command or unsupported query rejects the session. At least one check is required;
valid commands after the last check create no extra goal, and scopes need not be
closed at EOF. `check-sat-assuming`, reset commands, `:global-declarations`, and
model/proof/result requests remain unsupported. No `check-sat` is sent to the solver.

## Development build

Install [elan](https://github.com/leanprover/elan), Git, and a C++ toolchain
(Xcode Command Line Tools on macOS). Both projects use **Lean 4.33.1**. Elan selects
the version from each project's `lean-toolchain` file. Run from the repository root:

```sh
lake build
```

The first build needs network access for the pinned Lake dependencies and cvc5's
native libraries. Lake's checked-in `lake-manifest.json` records the resolved
dependency revisions; use it for reproducible builds.

The pinned upstream packages use Lean 4.33.0. This backend builds from source on
4.33.1; Mathlib's optional prebuilt cache requires the exact upstream toolchain.
When deliberately refreshing dependency resolution, skip that cache hook:

```sh
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
```

The translator imports cvc5 and lean-smt's Boolean/builtin/integer/UF term reconstructors
through `Smt2Lean/Backend.lean`. The direct dependencies are pinned to:

| Dependency | Revision |
| --- | --- |
| lean-smt | `5bdc51674065a074ece67b04e10024e9f426ec1f` |
| lean-cvc5 | `7e3365990661b697ccb30e92d6912f4cc6589322` (native cvc5 1.3.2) |

The example output project has its own dependency-free Lake configuration. Build
it separately:

```sh
cd examples
lake build
```

## Lean reconstruction test

Run the closed-proposition check with:

```sh
lake exe testReconstruction
```

It parses this fixed input using cvc5's native parser:

```smt2
(set-logic QF_UF)
(assert (and true (not false)))
(check-sat)
```

The test checks that only `set-logic` and `assert` were invoked and exactly one
assertion was captured. `check-sat` is intercepted without solving.

The inspection callback then uses Lean-SMT to translate the term into a Lean
expression. It checks that the expression has type `Prop` and matches
`True ∧ ¬False`, then asks Lean's kernel to check this definition:

```lean
def Reconstruction.assertion : Prop := True ∧ ¬False
```

The definition is installed in memory, with no unresolved variables, unfinished
goals, or axiom dependencies. This checks the proposition's construction; it does
not prove the proposition. This test does not write files. A failed check exits
nonzero.

## Query validation

The backend accepts sessions in the supported Bool/Int fragment. Run its fixtures with:

```sh
lake exe testParser
```

The Lean test modules live in `tests/backend/`. The parser test checks accepted inputs,
malformed input, and unsupported features; the reconstruction test checks the Lean
expression and its kernel validation.

Supported inputs:

- Nullary `Bool` or `Int` declarations, using `declare-const` or `declare-fun`.
- Functions with one or more `Bool`/`Int` arguments and either result sort, including
  nested calls and compound Boolean arguments. Bool results are Lean propositions.
- Boolean literals and `not`, `and`, `or`, `xor`, and `=>`.
- `ite` with a Boolean condition and two Bool branches or two Int branches.
- Simultaneous and nested `let` bindings over Bool/Int expressions, expanded by cvc5.
- Nonrecursive Bool/Int `define-fun`, expanded before reconstruction and CHC validation.
- `:named` assertions and closed subterms, with reusable bindings and preserved source labels.
- `define-sort` aliases and parameterized aliases resolving to Bool/Int.
- `forall` and `exists` over `Bool`/`Int`, including nested binders and unused variables.
- Quantifier hints `:pattern`, `:no-pattern`, and `:qid`, removed without changing the body.
- Integer literals, unary `-`, and `=`/`distinct` over either supported sort.
- Integer `+`, subtraction, `*`, `abs`, and `<`, `<=`, `>`, `>=`, including chains.
- No `set-logic`, or an initial `UF`, `LIA`, `NIA`, `UFLIA`, `UFNIA`, their `QF_` forms, or `ALL`.
  Every term is validated; accepting a logic does not enable all its operators.
  The CLI also accepts `HORN`, with the additional CHC restrictions below.
- `set-info` fields `:status`, `:source`, `:category`, `:license`, `:notes`, and
  `:smt-lib-version 2.6`. Metadata is ignored, never used as an assumption.
- `set-option` for `:produce-models`, `:produce-proofs`, `:produce-unsat-cores`,
  `:print-success`, and `:random-seed`, validated and recorded without execution.
- One or more `check-sat` commands, `push`/`pop`, and an optional final `exit`.

`parseAndInspectSession` calls `inspect` at each check with a `ParsedQuery`: the
query number, logic, active declarations (SMT names and native identities), active
assertions and definitions with source locations, and command history through that
check. cvc5 reports both declaration spellings as `declare-fun` in the invocation
trace. No query command is executed. Reconstruct native terms inside the callback,
before later commands can remove their scope. Keep only closed Lean expressions
afterward; the CLI uses fresh reconstruction caches for every query.

Callbacks can run before a later error. `Emit.translateSession` collects their
results and returns generated text only after the whole script succeeds; the CLI
then writes it. The older `parseAndInspectQuery` API remains strict: exactly one
check, no scopes, only metadata/exit afterward, and a callback after full validation.

Errors include `file:line:column`, the command number, and the query number for
CHCs and later SMT queries. cvc5 may print a warning when no logic is supplied;
the same term validation still applies.

`Smt2Lean.Source` reads command boundaries while preserving the exact input bytes.
It handles nested parentheses, comments, quoted identifiers, and strings with
doubled quotes. cvc5 still parses and checks the terms. Locations cover whole
commands; validation and reconstruction errors point to the relevant command's
start. Unterminated input reports EOF and where the unfinished construct opened.
Spans use UTF-8 byte offsets and one-based character columns, with an exclusive
end. A tab counts as one character; CRLF counts as one line break.

Generated `-- Source:` comments identify the original `check-sat` and each
assertion or CHC clause. Moving a command changes these comments without changing
the Lean proposition. The statement and proof remain in one file.

## Translate a CHC query

Translate the existing LiquidHaskell recursive-sum example:

```sh
lake exe smt2lean tests/chc/lh_sum_rec.smt2 --out chc-demo
lake env lean chc-demo/Query.lean
```

Compare `chc-demo/Query.lean` with the [expected output](tests/translation/chc/expected/Query.lean).
It contains one existential relation `r0 : Int → Prop` (the source relation `k_1`)
and all three clauses: a base rule, a recursive rule, and a false-head rule.
The Statements section defines `Problem`; the Proofs section contains:

```lean
theorem problem : Problem := by
  sorry
```

The `sorry` warning is expected. Typechecking verifies the generated statement;
the proof that satisfying relations exist remains unfinished. Status metadata
does not change this target. This command does not run Flex.

The combined fixture exercises sixteen clauses, including nonlinear and conditional guards,
nullary relations, multiple relation premises, and shadowed binders:

```sh
lake exe smt2lean tests/translation/chc/clauses.smt2 --out chc-clauses-demo
lake env lean chc-clauses-demo/Query.lean
```

Both output directories must be new. The combined fixture includes `False`, so
its generated proposition is intentionally unprovable; it tests translation.

## CHC validation

```sh
lake exe testHorn
```

This validates the unedited `tests/chc/lh_sum_rec.smt2` and the combined
[clause fixture](tests/translation/chc/clauses.smt2), without a solver query.

`Smt2Lean.Chc` recognizes Bool-valued relations over Bool/Int and bare facts such
as `(P 0)` or a nullary `done`. It retains native symbol identities, argument
order, and unused relations. Bound Bool variables remain data. Global Int
constants, Int-valued functions, and relations inside relation arguments are
outside this initial CHC profile.

`extractClause` records the source assertion number, leading `forall` variables
with their sorts, ordered implication premises, and a relation or `false` head.
Unused variables and original argument expressions are retained. For lh_sum_rec,
the three clauses have 3/5/3 binders and heads `k_1`, `k_1`, and `false`.
Existential clauses, quantifiers below the leading binders, and unsupported heads
are rejected.

`parseAndInspectProblem` parses the complete input and calls `inspect` once with a
validated `Problem`: all declared relations and all clauses. It uses `validateQuery`
to flatten premise conjunctions in order and classify each premise as a positive
relation call or a relation-free Bool/Int formula (a theory guard). Native terms
must stay inside the callback. A bad later clause rejects the entire problem.

The supported rule shape is:

```smt2
(forall ((x Int) (cond Bool))
  (=> (and (P x) (> x 0) (not cond)) (Q (+ x 1))))
```

Leading binders and premises may be absent; the head may instead be `false`.
Chained implications and any number of positive relation premises are accepted.
Guards support Bool/Int literals and variables, `not`, `and`, `or`, `xor`, `=>`, `=`, `distinct`, `ite`,
`+`, `-`, `*`, `abs`, and comparisons. Guard disjunctions and negations stay intact:
`(not cond)` is valid for a bound Bool, while `(not (P x))` is rejected. Relations
inside equality, distinct, xor, conditionals, disjunction, or another relation's arguments are also rejected.
Other theories/operators remain unsupported.

For lh_sum_rec, validation yields one guarded fact, one recursive rule, and one
false-head clause, with 0/1/1 relation premises. Status metadata does not change
the result. Clause validation errors identify the source location, query 1,
command, and one-based assertion number. For example:

```text
example.smt2:7:1: query 1: command 7: clause 3: CHC relation inside a theory guard: (P x)
```

The CLI routes `(set-logic HORN)` through CHC validation and emits `Problem`.
Other supported logics, or no explicit logic, emit the ordinary `Refutation`.
Routing uses the parsed command; comments, symbol names, and status metadata
cannot select the goal. The entire input and its Lean definition are checked
before any output is written.

`Smt2Lean.Translate.withClauses` reconstructs validated CHCs in memory as
`∀ variables, premise₁ → … → head`. It passes fresh relation parameters and the
clause propositions to a callback. Native identities preserve shadowed bindings;
unused variables and relations are retained. Facts have no added premise, and
false heads become Lean `False`.

`lake exe testTranslation` compares all nineteen clauses from lh_sum_rec and the
combined fixture with handwritten Lean propositions and kernel-checks each clause
after closing its relation parameters. These checks do not prove the clauses.

`Smt2Lean.Translate.defineProblem` combines those clauses into a closed
`Problem : Prop := ∃ relations, clause₁ ∧ … ∧ clauseₙ` definition in memory.
It retains unused and nullary relations; an empty conjunction is `True`. The
definition is kernel-checked, with only the standard Lean axioms above permitted. This checks its type,
not whether suitable relation interpretations exist. Status metadata never
changes the proposition.

`Smt2Lean.Emit.render value (kind := .problem)` renders that proposition as
`def Problem : Prop := ...` in Statements, followed by
`theorem problem : Problem := by sorry` in Proofs. `Emit.writeFile` writes both
sections to one `Query.lean` in a new directory and refuses existing destinations.
The output imports only Lean core. The default emitter target is the SMT refutation.

## Translation checks

The translator reconstructs assertions and kernel-checks a closed refutation
definition in memory. Run its checks with:

```sh
lake exe testTranslation
```

This test also renders 33 SMT cases and 16 CHC cases, compares the
re-elaborated statements with the original expressions, and compiles each complete
file and its isolated statement section using only Lean core. `Refutation` and
`Problem` reject admissions and query-specific axioms; conditionals may use the
standard Lean axioms listed above. Only their proof templates are admitted.

`Smt2Lean.Translate.withAssertions` binds each SMT declaration to a fresh Lean
parameter of its reconstructed type and reconstructs the assertions using Lean-SMT.
Names such as `|True|`, `|Int|`, and `|Int.add|` stay parameters. Unmapped terms fail,
and each query has its own caches.

The local quantifier handler maps bound native terms to fresh Lean variables.
Each binder scope gets a fresh term cache seeded with its active variable bindings;
leaving the scope restores the previous cache. This preserves identity even when
an outer and inner variable have the same source name. The emitter prints binder
types explicitly, so unused existential variables still elaborate.

`defineRefutation` closes over all parameters and installs `Refutation : Prop`.
For assertions `p` and `(not p)`, its body is:

```lean
∀ p : Prop, (p ∧ ¬p) → False
```

A single assertion gives `∀ p : Prop, p → False`; no assertions give
`True → False`. Status metadata never changes the target. Every definition is
kernel-checked with the same axiom restrictions. This checks its type, not its truth.
