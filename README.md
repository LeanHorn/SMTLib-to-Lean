# SMTLib-to-Lean

A tool to connect SMT-based frontends to Lean4.

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

Run the automated demo checks with Python 3 installed:

```sh
tests/translation/run-demo.sh
```

The script checks both the Boolean and integer demos: expected outputs, metadata
variants, standalone statements and templates, and the completed proofs shown here.
It also checks rejection cases and overwrite protection, using temporary
directories that are removed afterwards.

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
| `<`, `<=`, `>`, `>=` | Two or more `Int` | `Bool` | Conjunction of adjacent comparisons |

SMT `Bool` results become Lean propositions. All generated code uses Lean core;
`div` and `mod` remain unsupported.

The combined [arithmetic fixture](tests/translation/int/arithmetic.smt2) covers
these operators, nested absolute values, large integers, and comparison chains.

## Translate integer functions

Task 5.1 supports declarations such as `(declare-fun f (Int Int) Int)` and nested
applications. Each function becomes a Lean parameter, here `f : Int → Int → Int`.

```sh
lake exe smt2lean tests/translation/functions/applications.smt2 --out function-demo
lake env lean function-demo/Query.lean
```

The combined fixture checks argument order, nested calls, an unused function, and
a quoted name matching Lean's `Int.add`. Output still uses only Lean core, with an
unfinished proof. Predicates and Boolean function arguments follow in tasks 5.2–5.3.

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

The backend accepts one query in the supported Bool/Int fragment. Run its fixtures with:

```sh
lake exe testParser
```

The Lean test modules live in `tests/backend/`. The parser test checks accepted inputs,
malformed input, and unsupported features; the reconstruction test checks the Lean
expression and its kernel validation.

Supported inputs:

- Nullary `Bool` or `Int` declarations, using `declare-const` or `declare-fun`.
- Functions with one or more `Int` arguments and an `Int` result, including nested calls.
- Boolean literals and `not`, `and`, `or`, and `=>`.
- Integer literals, unary `-`, and `=` over either supported sort.
- Integer `+`, subtraction, `*`, `abs`, and `<`, `<=`, `>`, `>=`, including chains.
- No `set-logic`, or an initial `QF_UF`, `QF_LIA`, `QF_NIA`, `QF_UFLIA`, `QF_UFNIA`, or `ALL` logic.
  Every term is validated; accepting a logic does not enable all its operators.
- `set-info` fields `:status`, `:source`, `:category`, `:license`, `:notes`, and
  `:smt-lib-version 2.6`. Metadata is ignored, never used as an assumption.
- Exactly one `check-sat`, followed only by metadata and an optional final `exit`.

The driver validates every declaration and assertion, then calls `inspect` once
with a `ParsedQuery`: declarations (SMT names and native term identities), assertion
terms, and executed command names. cvc5 reports both declaration spellings as
`declare-fun` in this trace. No query command is executed.

Unsupported input is rejected before `inspect` runs, including content after
`check-sat` or `exit`. Errors include the input name and command number. cvc5 may
print a warning when no logic is supplied; the same term validation still applies.

## Translation checks

The translator reconstructs assertions and kernel-checks a closed refutation
definition in memory. Run its checks with:

```sh
lake exe testTranslation
```

This test also renders fourteen cases, compares the re-elaborated statements with
the original expressions, and compiles each generated file using only Lean core.
It checks that `Refutation` has no axiom dependencies and only its proof is admitted.

`Smt2Lean.Translate.withAssertions` binds each SMT declaration to a fresh Lean
parameter of its reconstructed type and reconstructs the assertions using Lean-SMT.
Names such as `|True|`, `|Int|`, and `|Int.add|` stay parameters. Unmapped terms fail,
and each query has its own caches.

`defineRefutation` closes over all parameters and installs `Refutation : Prop`.
For assertions `p` and `(not p)`, its body is:

```lean
∀ p : Prop, (p ∧ ¬p) → False
```

A single assertion gives `∀ p : Prop, p → False`; no assertions give
`True → False`. Status metadata never changes the target. Every definition is
kernel-checked and has no axiom dependencies. This checks its type, not its truth.

PRs 3 and 4 provide the Boolean and integer demos above. PR 5 adds functions; see the
[implementation plan](docs/PR-PLAN.md).
