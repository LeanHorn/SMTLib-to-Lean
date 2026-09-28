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
tests/translation/run-bool.sh
```

The script builds the CLI, checks the expected output and metadata variants,
compiles the generated statements and templates, and checks the completed proof
above. It also checks rejection cases and overwrite protection, using temporary
directories that are removed afterwards.

## Translate integer declarations and literals

Task 4.1 adds `Int` variables, exact integer literals, unary minus, and equality:

```sh
lake exe smt2lean tests/translation/int/literals.smt2 --out integer-demo
lake env lean integer-demo/Query.lean
```

SMT `Bool` declarations become Lean `Prop` parameters; `Int` declarations become
Lean `Int` parameters. Literals keep their exact values, including values beyond
64 bits. The generated file still uses only Lean core, with statements followed
by an unfinished proof. Arithmetic and comparisons follow in tasks 4.2–4.3;
`div` and `mod` remain unsupported.

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

The translator imports cvc5 and lean-smt's Boolean/builtin/integer term reconstructors
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
- Boolean literals and `not`, `and`, `or`, and `=>`.
- Integer literals, unary `-`, and `=` over either supported sort.
- No `set-logic`, or an initial `QF_UF`, `QF_LIA`, `QF_NIA`, or `ALL` logic.
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

This test also renders eleven cases, compares the re-elaborated statements with
the original expressions, and compiles each generated file using only Lean core.
It checks that `Refutation` has no axiom dependencies and only its proof is admitted.

`Smt2Lean.Translate.withAssertions` binds each SMT declaration to a fresh Lean
`Prop` or `Int` parameter and reconstructs the assertions using Lean-SMT. Names such
as `|True|` and `|Int|` stay variables. Unmapped terms fail, and each query has its own caches.

`defineRefutation` closes over all parameters and installs `Refutation : Prop`.
For assertions `p` and `(not p)`, its body is:

```lean
∀ p : Prop, (p ∧ ¬p) → False
```

A single assertion gives `∀ p : Prop, p → False`; no assertions give
`True → False`. Status metadata never changes the target. Every definition is
kernel-checked and has no axiom dependencies. This checks its type, not its truth.

Tasks 3.1–3.6 complete the Boolean demo above. PR 4 extends it to integers; see the
[implementation plan](docs/PR-PLAN.md).
