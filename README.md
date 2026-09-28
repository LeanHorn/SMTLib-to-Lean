# SMTLib-to-Lean

A tool to connect SMT-based frontends to Lean4.

## Translate a Boolean query

From the repository root:

```sh
lake exe smt2lean tests/translation/bool/contradiction.smt2 --out boolean-demo
```

This creates `Statements.lean` with the closed `Refutation : Prop` definition and
`Proofs.lean` with an unfinished theorem containing `by sorry`. The generated
files use Lean core; they do not depend on cvc5 or this translator.

The output directory must be new, and its parent must exist. Existing proof work
is never overwritten. The translator validates the whole input and kernel-checks
the in-memory statement before writing files. It does not solve the query or
prove the theorem.

Use `lake exe smt2lean --help` for usage. Exit codes are `0` for generation/help,
`2` for invalid arguments, and `1` for input, translation, or output errors.
Only the Boolean fragment listed below is currently supported.

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

The translator imports cvc5 and lean-smt's Boolean/builtin term reconstructors
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

## Boolean query validation

Task 3.1 extends the backend to accept one Boolean query. Run its fixtures with:

```sh
lake exe testParser
```

The Lean test modules live in `tests/backend/`. The parser test checks accepted inputs,
malformed input, and unsupported features; the reconstruction test checks the Lean
expression and its kernel validation.

Supported inputs:

- `declare-const p Bool` and `declare-fun p () Bool`.
- Boolean literals and `not`, `and`, `or`, `=>`, and Boolean `=`.
- No `set-logic`, or an initial `QF_UF` or `ALL` logic.
- `set-info` fields `:status`, `:source`, `:category`, `:license`, `:notes`, and
  `:smt-lib-version 2.6`. Metadata is ignored, never used as an assumption.
- Exactly one `check-sat`, followed only by metadata and an optional final `exit`.

The driver validates every declaration and assertion, then calls `inspect` once
with a `BoolQuery`: declarations (SMT names and native term identities), assertion
terms, and executed command names. cvc5 reports both declaration spellings as
`declare-fun` in this trace. No query command is executed.

Unsupported input is rejected before `inspect` runs, including content after
`check-sat` or `exit`. Errors include the input name and command number. cvc5 may
print a warning when no logic is supplied; the Boolean validation still applies.

## Boolean translation

Tasks 3.2–3.3 reconstruct Boolean assertions and kernel-check a closed refutation
definition in memory. Run:

```sh
lake exe testTranslation
```

This test also renders all eight cases, compares the re-elaborated statements with
the original expressions, and compiles both generated files using only Lean core.

`Smt2Lean.Translate.withAssertions` binds each SMT declaration to a fresh Lean
`Prop` parameter and reconstructs the assertions using Lean-SMT. Names such as
`|True|` stay variables. Unmapped terms fail, and each query has its own caches.

`defineRefutation` closes over all parameters and installs `Refutation : Prop`.
For assertions `p` and `(not p)`, its body is:

```lean
∀ p : Prop, (p ∧ ¬p) → False
```

A single assertion gives `∀ p : Prop, p → False`; no assertions give
`True → False`. Status metadata never changes the target. Every definition is
kernel-checked and has no axiom dependencies. This checks its type, not its truth.

Tasks 3.4–3.5 connect this translation to file generation and the CLI above.
The reviewed demo walkthrough remains task 3.6; see the
[implementation plan](docs/PR-PLAN.md).
