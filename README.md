# SMTLib-to-Lean

A tool to connect SMT-based frontends to Lean4.

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
not prove the proposition. No output file is generated yet. A failed check exits
nonzero.

## Boolean query validation

Task 3.1 extends the backend to accept one Boolean query. Run its fixtures with:

```sh
lake exe testParser
```

Both test modules live in `tests/backend/`. The parser test checks accepted inputs,
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

The main `smt2lean` CLI remains a stub. Variable reconstruction and generated Lean
files follow in tasks 3.2–3.6; see the [implementation plan](docs/PR-PLAN.md).
