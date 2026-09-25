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

## Parser and Lean reconstruction smoke test

Run the tasks 2.2–2.3 checks with:

```sh
lake exe backendSmoke
```

It parses this fixed input using cvc5's native parser:

```smt2
(set-logic QF_UF)
(assert (and true (not false)))
(check-sat)
```

Only `set-logic` and `assert` reach native command invocation. The driver
intercepts `check-sat`, captures the assertions, and the smoke test verifies one
Bool-sorted term with the expected AND/NOT/constant structure. It prints the
actual invocation trace and checks rejection of malformed input, invalid logic,
unsupported queries, missing/repeated checks, and trailing commands. A failed
check exits nonzero. The driver currently accepts only `set-logic`, `assert`, and
one final `check-sat`; this is not yet a general SMT-LIB importer.

The inspection callback then uses Lean-SMT to translate the term into a Lean
expression. It checks that the expression has type `Prop` and matches
`True ∧ ¬False`, then asks Lean's kernel to check this definition:

```lean
def BackendSmoke.assertion : Prop := True ∧ ¬False
```

The definition is installed in memory, with no unresolved variables, unfinished
goals, or axiom dependencies. This checks the proposition's construction; it does
not prove the proposition. No output file is generated yet.

The main `smt2lean` CLI remains a stub. PR 3 adds file input and generated Lean
files; see the [implementation plan](docs/PR-PLAN.md).
