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

The CLI currently remains a stub. Task 2.1 establishes backend compilation and
native linking; parser execution and reconstruction checks follow in tasks 2.2
and 2.3 of the [implementation plan](docs/PR-PLAN.md).
