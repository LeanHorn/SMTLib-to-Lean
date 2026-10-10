# SMTLib-to-Lean

Translate SMT-LIB queries into Lean 4 propositions for interactive proof when an
SMT solver cannot settle a query. Generated statements are kernel-checked; proof
templates contain `sorry` until you complete them.

Support includes Bool, Int, Real and bitvector expressions, functions,
quantifiers, ordinary and recursive definitions, let bindings, arrays, monomorphic
datatypes, uninterpreted sort constructors, incremental sessions, and a restricted
Horn-clause fragment. Recursive definitions become equations over function
interpretations; no Lean termination proof is required.
Full SMT-LIB support is in progress.

## Install

Install [elan](https://github.com/leanprover/elan), Git, and a C++ toolchain
(Xcode Command Line Tools on macOS), then run:

```sh
git clone https://github.com/LeanHorn/SMTLib-to-Lean.git
cd SMTLib-to-Lean
lake build
```

The project pins Lean and its dependencies. The first build downloads dependencies
and cvc5's native libraries.

## Try it

```sh
lake exe smt2lean tests/translation/bool/contradiction.smt2 --out boolean-demo
lake env lean boolean-demo/Query.lean
```

The output directory must be new, with an existing parent. Each query produces
named assertions or clauses, a statement, and a proof template in `Query.lean`.
SMT queries produce a `Refutation` goal; Horn queries produce a `Problem` goal
asserting the existence of satisfying relations.

Use `--mode model` for general model-existence goals, including non-Horn formulas.
Use `--mode fixedpoint` for positive Z3 `rule`/`query` inputs over Bool, Int, Real,
and bitvectors: `Safe` means query `unsat`; `Reachable` means query `sat`.

For this example, replace `sorry` with:

```lean
  intro p h
  exact h.2 h.1
```

Run the Lean command again to check the completed proof. For broader examples,
see [demo.smt2](demo.smt2) and [demo-chc.smt2](demo-chc.smt2).
Use `--max-rec-depth N` to override the default recursion limit of 4096.

## Library API: standalone definitions

`Smt2Lean.Translate.reconstructDefinitions` takes a validated
`Backend.ParsedQuery` and returns `Array ReconstructedDefinition` in `Lean.MetaM`.
Each result contains the original SMT name (without quoting bars), source location,
Lean type, and closed Lean value. All active ordinary definitions are returned in
source order, including definitions unused by assertions. Unused parameters retain
their positions; SMT `Bool` becomes Lean `Prop`.

```lean
import Smt2Lean

open Lean Meta

run_elab do
  let env ← getEnv
  let input := "(set-logic LIA) \
    (define-fun inv ((x Int)) Bool (>= x 0)) (check-sat)"
  (Smt2Lean.Backend.parseAndInspectQuery input fun query => do
    let inspect : MetaM Unit := do
      let definitions ← Smt2Lean.Translate.reconstructDefinitions query
      for definition in definitions do
        IO.println s!"{definition.name} : {← ppExpr definition.type} := {← ppExpr definition.value}"
    discard <| inspect.toIO { fileName := "definitions", fileMap := default } { env }
  ).runIO
```

Run this with `lake lean`, which loads the native cvc5 plugin. The result is an
`Int → Prop` lambda equivalent to `fun x => x ≥ 0`. Reconstruction must happen
inside the parser callback, but the returned values remain usable afterwards in
the original Lean environment. The API leaves no generated declarations or
changed reconstruction handlers behind.

The initial API supports Bool/Int signatures and bodies, including Boolean and
integer operators, quantifiers, `ite`, `let`, and calls to earlier ordinary
definitions. Definitions with unresolved global symbols, recursive definitions,
other sorts, or division/modulo needing an unspecified zero-case interpretation
are rejected with source context. Division/modulo by a nonzero integer literal
is supported. These restrictions apply to this standalone API; the query
translator retains its broader theory support.

This API does not invoke `checkSat`, use assertions as assumptions, or certify
that returned definitions satisfy a constraint. It accepts parsed SMT scripts;
importing external solver response envelopes uses the API below.

## Library API: external solver models

`Smt2Lean.Model.importResponse` takes solver **stdout**, a Lean environment, and
an optional source name. It returns typed, closed definitions using the same
parser and reconstruction API above; it does not launch a process or solve again.

```lean
import Smt2Lean

open Lean Meta

run_elab do
  let response ← Smt2Lean.Model.importResponse
    "sat ((define-fun inv ((x Int)) Bool (>= x 0)))"
    (← getEnv) "spacer.out"
  let some definitions := response.definitions
    | throwError "solver returned no model"
  for definition in definitions do
    logInfo m!"{definition.name} : {definition.type} := {definition.value}"
```

Run with `lake lean` to load the native plugin. Results remain usable after the
call in the supplied environment. The function returns:

- `status : Option SolverResponse.Status`: the literal `sat`, `unsat`, or
  `unknown` response. Standalone models and error-only responses have no status.
- `definitions : Option (Array ReconstructedDefinition)`: `none` means no model
  was supplied; `some #[]` means an explicitly empty model. Definition order,
  original symbol names, and source spans in the response are preserved.
- `diagnostics`: decoded `(error "...")` and `(:reason-unknown ...)` messages,
  tagged by kind and source location. Solver stderr belongs to the process runner
  and should not be concatenated with stdout.

Accepted model formats are `((define-fun ...) ...)`, `(model (define-fun ...) ...)`,
and direct `define-fun` sequences, with or without a preceding `sat`.
Leading `success` acknowledgements and SMT-LIB comments are accepted. Helpers
must precede their callers, as in an ordinary SMT script, and are expanded by
the existing capture-avoiding definition machinery. All definitions, including
helpers, are returned. The Bool/Int restrictions of the standalone API apply.

The importer consumes exactly one response. Duplicate names, repeated statuses,
multiple models, malformed/trailing data, unsupported definitions, and models
mixed with errors or `unknown`/`unsat` are rejected with source context. Imports
fail atomically: a valid prefix of an invalid model is never returned. A status
without a model, or an error/unknown response, returns no definitions.

This API handles models for **asserted CHCs with `check-sat`**, where `sat`
indicates satisfiability. It does not interpret Z3 fixedpoint `(query ...)`
answers or their different status convention. Definitions are candidate
interpretations; no proof that they satisfy the original constraints is added.
Matching them to Flex's existential predicates and checking those constraints
belongs to the later integration.

Captured Z3/Spacer and Eldarica fixtures, commands, and versions are in
[`tests/models/README.md`](tests/models/README.md). The tests run without either
external solver installed:

```sh
lake build testModels
lake env .lake/build/bin/testModels
```

## Tests

```sh
bash tests/run.sh
```

Runs independent test groups with four workers; use `--jobs 1` for a serial run.

For focused CLI checks, list groups with `python3 tests/cli.py --list`, then run
`lake env python3 tests/cli.py horn` (build `smt2lean` first).

For benchmark-runner options: `lake env python3 benchmarks/run.py --help`.
