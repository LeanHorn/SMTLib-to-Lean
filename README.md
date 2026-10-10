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
