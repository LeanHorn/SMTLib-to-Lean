# SMTLib-to-Lean

Translate SMT-LIB queries into Lean 4 propositions, and
do an interactive proof
when SMT gets stuck, or
you want higher trust.

## Setup and usage

Install [elan](https://github.com/leanprover/elan), Git, and a C++ toolchain
(Xcode Command Line Tools on macOS). Elan selects the pinned Lean version.

```sh
git clone https://github.com/LeanHorn/SMTLib-to-Lean.git
cd SMTLib-to-Lean
lake build
```

The first build downloads dependencies and cvc5's native libraries.
To translate a file and typecheck the result:

```sh
lake exe smt2lean input.smt2 --out output
lake env lean output/Query.lean
```

The output directory must be new, with an existing parent. Each `check-sat`
becomes a statement in `Query.lean`, followed by a proof template containing `sorry`.
Open that file in your Lean editor to complete the proof.

## Demo

[tests/translation/bool/contradiction.smt2](tests/translation/bool/contradiction.smt2)
asserts both `p` and its negation:

```smt2
(set-logic QF_UF)
(declare-const p Bool)
(assert p)
(assert (not p))
(check-sat)
(exit)
```

Run:

```sh
lake exe smt2lean tests/translation/bool/contradiction.smt2 --out boolean-demo
lake env lean boolean-demo/Query.lean
```

Generated `Query.lean` (source comments omitted):

```lean
import Init

-- Statements

def Refutation : Prop :=
  ∀ (p0 : Prop), p0 ∧ ¬p0 → False

-- Proofs

theorem refutation : Refutation := by
  sorry
```

The `sorry` warning means the proof is unfinished. Replace `sorry` with:

```lean
  intro p h
  exact h.2 h.1
```

Run the Lean command again; the proof now checks without `sorry`.
For broader examples, try [demo.smt2](demo.smt2) and [demo-chc.smt2](demo-chc.smt2).

## Research prototype in progress

The translator supports a first-order SMT-LIB fragment over Bool, Int, Real, and nonempty uninterpreted sorts (`declare-sort` of arity zero), including exact integer and real arithmetic, uninterpreted functions, quantifiers, nonrecursive definitions, let bindings, and incremental queries with `push`/`pop`, temporary `check-sat-assuming` assumptions, resets, and global declarations.

Real output imports `Mathlib.Data.Real.Basic` from the pinned dependencies; other output uses Lean core. Division at zero preserves arbitrary, shared interpretations. General Int/Real conversions remain unsupported.

Supported constrained Horn clauses have universal binders, positive relation premises, quantifier-free and relation-free theory guards, and a relation or false head.

Support for additional SMT-LIB theories and commands is under development.
