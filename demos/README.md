# Five advisor demos

Run from the repository root. Each file contains one query.

| Demo | Question | What it shows | Expected SMT result |
| --- | --- | --- | --- |
| [01-finite-list.smt2](01-finite-list.smt2) | Can a finite list be its own tail? | Recursive Lean inductives and an interactive induction proof | unsat |
| [02-array-swap.smt2](02-array-swap.smt2) | Can swapping two cells twice change memory? | Symbolic arrays, extensionality, simultaneous let, and definitions | unsat |
| [03-safe-midpoint.smt2](03-safe-midpoint.smt2) | Can `lo + ((hi - lo) >> 1)` escape unsigned search bounds? | Actual 32-bit arithmetic and logical shifts | unsat |
| [04-real-buckets.smt2](04-real-buckets.smt2) | Can a timestamp fall outside its computed millisecond bucket? | Exact reals, integer conversion, and floor for negative times | unsat |
| [05-stack-invariant.smt2](05-stack-invariant.smt2) | Can a relation certify that pushes/pops preserve a consistent height? | Recursive CHCs, datatypes, testers, and match | sat |

The first four generate `Refutation`: no interpretation satisfies the assertions.
The fifth generates `Problem`: some relation satisfies every Horn clause. A suitable
relation is `Reach(s, n)` iff `n` is the structural length of `s`.

All five templates and their statement-only sections were checked with Lean.
The translator does not run an SMT solver. Generated proofs start with `sorry`;
the completed proof below was also checked without admissions.

## Run all five

This creates a fresh output directory on every run and prints its location:

```sh
(
  set -eu
  demo_out=$(mktemp -d /tmp/smt2lean-demos.XXXXXX)
  for input in demos/*.smt2; do
    name=$(basename "$input" .smt2)
    lake exe smt2lean "$input" --out "$demo_out/$name"
    lake env lean "$demo_out/$name/Query.lean"
  done
  echo "Open the generated Query.lean files under: $demo_out"
)
```

To run one example into a new directory inside the project:

```sh
lake exe smt2lean demos/01-finite-list.smt2 --out list-demo
lake env lean list-demo/Query.lean
```

## Finish a proof live

Open the generated file for demo 1. Its statement says that
`xs = cons x xs` is impossible for every finite list `xs` and integer `x`.
Replace the theorem's `sorry` with:

```lean
  intro xs x
  induction xs with
  | c0_nil => intro h; cases h
  | c1_cons y ys ih =>
    intro h
    obtain ⟨rfl, htail⟩ := SMT.Datatypes.g0.T0_IntList.c1_cons.inj h
    exact ih htail
```

Then run `lake env lean list-demo/Query.lean` again. The proof checks without `sorry`.
The empty case uses constructor disjointness; the nonempty case uses constructor
injectivity and the induction hypothesis on the tail.
