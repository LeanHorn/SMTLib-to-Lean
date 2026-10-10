# Solver response fixtures

Captured with Z3 **4.15.4** (`fp.engine=spacer`) and Eldarica **2.3** on
2026-10-10. The `.out` files are unchanged stdout; `.err` files are unchanged
stderr. `testModels` imports stdout only and needs neither executable installed.

For each input `safe.smt2`, `multiple.smt2`, and `unsafe.smt2`, capture with:

```sh
z3 fp.engine=spacer safe.smt2 > spacer-safe.out 2> spacer-safe.err
eld -hsmt -ssol safe.smt2 > eldarica-safe.out 2> eldarica-safe.err
```

Repeat using `multiple` and `unsafe` for the other fixture pairs. These inputs
use asserted HORN constraints and `check-sat`, not fixedpoint `query` commands.
`safe` has a nonnegative counter invariant. `multiple` adds a binary relation,
a universally true predicate with an unused Bool argument, and a false predicate.
The solvers need not choose identical invariants or definition order.

The safe and multiple runs exit 0. For `unsafe`, Spacer exits 1 and prints `unsat`
followed by `(error "... model is not available")`, because the fixture requests
`get-model` unconditionally. This tests that an unsuccessful model request cannot
be imported as an empty/successful model. Eldarica exits 0 with `unsat`.
Eldarica's `-ssol` supplies the model; its warning that it ignores `get-model`
goes to stderr. A production runner should request models only when appropriate
and check process exit codes separately.

Upstream references: [Z3 HORN syntax](https://microsoft.github.io/z3guide/docs/fixedpoints/syntax/)
and [Eldarica](https://github.com/uuverifiers/eldarica).
