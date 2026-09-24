# Tests

Real SMT-LIB queries from LiquidHaskell (`lh_*`) and Flux (`flux_*`).

```sh
tests/run.sh   # replays every file through z3 and checks the recorded answers
```

## `smt/`: verification conditions (8)

Unedited z3 sessions saved by `fixpoint --save`. After each `(check-sat)` there's a `; SMT Says:` comment with the answer z3 gave at the time.

- `unsat`: the VC is valid.
- `sat`: a candidate qualifier was rejected during κ inference. In `lh_sets_neg` it's a real verification failure.

## `chc/`: Horn clauses for Spacer (4)

These use `(set-logic HORN)`. The expected answer is in `(set-info :status …)`.

- `sat`: safe, since an invariant exists.
- `unsat`: unsafe, since a counterexample exists.

They were converted from liquid-fixpoint's Horn format with `tools/fqhorn2chc.py`.

Each file's header gives its source, the command that produced it and the theories it uses.
