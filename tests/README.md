# Tests

Real SMT-LIB queries from LiquidHaskell (`lh_*`) and Flux (`flux_*`).

```sh
tests/run.sh   # replays every file through z3 and checks the recorded answers
```

The translator's own checks run from the repository root without solving in cvc5:

```sh
lake exe testParser          # tests/backend/Parser.lean
lake exe testReconstruction  # tests/backend/Reconstruction.lean
lake exe testTranslation     # tests/backend/Translation.lean
```

`Parser.lean` checks accepted queries and rejection diagnostics.
`Reconstruction.lean` translates one proposition and checks it with Lean's kernel.
`Translation.lean` checks variable binding, connectives, independent reconstruction
contexts, and eight closed refutations against handwritten Lean propositions.
It also compares the printed statements with the original expressions and compiles
each `Query.lean` using only Lean core. Statements have no axiom dependencies;
only the following proof templates contain admissions. Existing proof work is
preserved. The test reuses the three fixtures below.

Check the CLI's exit codes, diagnostics, and output protection with:

```sh
lake build smt2lean
lake env python3 tests/cli.py
```

All generated test files go into temporary directories and are removed afterwards.

`translation/bool/` keeps three reusable queries:

- `contradiction.smt2`: the smallest demo, `p` and `not p`.
- `connectives.smt2`: all supported connectives, both declaration forms, quoted
  names, an unused declaration, metadata, and exit in one query.
- `empty.smt2`: a query with no assertions.

`backend/Parser.lean` reuses these for logic and metadata variants. Its 26 short
rejection cases live together in a table: each needs a separate parse because
validation stops at the first error. Checks cover declaration identity and error
locations; invalid input must never reach the inspection callback.

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
