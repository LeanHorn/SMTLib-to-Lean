# Tests

Run the Boolean and integer demo checks from the repository root:

```sh
tests/translation/run-demo.sh
```

The script builds the CLI, runs the reconstruction smoke test, and runs `cli.py`.
The CLI checks compile twelve generated files and their statement sections using
Lean core. Boolean contradiction and integer bounds outputs, including their
status variants, must match `translation/bool/expected/Query.lean` and
`translation/int/expected/Query.lean`. Both README proofs compile with warnings
treated as errors and no `sorryAx` dependency. The Boolean proof has no axioms;
the integer proof uses core's `propext` through its order lemma. Edited templates
and completed proofs survive attempted overwrites. Python 3 is required.

For the original LiquidHaskell (`lh_*`) and Flux (`flux_*`) queries:

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
contexts, and thirteen closed Bool/Int refutations against handwritten Lean propositions.
It also compares the printed statements with the original expressions and compiles
each `Query.lean` using only Lean core. Statements have no axiom dependencies;
only the following proof templates contain admissions. Existing proof work is
preserved. The tests reuse the combined fixtures below.

Run the CLI/demo checks without rebuilding the smoke test:

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

`translation/int/` keeps three reusable queries:

- `literals.smt2`: mixed Bool/Int declarations, quoted names, unused parameters,
  chained equality, unary minus, zero, and integers beyond 64 bits.
- `arithmetic.smt2`: operand order, nonlinear multiplication, nested negation/abs,
  absolute value at negative/zero/positive inputs, and all four comparison chains.
- `bounds.smt2`: the small contradiction `x ≥ 0` and `x < 0`.

The translation test compares each complete formula with a handwritten Lean target.
Emitted absolute values use only core `if/then/else`; comparison chains retain
every adjacent pair. The parser test also checks their native binary structure.

`backend/Parser.lean` reuses these for logic and metadata variants. Its short
rejection cases live together in a table: each needs a separate parse because
validation stops at the first error. Checks cover declaration identity and error
locations; invalid input must never reach the inspection callback.
Div/mod remain rejected for zero and nonzero divisors, including inside supported
arithmetic. Real terms and non-nullary functions are also rejected.

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
