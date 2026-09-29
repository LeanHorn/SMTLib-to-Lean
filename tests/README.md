# Tests

Run all translation demos from the repository root:

```sh
tests/translation/run-demo.sh
```

The script builds the CLI, runs the source-reader and reconstruction tests, and runs `cli.py`.
The CLI checks compile twenty-seven SMT files, six CHC files, and their statement sections using
Lean core. Boolean contradiction, integer bounds, function congruence, quantified,
and lh_sum_rec outputs must match their `expected/Query.lean`. Status variants
must match after removing source comments, since inserting metadata can move
locations without changing a proposition. All four README proofs compile with warnings treated as errors
and no `sorryAx` dependency. The Boolean, function, and quantifier proofs have no axioms; the
integer proof uses core's `propext` through its order lemma. Edited templates and
completed proofs survive attempted overwrites. The combined function/predicate
fixture also compiles through the CLI. Python 3 is required.

For the original LiquidHaskell (`lh_*`) and Flux (`flux_*`) queries:

```sh
tests/run.sh   # replays every file through z3 and checks the recorded answers
```

The translator's own checks run from the repository root without solving in cvc5:

```sh
lake exe testSource          # tests/backend/Source.lean
lake exe testParser          # tests/backend/Parser.lean
lake exe testReconstruction  # tests/backend/Reconstruction.lean
lake exe testTranslation     # tests/backend/Translation.lean
lake exe testHorn            # tests/backend/Horn.lean
```

`Source.lean` checks command boundaries, exact bytes, UTF-8 offsets, CR/LF/CRLF,
quoted identifiers, doubled quotes, literal backslashes in strings, and malformed
input. `Parser.lean` checks accepted queries, attachment of source ranges, and
rejection diagnostics. Locations point to command starts or lexical failures;
reconstruction errors retain the originating assertion/clause location.
`Horn.lean` parses the unedited `chc/lh_sum_rec.smt2` in explicit CHC mode. It checks
one typed declaration, three quantified assertions, and an invocation trace with
no solver query. Unsupported terms/sorts and invalid command sequences still fail
before inspection. It also recognizes relations and bare facts, checks native
identity and bound Bool arguments, and rejects unsupported CHC declarations and
relations nested inside arguments. Clause extraction checks assertion numbers,
binder identities/sorts, premise order, and relation/false heads. Existential or
non-leading quantifiers and unsupported heads are rejected. Validation flattens
premise conjunctions in order, distinguishes relation calls from theory guards,
and rejects hidden or negated relations. A bad later clause never reaches the
validated-problem callback. Errors identify the file, query, and offending clause;
parser errors retain command numbers. Status variants produce identical CHC structure.
The CLI tests translate lh_sum_rec to `Problem`, preserving the target under
absent/sat/unsat/unknown status metadata. The same clauses under `ALL` or no logic
produce `Refutation`; HORN text in comments, names, and metadata cannot select
CHC mode. Empty HORN input also translates. Invalid CHC declarations, later
clauses/operators, missing checks, and malformed tails fail with source context
and create no output. The combined fourteen-clause CHC fixture also compiles through
the CLI. Source checks cover multiline commands, quoted text, CRLF input, and
filenames containing newlines. Moving the input changes only source comments.
Edited CHC proof work survives attempted overwrites.
`Reconstruction.lean` translates one proposition and checks it with Lean's kernel.
`Translation.lean` checks variable binding, connectives, independent reconstruction
contexts, and closed Bool/Int refutations against handwritten Lean propositions.
It checks all 28 truth assignments for xor with two, three, and four operands
against odd parity, plus four integer distinct cases, using kernel-checked proofs.
Eight Boolean ite truth cases and four integer ite cases check branch selection,
negative/large values, and nesting.
These cases and a quantified function-argument example bring the total to 24 refutations.
It also compares the printed statements with the original expressions and compiles
each `Query.lean` and its isolated statement section using only Lean core.
Used xor/distinct helpers must appear exactly once before the query statement.
Tests compare the emitted helper bodies with their checked definitions, then
unfold helpers in each environment separately to compare the complete statements.
Tests check exact axiom dependencies: none for the earlier examples, and only
`propext`, `Classical.choice`, and `Quot.sound` for classical conditionals.
Separate rejection cases check that admissions and fabricated axioms remain
forbidden, including through another definition. Only proof templates contain
admissions in generated output. Existing proof work is
preserved. The tests reuse the combined fixtures below.

The translation test also reconstructs all seventeen CHC clauses from lh_sum_rec
and the combined CHC fixture. Each clause is compared with a handwritten Lean
proposition and kernel-checked after closing its relation parameters. Checks cover
unused variables/relations, shadowed binders, mixed sorts, nullary relations,
multiple premises, false heads, and isolation between nested reconstructions.
An unmapped relation named `True` must fail instead of resolving to Lean's builtin.
Complete CHC problems are compared with handwritten existential propositions,
including both fixtures, empty inputs, unused relations, nullary facts, and
inconsistent clauses. Absent/sat/unsat/unknown status variants of lh_sum_rec keep
the same target. All ten `Problem` definitions are closed, kernel-checked, and
checked against their expected axiom dependencies. The emitter writes each CHC case to one temporary `Query.lean`
with Statements before Proofs. The complete file and isolated statements compile
using only Lean core; only the `problem` theorem depends on `sorryAx`. Edited files
survive attempted overwrites.

Run the CLI/demo checks without rebuilding the smoke test:

```sh
lake build smt2lean
lake env python3 tests/cli.py
```

All generated test files go into temporary directories and are removed afterwards.

`translation/bool/` keeps three reusable queries:

- `contradiction.smt2`: the smallest demo, `p` and `not p`.
- `connectives.smt2`: all supported connectives, both declaration forms, quoted
  names, an unused declaration, metadata, and exit in one query. Includes xor
  with two to four operands, Boolean distinct, and nested Boolean conditionals.
- `empty.smt2`: a query with no assertions.

`translation/int/` keeps three reusable queries:

- `literals.smt2`: mixed Bool/Int declarations, quoted names, unused parameters,
  chained equality, unary minus, zero, and integers beyond 64 bits.
- `arithmetic.smt2`: operand order, nonlinear multiplication, nested negation/abs,
  absolute value at negative/zero/positive inputs, all four comparison chains,
  pairwise distinct with a repeated nonadjacent operand, and integer conditionals
  with both symbolic and decidable conditions.
- `bounds.smt2`: the small contradiction `x ≥ 0` and `x < 0`.

`translation/functions/` keeps two queries:

- `applications.smt2`: Bool/Int functions and predicates, mixed signatures, nested
  calls, compound Boolean arguments, quoted `Int.add`/`True` names, and unused
  parameters, and Bool/Int conditional arguments. Tests check argument order, missing mappings, and fresh parameters
  across nested reconstructions and separate inputs with reused names.
- `congruence.smt2`: the small contradiction `x = y` and `f(x) ≠ f(y)`.

`translation/quantifiers/` keeps two queries:

- `scopes.smt2`: alternating forall/exists, mixed Bool/Int binders, shadowing,
  premise-only and unused variables, quoted names, and quantified Boolean arguments.
  A `let` alias keeps an outer variable accessible under an inner binder with the
  same name. This checks native identity rather than name-based lookup.
  Conditional branches retain outer variables when their conditions introduce
  shadowed existential/universal binders.
- `quantified.smt2`: `∀ x, P x` together with `∃ x, ¬P x`, with a completed README proof.

The parser test also constructs native terms with a dangling variable and a
different variable with the same name. Both must fail scope validation, even when
the same subterm was already accepted under a quantifier.

`translation/chc/expected/Query.lean` is the reviewed output for `chc/lh_sum_rec.smt2`:
one existential relation and all three original clauses, followed by an unfinished
proof. Its source comments identify the original query and clause ranges.

`translation/chc/clauses.smt2` combines six relation declarations and fourteen clauses:
five bare facts, a quantified fact, seven rules, and a bare false assertion. It
covers mixed sorts, arithmetic, quoted names, unused relations/variables, chained
implications, and shadowed leading binders. Tests preserve argument and premise
order before and after flattening premise conjunctions. A nonlinear rule combines
three relation premises with arithmetic, nested conjunctions, and Boolean guards;
conjunctions inside a guard's `or` stay intact. Another rule combines xor and
Bool/Int distinct guards with nested operators in a relation argument.
Conditional guards and both Bool/Int conditional relation arguments are included;
relations and nested quantifiers hidden inside conditions remain rejected.
The unedited lh_sum_rec fixture
retains its three clauses with binder counts 3/5/3, heads k_1/k_1/false, and
relation-premise counts 0/1/1 under absent/sat/unsat/unknown status metadata.
Short invalid cases stay inline in `Horn.lean`. Separate checks distinguish a bound
Bool from a same-named nullary relation and reject a different native symbol with
the same printed name.

The translation test compares each complete formula with a handwritten Lean target.
Emitted absolute values use only core `if/then/else`; comparison chains retain
every adjacent pair. The parser test also checks their native binary structure.

`backend/Parser.lean` reuses these for logic and metadata variants. Its short
rejection cases live together in a table: each needs a separate parse because
validation stops at the first error. Checks cover declaration identity and error
locations; invalid input must never reach the inspection callback.
Div/mod remain rejected for zero and nonzero divisors, including inside supported
arithmetic. Real, array, and bitvector signatures, higher-order logic, and incorrect
application arities/types are also rejected.
Quantifier patterns, unsupported binder sorts (even when unused), unsupported
operators inside quantified bodies, and quantifiers in `QF_*` logics are rejected
before file generation.

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
