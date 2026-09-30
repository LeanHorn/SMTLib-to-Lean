# Tests

Run the complete translator suite from any working directory:

```sh
tests/translation/run-demo.sh
```

This builds the CLI and Lean tests, runs each Lean test executable, then runs
`cli.py`. Python 3 is required. Generated files go into temporary directories.

## What each layer checks

| Command | Coverage |
| --- | --- |
| `lake exe testSource` | Exact source bytes, command boundaries, quoting, UTF-8, line endings, labels, and malformed input |
| `lake exe testParser` | Supported terms and configuration, binding identity, definitions, aliases, hints, session scopes, and rejection locations |
| `lake exe testReconstruction` | One closed proposition reconstructed by upstream handlers and checked by Lean's kernel |
| `lake exe testHorn` | Relation identities, ordered clause arguments, leading binders, theory guards, false heads, and unsupported Horn forms |
| `lake exe testTranslation` | Handwritten expected propositions, operator semantics, capture avoidance, cache isolation, re-elaborated output, and exact axiom dependencies |
| `lake env python3 tests/cli.py` | CLI results, standalone file compilation, golden outputs, completed proofs, diagnostics, and output protection; build `smt2lean` first |

The Lean test modules stay in `backend/`. Semantic tests elaborate generated text
in memory and compare it with the reconstructed expressions. The CLI suite owns
filesystem checks: it compiles both `Query.lean` and its statement section,
refuses existing destinations, and preserves edited proofs. Core-only outputs
are checked without package search paths; Real outputs use the pinned Mathlib.

Statement checks reject admissions and query-specific axioms, including transitive
dependencies. Classical conditionals may use `propext`, `Classical.choice`, and
`Quot.sound`. Proof templates use `sorry`; the four completed README proofs must
compile without it. The integer proof uses `propext`; the other three are axiom-free.

## Combined translation fixtures

| Directory | Cases |
| --- | --- |
| `translation/bool/` | Contradiction, connectives, empty assertions, solver options, and metadata |
| `translation/int/` | Exact literals beyond 64 bits, arithmetic including div/mod, comparisons, distinct, conditionals, and contradictory bounds |
| `translation/real/` | Exact rationals, arithmetic, comparisons, conditionals, mixed function signatures, bindings, and shared division-at-zero interpretations |
| `translation/bitvec/` | Modular arithmetic, bitwise operations, comparisons, width changes, shifts, rotations, division/remainders, Int conversions, and overflow predicates |
| `translation/sorts/` | Nonempty uninterpreted carriers, mixed functions, aliases, definitions, equality/distinct, conditionals, and quantifiers |
| `translation/functions/` | Mixed Bool/Int functions and predicates, quoted names, argument order, unused parameters, and congruence |
| `translation/bindings/` | Simultaneous/nested let, nonrecursive definitions, sort aliases, named subterms, and capture avoidance |
| `translation/quantifiers/` | Nested forall/exists, shadowing, Bool binders, unused variables, and quantifier hints |
| `translation/chc/` | Facts, multiple relation premises, guards, false heads, definitions, named clauses, and relations over uninterpreted sorts |
| `translation/sessions/` | SMT/CHC checks with push/pop, temporary assumptions, resets, local/global term and sort declarations, reused symbols, and shared helpers |

Quantifier hints `:pattern`, `:no-pattern`, and `:qid` are checked and removed without
changing the proposition. Unsupported annotations and operators still fail. Short
invalid scripts remain inline in the test modules: each requires a separate parse
because validation stops at its first error.

The session tests compare every goal with a handwritten proposition. They check
that popped declarations disappear, redeclarations get fresh identities, repeated
checks remain separate, and a later failure produces no output. The strict
single-query API also retains tests for its callback-after-validation contract.

Five `expected/Query.lean` files preserve reviewed output for the Boolean, integer,
function, quantified, and `chc/lh_sum_rec.smt2` examples. Metadata variants must leave
code unchanged after source comments are removed. Root `demo.smt2` and
`demo-chc.smt2` provide commented feature tours; the commands are in the main README.

## Original frontend queries

```sh
tests/run.sh   # Replay the original SMT/CHC corpus through z3.
```

This separate script compares solver results with the answers recorded in the
inputs. It requires z3 and does not test Lean translation. Translator tests never
invoke cvc5's solving commands. `tools/fqhorn2chc.py` converts liquid-fixpoint Horn
files into the SMT-LIB fixtures described below.

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

## Temporary assumptions

`translation/sessions/assuming.smt2` checks temporary positive/negative Boolean
literals, definitions, empty assumption lists, duplicates, quoted names, and
scoped redeclarations. The Lean suite compares every goal with a handwritten
proposition; CLI tests compile the output and reject invalid later assumptions.

The input follows [SMT-LIB 2.6, section 4.2.5](https://smt-lib.org/papers/smt-lib-reference-v2.6-r2024-09-20.pdf):
assumptions are user-declared/defined Boolean constants or their negations.
They apply to one check only. Neither check command invokes the solver.
HORN negated literals become safety clauses and still undergo Horn validation.

## Reset and observation commands

`translation/sessions/resets.smt2` combines local/global declaration lifetimes,
scoped definitions and aliases, both resets, temporary assumptions, and symbol reuse.
`:global-declarations` must be set before the logic or declarations. `reset` clears
all state and options; `reset-assertions` clears assertions and scopes, retaining
declarations/definitions only in global mode. Query numbering continues across resets.

The session CLI parses observational `get-*` commands for models, values, proofs,
cores, assumptions, assignments, assertions, options, and info, and records them as
`Not executed` comments. It never produces solver responses. Result-dependent
requests require a preceding check in the current context. Requests cannot introduce
`:named` bindings. The strict single-query
API retains its original command restrictions.

## Uninterpreted sorts

`translation/sorts/uninterpreted.smt2` combines ordinary SMT operations over three
carriers; `translation/chc/uninterpreted.smt2` combines Horn clauses over two.
`translation/sessions/sorts.smt2` checks sort identities and lifetimes across eight
queries, including aliases, definitions, local scopes, and both reset modes.

Each `(declare-sort S 0)` introduces an arbitrary Lean `Type` with a `Nonempty`
requirement. Refutations quantify carriers universally; CHC model existence
quantifies them existentially. Sort constructors with positive arity are rejected.
The nonemptiness requirement follows [SMT-LIB 2.6, section 5.1](https://smt-lib.org/papers/smt-lib-reference-v2.6-r2024-09-20.pdf).

The Lean tests compare complete statements with handwritten targets, including
unused carriers. Six completed CLI proofs distinguish nonempty, singleton,
two-element, and infinite domains, plus satisfiable and impossible Horn models.
They supplement the four existing completed proofs. Unsupported Horn declarations
and later sort-scope failures still reject the entire session before output.

## Integer division and modulo

`translation/int/division.smt2` combines signed arithmetic, chained division,
zero divisors, definitions, let, functions, quantifiers, and name collisions.
`translation/chc/division.smt2` uses both operators across guards, relation arguments,
and clauses, together with an uninterpreted carrier.

The encoding follows the [SMT-LIB integer theory](https://smt-lib.org/theories-Ints.shtml):
nonzero divisors use Euclidean division; the remainder is nonnegative even for
negative operands. At zero, separate `Int → Int` parameters preserve unspecified
results consistently across all occurrences. Refutations quantify these functions
universally; CHC models quantify them existentially before the relations.

The Lean tests prove 277 signed/large-number arithmetic cases, deriving the small
expected quotients/remainders by an independent search over multiplication and order.
They compare complete statements against handwritten targets and check assumption,
scope, and reset isolation. Six completed CLI proofs distinguish arbitrary zero
values, input dependence, division/modulo independence, and congruence across
quantifiers and clauses. Statement definitions still reject admitted axioms.

All four original `chc/` files now translate and elaborate with **28 clauses**:
`lh_sum_rec` (3), `lh_abs_neg` (5), `flux_sum_off_by_one` (5), and `flux_bsearch` (15).
This checks translation, not satisfiability or Flex proofs. Regression rejection
cases now use unsupported exponentiation instead of the newly supported div/mod.

## Exact Real arithmetic

`translation/real/arithmetic.smt2` combines Real expressions with functions,
quantifiers, definitions, aliases, let bindings, and an uninterpreted carrier.
`translation/chc/real.smt2` uses Real guards and relation arguments across three
clauses. The usual Horn restrictions still apply.

The encoding follows [SMT-LIB Reals](https://smt-lib.org/theories-Reals.shtml).
Real means Mathlib's `Real`, not rational numbers or floating point. Decimals are
read as exact native rationals and emitted as ratios of Real numerals. `/` folds
left, and a shared `Real → Real` function represents its unconstrained result at
zero. This function is universal in refutations and existential in Horn models,
independently of the integer division and modulo choices.

Real files import `Mathlib.Data.Real.Basic` from Mathlib revision
`db584cd6d46c92f209a44c0f1c829460d327499d`, already pinned in `lake-manifest.json`.
Check them with `lake env lean`. Completed arithmetic proofs additionally import
`Mathlib.Tactic.NormNum`; generated statements do not require that tactic import.

Tests cover 13 exact arithmetic cases, including decimal fractions beyond machine
precision, signed division, comparison chains, and large numerals. Nine completed
proofs check these cases, composite divisors, numerator-dependent zero choices,
congruence, quantifier sharing, independence from Int zero choices, a linear Horn
invariant, and consistent zero choices across clauses. Handwritten propositions
also check Real quantifiers (including an irrational-root formula), shadowing,
five assumption/reset snapshots, and import selection across scopes.

cvc5 can retain Int numerals in Real arithmetic; the translator reconstructs these
at the expected Real type without contaminating the Int term cache. Int/Real
conversions are covered below. Exponentiation, algebraic-number constants,
and transcendental operators remain rejected. Earlier unsupported-Real cases exercise unsupported
String sorts, while accepted Real cases have their own checks.

## Mixed Int/Real arithmetic

`translation/real/conversions.smt2` combines explicit and implicit casts, floor,
integrality, aliases, functions, definitions, simultaneous let, shadowed binders,
and shared zero interpretations. `translation/chc/conversions.smt2` uses these
operations in guards and relation arguments across three clauses.

The encoding follows [SMT-LIB Reals_Ints](https://smt-lib.org/theories-Reals_Ints.shtml):
`to_real` is exact, `to_int` is `Int.floor`, and `is_int x` means
`x = (Int.floor x : Real)`. In particular, `to_int(-1.7)` is `-2`.
Floor and integrality outputs import `Mathlib.Algebra.Order.Archimedean.Real.Basic`;
casts alone retain the smaller Real import. No dependency pins change.

Tests compare complete SMT/CHC propositions, all eight mixed logic profiles, and
four assumption/scope/reset snapshots. Eight completed CLI proofs cover twelve
exact boundary cases, Int round trips, the integer-witness meaning of `is_int`,
a nonintegral fraction, implicit casts, floor at an arbitrary zero-division value,
a Horn model, and an impossible Horn model. Negative floors are checked using
their defining inequalities. Invalid conversions and later unsupported commands
must fail without producing partial output.

## Fixed-width bitvectors

`translation/bitvec/arithmetic.smt2` combines exact literals, arithmetic, every
supported bitwise/comparison operator, aliases, functions, definitions, simultaneous
let, mixed signatures, and shadowed binders. `translation/chc/bitvec.smt2` uses
bitvectors in guards and relation arguments across four clauses. Both emit
`import Init`; standalone tests remove the package search path.

The encoding follows [SMT-LIB bitvectors](https://smt-lib.org/theories-FixedSizeBitVectors.shtml)
and the [QF_BV definitions](https://smt-lib.org/logics-all.shtml#QF_BV).
`(_ BitVec w)` becomes `BitVec w` for positive widths. Arithmetic wraps modulo
`2^w`; signed comparisons use two's complement, while unsigned comparisons use
natural values. `bvcomp` returns `BitVec 1`, independently of SMT Bool → Lean Prop.
NAND, NOR, XNOR, and `bvcomp` retain named, kernel-checked helpers in output.

The Lean tests prove 7,560 closed operator cases in the kernel: exhaustive operands
at widths 1–4, plus zero, one, and signed/unsigned boundaries at widths 32/64/129.
Expected results use integer arithmetic and individual binary digits, independently
of Lean's BitVec operators. Whole SMT/CHC targets and four session snapshots are
compared with handwritten propositions and with their reloaded output.

Five completed CLI proofs check 21 exact/associative/boundary cases, signed versus
unsigned ordering, function congruence, a Horn model, and wraparound that makes a
Horn model impossible. Invalid widths, overflowing decimal literals, stale aliases,
and later unsupported operators must fail before output. BV division/remainder
and BV/Int conversions and overflow predicates are covered below.

`translation/bitvec/widths.smt2` and `translation/chc/widths.smt2` combine concat,
extract, zero/sign extension, and repeat through functions, definitions, quantifiers,
and Horn guards/arguments. The Lean tests check 1,647 additional cases against
natural-number arithmetic: every valid slice at widths 1–4, mixed-width concat,
zero-bit extension, repetition, and boundaries at widths 32/64/129. Whole targets
and three assumption/pop/reset snapshots are compared with handwritten propositions.

Five additional completed CLI proofs cover 22 exact cases, symbolic concat/extract
round trips, distinct zero/sign extension results, and satisfiable/impossible Horn
models. Output compiles with only `Init`. Invalid indices, zero repetitions, wrong
result widths, and unsupported operators hidden inside width changes must fail;
a later error leaves no output. Core concat/repeat width proofs use the permitted
foundational axioms `propext` and `Quot.sound`, with no admissions.

```sh
lake exe smt2lean tests/translation/bitvec/widths.smt2 --out bitvec-widths-demo
lake env lean bitvec-widths-demo/Query.lean
```

`translation/bitvec/shifts.smt2` and `translation/chc/shifts.smt2` combine variable
`bvshl`/`bvlshr`/`bvashr` amounts with indexed `rotate_left`/`rotate_right`,
functions, definitions, binders, and Horn guards/arguments. The shift helpers bound
the unsigned amount by the operand width to avoid huge intermediate integers.
Three general Lean proofs check equivalence to the unbounded core operations.

The Lean suite checks 2,016 cases against an independent bit-by-bit reference:
exhaustive operands/amounts at widths 1–4, boundaries at 32/64/129, oversized shifts,
and rotations through index 4294967295. Whole targets and four query snapshots
check scope, helper emission, and re-elaboration. Five completed CLI query proofs
cover 24 exact cases, variable amounts, signedness, and possible/impossible Horn
models. Standalone files import only `Init`.

Indices above 4294967295 are rejected before native parsing: the pinned cvc5
silently saturates them. Regression cases include quoted operator names, erased
let bodies, unused definitions, comments/strings, malformed indices, wrong widths,
and later failures that must leave no output.

```sh
lake exe smt2lean tests/translation/bitvec/shifts.smt2 --out bitvec-shifts-demo
lake env lean bitvec-shifts-demo/Query.lean
```

## Bitvector division and remainders

`translation/bitvec/division.smt2` and `translation/chc/bv-division.smt2` combine
`bvudiv`, `bvurem`, `bvsdiv`, `bvsrem`, and `bvsmod` with bindings, functions,
quantifiers, and Horn guards/arguments. Generated files use core `smtUDiv`, `%`,
`smtSDiv`, `srem`, and `smod`, preserving SMT-LIB's specified zero-divisor behavior.
Signed division truncates toward zero; nonzero `bvsrem` follows the dividend's
sign, while nonzero `bvsmod` follows the divisor's sign. Signed overflow wraps.

The Lean suite proves 2,240 cases against an independent integer oracle, covering
every operand pair at widths 1–4 and boundaries at widths 32/64/129. Whole SMT/CHC
targets are compared with handwritten propositions and re-elaborated output.
Five completed CLI proofs check 22 explicit cases, remainder signs, zero divisors,
a Horn overflow model, and an impossible Horn modulo model. All output compiles
with only `Init`; the core operators use the already permitted `propext`.
Invalid arities/widths and hidden unsupported conversions fail before output.

```sh
lake exe smt2lean tests/translation/bitvec/division.smt2 --out bitvec-division-demo
lake env lean bitvec-division-demo/Query.lean
```

## Bitvector/Int conversions and overflow predicates

`translation/bitvec/conversions.smt2` and `translation/chc/bv-conversions.smt2`
combine conversions and five overflow predicates with definitions, simultaneous
let, quantifiers, mixed function signatures, and Horn guards/arguments.
`int_to_bv`/`int2bv` wrap modulo 2^w; `ubv_to_int`/`bv2nat` return a nonnegative
Int, and `sbv_to_int` interprets two's complement. For eight bits, −1 becomes #xff;
#xff converts back to 255 unsigned or −1 signed. Overflow predicates cover
negation and signed/unsigned addition and multiplication.

The Lean suite proves 2,744 cases using an independent integer oracle: exhaustive
small widths 1–4, two wraps in either direction, and boundaries at 32/64/129 bits.
It compares full SMT/CHC targets and four scoped query snapshots with handwritten
propositions, and checks composition with Real floor/casts and arbitrary integer
division at zero. Six completed CLI proofs cover 22 explicit cases, a symbolic
signed round trip, signedness, overflow, and possible/impossible Horn models.
Pure BV/Int output compiles using only `Init`.

Zero, negative, malformed, or oversized conversion widths and wrong operand
sorts/arities fail. The source guard rejects widths above 4294967295 before cvc5
can silently saturate them, including aliases, quoted names, erased let terms,
unused definitions, and observational requests. Text inside strings/comments is
unaffected. Later errors leave no output. Subtraction/division overflow predicates
remain rejected; previous unsupported-conversion tests now reject exponentiation.

```sh
lake exe smt2lean tests/translation/bitvec/conversions.smt2 --out bitvec-conversions-demo
lake env lean bitvec-conversions-demo/Query.lean
```
