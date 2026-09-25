# SMT-LIB to Lean: roadmap, with Stage 1 as the current focus

**Historical exploration; execution plan superseded.** The user's revised stages
are competition translation, frontend tooling, then Flex integration. The current
ordered backlog is [PR-PLAN.md](PR-PLAN.md); technical evidence and architecture are
in [FLEX-ARCHITECTURE.md](FLEX-ARCHITECTURE.md). The narrower stage labels and
Mathlib-free scope below describe the earlier proposal, not the current milestones.
Its semantic observations remain useful background.

Reviewed 2026-09-24 against the existing plan, this repository, and lean-smt
commit `5bdc51674065a074ece67b04e10024e9f426ec1f`.

## Recommendation

Build a standalone importer that produces an editable Lean project from an SMT-LIB
session without requiring a solver result. Keep the Lean 4 implementation and
Mathlib-free generated output proposed in the existing plan. Investigate lean-smt
reuse in a one-day spike before committing to a parser/reconstruction backend.
Do not make the escape hatch depend on successfully running an SMT solver.

The Stage 1 product promise is:

> Turn these real LiquidHaskell and Flux queries into readable, well-typed Lean
> statements, with the original assumptions and an explicit place to continue
> interactively—even when no solver answer is available.

This is translation, not proof certification. A file containing `by sorry` can
typecheck even when its theorem is false. Some current fixtures intentionally
represent failed verification attempts. Preserve those faithfully; never promise
that every translated safety statement is provable. Proving the generated queries
remains outside Stage 1.

## What lean-smt already provides

The original plan's description of lean-smt as only going in the opposite
direction is incomplete. Its current source contains the following infrastructure.

| Component | What it does | Decision for this project |
| --- | --- | --- |
| `Smt.Reconstruct.reconstructSort` / `reconstructTerm` | Extensible conversion from cvc5 sorts/terms to Lean `Expr` | Evaluate reuse for supported theories in the spike |
| cvc5 `InputParser`, used by `runQuery` | Reads SMT-LIB commands and maintains a symbol manager | Candidate parsing/sort-checking backend; intercept commands instead of invoking solver checks |
| `solveAndReconstructProof` and the `reconstruct` tactic | Accept SMT-LIB text, run cvc5, reconstruct results/proofs | Useful adjacent infrastructure, but not the importer's entry point |
| `smt` tactic and proof reconstructors | Discharge existing Lean goals and expose reconstruction holes | Optional future proof assistance after translation |
| Datatype reconstruction | Looks up existing Lean datatype/constructor declarations | Does not generate this project's parametric datatype declarations |
| lean-auto's `SMTSexp` / `SMTParser` | Pure Lean S-expression parsing and SMT-term reconstruction using a supplied symbol map | Inspect the lexer for lightweight reuse; do not assume the term parser handles arbitrary input semantics |

The high-level reconstruction API requires the relevant Lean symbols to exist
already. It also still solves when `prove := false`; that flag disables proof
production, not solving. Its session runner invokes commands and the solver path
performs a final `checkSat`, rather than exporting every check as a separate Lean
obligation. Source spans, scoped declaration generation, all-query extraction,
readable names, output packaging, and CHC task representation remain our work.
The inspected reconstructors do not supply the required array support or a general
datatype selector/tester importer.

Upstream pins Lean 4.33.0; this project pins 4.33.1. Its main package requires
lean-auto, lean-cvc5, and Mathlib; its README advertises an experimental
`no_mathlib` branch. A translator dependency and a generated-project dependency
are separate decisions: using cvc5 while translating need not force generated
Lean files to depend on cvc5 or lean-smt.

Sources: [reconstruction APIs](https://github.com/ufmg-smite/lean-smt/blob/5bdc51674065a074ece67b04e10024e9f426ec1f/Smt/Reconstruct.lean),
[datatype reconstruction](https://github.com/ufmg-smite/lean-smt/blob/5bdc51674065a074ece67b04e10024e9f426ec1f/Smt/Reconstruct/Datatype.lean),
[dependencies](https://github.com/ufmg-smite/lean-smt/blob/5bdc51674065a074ece67b04e10024e9f426ec1f/lakefile.lean),
[toolchain](https://github.com/ufmg-smite/lean-smt/blob/5bdc51674065a074ece67b04e10024e9f426ec1f/lean-toolchain),
[README](https://github.com/ufmg-smite/lean-smt/blob/5bdc51674065a074ece67b04e10024e9f426ec1f/README.md).

The pinned [lean-cvc5 API](https://github.com/abdoo8080/lean-cvc5/blob/7e3365990661b697ccb30e92d6912f4cc6589322/cvc5.lean)
exposes `Command.getCommandName` and `Solver.getAssertions`, making a parse-only
adapter plausible without calling the existing solver entry point. Its native
build cost still needs measurement. The lightweight alternative to inspect is
[lean-auto's lexer](https://github.com/leanprover-community/lean-auto/blob/eb9c694863439fb55800228bc4c7babe42b089bf/Auto/Parser/SMTSexp.lean);
its [term parser](https://github.com/leanprover-community/lean-auto/blob/eb9c694863439fb55800228bc4c7babe42b089bf/Auto/Parser/SMTParser.lean)
also assumes existing symbols and contains coercions designed for round trips.

### Reuse spike: bounded decision, not a prerequisite research project

Use a separate experiment pinned to the inspected revision. Try parsing all 12
fixtures without executing `check-sat` or requiring any verdict. For one arithmetic
snapshot, construct the Lean declaration context, reconstruct its assertions, and
emit a self-contained Lean statement. Probe the array-map extension, scoped symbol
redeclarations, qualified constructors, and selectors separately. Record native
build requirements and toolchain compatibility.

Adopt the backend only if adapting it preserves the input dialect and source
mapping and demonstrably reduces work. If not, proceed with the small Lean
S-expression parser and typed IR from the existing plan, using upstream theory
mappings as references. Do not build two production backends in Stage 1. Any copied
code must retain the applicable upstream license and attribution.

## Current baseline

The repository has a Lake skeleton, a CLI that prints its arguments, a small
prelude, and an empty generated-project scaffold. It does not yet translate queries.
Both Lake projects build; `tests/run.sh` passes with Z3 4.15.4.

| Input under `tests/` | Checks | Recorded unsat | Recorded sat |
| --- | ---: | ---: | ---: |
| `smt/flux_matrix_index_nonlinear.smt2` | 1 | 1 | 0 |
| `smt/flux_bsearch_overflow.smt2` | 72 | 37 | 35 |
| `smt/lh_kvar_defunc.smt2` | 16 | 4 | 12 |
| `smt/lh_mergesort.smt2` | 206 | 41 | 165 |
| `smt/lh_sets_neg.smt2` | 5 | 4 | 1 |
| `smt/flux_bitvec_page_align.smt2` | 2 | 2 | 0 |
| `smt/lh_ple_list_len_adt.smt2` | 14 | 5 | 9 |
| `smt/lh_polyset_adt_sets.smt2` | 1 | 1 | 0 |
| `chc/flux_bsearch.smt2` | 1 | 0 | 1 |
| `chc/lh_sum_rec.smt2` | 1 | 0 | 1 |
| `chc/flux_sum_off_by_one.smt2` | 1 | 1 | 0 |
| `chc/lh_abs_neg.smt2` | 1 | 1 | 0 |
| **Total** | **321** | **97** | **224** |

Keep the SMT subtotal (317 checks: 95 unsat, 222 sat) separate from the CHC subtotal
(four checks: two sat, two unsat). Their verification interpretations differ.

## Semantic contract and corrections to the old plan

1. **Separate statements from unfinished proofs.** Emit canonical query/obligation
   definitions in `Generated/`; keep editable theorem skeletons in `Proofs/`.
   `Generated/` must elaborate without `sorry`, unbound symbols, or axioms asserting
   query validity. `Proofs/` may contain explicitly reported `sorry`s. Regeneration
   must not overwrite users' proofs. Do not use unfinished theorems as hypotheses
   for other generated queries.
2. **Keep result metadata separate from meaning.** For an ordinary VC, the task is
   to refute the active assertions: `∀ symbols, A₁ → … → Aₙ → False`. Recovering
   `H → G` from assertions `H` and `¬G` is a classical equivalence, not evidence that
   `G` is true. Recorded `unsat` may select a proof template; recorded `sat` remains
   a candidate reported invalid by the solver; missing/unknown results remain open
   tasks. Comments and `:status` fields are never Lean proof evidence. Translation
   must still work when recorded answers are removed.
3. **Model underspecified operations faithfully from the start.** Do not replace
   SMT integer division at zero with Lean's fixed answer. For the current corpus,
   supporting reachable divisions by nonzero literals and rejecting other divisors
   is an acceptable narrower implementation. Broader support needs shared, explicit
   interpretation parameters such as `divZero : Int → Int`, with a wrapper choosing
   that function at zero and Euclidean division otherwise. Do likewise for `mod`.
   Universally quantify these choices in validity/refutation tasks; existentially
   quantify them in model-existence tasks. Never choose a fresh result per occurrence.
4. **Handle partial datatype selectors as total but underspecified functions.**
   Preserve constructor equations and parameterize wrong-constructor results by
   the selector's input. A single arbitrary constant is enough for the current
   list selectors' nil case, but is not a general ADT solution. Avoid replacing
   arbitrary interpretations by one global chosen implementation.
5. **Scope all bindings.** Declarations, definitions, sort aliases, datatypes, and
   assertions belong to the session environment. Use unique internal binding IDs,
   capture definition bodies against the environment at definition time, and take
   an immutable snapshot at every check. Equal raw names/signatures in sibling
   scopes do not make them the same binding. The current corpus reaches push depth
   four and contains declarations inside those scopes.
6. **Reject unsupported semantics visibly.** Do not silently drop assertions or
   replace reachable unsupported operators with arbitrary functions. Solver tuning
   options can be ignored explicitly; semantic options such as global declarations
   must be implemented or rejected when encountered. Prune unused definitions only
   after resolving dependencies. Record any unsupported unused preamble separately.
7. **Do not equate parser validation with translation validation.** SMT round trips
   exercise parsing/session handling; Lean builds exercise elaboration. Neither
   alone establishes that the Lean statement means the same thing as the input.
   Add independently reviewed expected statements and focused semantic regressions.

Keep Bool-to-Prop, function arrays, core `Int`, and core `BitVec` for the supported
fragment. `SmtArray Int Prop` is legal with the current prelude (`Prop : Type`).
In Stage 2, uninterpreted carriers must be parameters with nonemptiness assumptions;
do not pick one opaque carrier and mistake validity over it for validity over all
SMT interpretations. Do not substitute `Rat` for general SMT `Real`.

Quantified arrays and complete strings need their own semantic support gates.
Function arrays do not automatically establish adequacy for every quantified
[ArraysEx](https://smt-lib.org/theories-ArraysEx.shtml) problem, whose axioms do not
require the array domain to contain every mathematical function. Lean `String`
also has a different character domain from the complete
[SMT UnicodeStrings theory](https://smt-lib.org/theories-UnicodeStrings.shtml).
Support for the current array fragment and unused string preamble does not count
as support for those broader theories.

The division issue follows the [SMT-LIB integer theory](https://smt-lib.org/theories-Ints.shtml).
Selector behavior is specified in §5.3 of the
[SMT-LIB 2.7 reference](https://smt-lib.org/papers/smt-lib-reference-v2.7-r2025-07-07.pdf).
These are obligations of a reverse importer even when an upstream Lean-to-SMT
encoding safely makes a more specific choice for its own terms.

## Stage 1: the complete current corpus and an excellent demo

### Architecture

```text
SMT-LIB text + optional frontend metadata
    → source-positioned parsing
    → scoped command interpreter
    → sorted terms + one snapshot per check
    → canonical query/task representation
    → readable Lean definitions + source map
    → separate editable proof templates + project manifest
```

Retain the existing plan's `Sexp`, `Syntax`, `Env`, `Elab`, `Goal`, `Names`, and
`Print` module split. Add CHC task construction above the same typed IR. A chosen
external parser is an adapter at the first two boundaries, not the owner of the
product's goal semantics or output format.

### Implementation order and acceptance gates

| Milestone | Work | Exit condition |
| --- | --- | --- |
| M0: contract and reuse decision | Freeze the corpus manifest; define result/polarity metadata; audit prelude; run the bounded lean-smt spike | Backend decision recorded; root and output builds pass; semantics policy agreed in code/docs |
| M1: one complete path | Parser, source positions, declarations/definitions, Int/Bool/UF, scopes, dependency pruning, basic names, typed IR, emitter | `flux_matrix_index_nonlinear` produces its one readable index-bound obligation; output builds without running a solver |
| M2: incremental sessions | Exact push/pop, shadowing, capture-safe definition expansion, quantifiers, all checks, status handling | Binary search, defunctionalization, and mergesort work too: cumulative 295/321 checks |
| M3: arrays and bitvectors | const/store/select/map-or; the exact bitvector operations in the fixtures | Sets and page alignment bring cumulative coverage to 302/321 checks |
| M4: parametric datatypes | Declarations, constructors, selectors, testers, ascriptions, nested type instances | Both ADT fixtures work: all 317 ordinary SMT checks elaborate |
| M5: current CHCs | Existential invariant interpretations and explicit refutation tasks over the same typed clauses | All four CHC files work: 321/321 checks represented |
| M6: demo release | Stable names/IDs, source links, proof-file preservation, manifest, reproducible generation, CI, README walkthrough | Fresh checkout can generate/check all 12 inputs and open an editable demo with one documented command |

M1 need not implement every unused common-preamble body, but must identify its
signature, dependencies, and unsupported status accurately. Do not let unused
string helpers block the first arithmetic demo. Implement every reachable feature
needed by the whole corpus before declaring Stage 1 complete.

### CHC scope in Stage 1

For these four normalized `HORN` fixtures, retain a canonical statement of the form
`HasSolution := ∃ P₁ … Pₖ, clause₁ ∧ … ∧ clauseₙ` over the intended background
domains. Universally quantify each clause's own variables, including variables
appearing only in its body. Quantify other uninterpreted symbols too if present.

Offer `HasSolution` as the invariant-existence task for the two known sat fixtures
and `¬ HasSolution` as the no-model task for the two known unsat fixtures. Name the
task explicitly. Negating invariant existence is not the same artifact as producing
a program counterexample. Keep the underlying clause system identical regardless
of status metadata. For an unknown CHC result, default the interactive safety task
to invariant existence and label it as an unproved task.

This handles today's inputs without claiming to solve general CHC semantics.
Stage 4 can add least-model reasoning, derivation/counterexample evidence, witness
import, recursive datatype theory, and richer frontend contracts. Basic CHC model
existence must already be represented correctly in Stages 1–3.

### Demo experience

Proposed CLI, to implement rather than assume available today:

```sh
lake exe smt2lean --out examples tests/smt/*.smt2 tests/chc/*.smt2
./scripts/check.sh
./scripts/demo.sh
```

The demo command should check the environment, build/generate as needed, display
the 12-file table, and print exact Lean files to open. Require elan/Lean as a
documented prerequisite; translation and generated-project typechecking must not
require Z3/cvc5 to find a solution. Keep solver replay in the developer/CI check.

Open with the two small Flux bitmask goals. Show the original source excerpt, the
SMT assertion, and a readable Lean goal with its local hypotheses visible at
`sorry`. Then show `lh_sets_neg` retaining its failing check, the PLE list-length
query gaining enough equations across the session, and `lh_sum_rec` exposing an
invariant to choose. Keep mergesort as evidence that the tool handles a substantial
session, rather than the first screen of the demo.

Commit generated examples and small proof templates. Use stable query IDs and a
manifest linking input path/hash, check index, source span, recorded status, task
polarity, generated declaration, and semantic support status. Basic readable names
belong in M1; polishing names and formatting belongs in M6. A `--check N` selection
option is useful for opening one obligation from a long transcript.

Do not describe current fixtures as actual solver timeouts: they have recorded
answers. Demonstrate independence from results by translating a copy with answer
comments removed. A recorded real timeout can become a later frontend fixture.

### Stage 1 release checks

- All 12 input files and exactly 321 checks are represented; none are silently skipped.
- Canonical generated definitions elaborate with no errors and no `sorry` or
  query-validity axioms. Only designated proof templates contain admitted goals;
  report these as unfinished, never as verified.
- All input status counts and source/check mappings match the frozen manifest.
- Hand-reviewed expected goals cover arithmetic, arrays, bitvectors, ADTs, and CHCs.
- Focused regressions cover popped assertions/declarations, rebinding, definition
  capture, Bool equality, nonzero and zero division, selector behavior, and polarity.
- Z3 replay continues to match recorded results. Optional SMT round trips are an
  additional parser check, not the semantic-correctness criterion.
- Repeated generation is deterministic; regeneration preserves edited proof files.
- The output project builds on the pinned toolchain independently of the translator.
- Record clean-build and incremental-build times; if a large session causes poor
  editor latency, split generated modules without changing query IDs.

**Immediate next implementation deliverable:** complete M0, then M1. One real
query should travel from its unedited transcript to an inspectable Lean goal
before expanding the theory surface.

## Stage 2: grow support through real frontend queries

The current tests are a regression floor, not the definition of universal support.
Collect new queries, classify failures, implement the most valuable missing
feature, minimize a representative regression, and repeat.

1. Expand LiquidHaskell/Flux examples, then add one frontend at a time from
   Dafny/Boogie, Why3, F*, Verus, and SMT-exporting model checkers. Verify the current
   export mechanism when integrating each frontend rather than hard-coding old
   command-line flags into this roadmap.
2. Prioritize `let`, annotations/named assertions, uninterpreted nonempty sorts,
   `check-sat-assuming`, more session commands, and broader quantifier coverage.
   Then expand bitvectors, arrays and ADTs based on measured corpus failures.
3. Treat Reals, complete strings/regular expressions, recursive definitions, and
   floating point as distinct semantic projects. An optional Mathlib profile is
   reasonable for Reals. Recursive equations need an explicit soundness contract;
   do not fabricate terminating Lean definitions or add unchecked axioms.
4. Introduce a small frontend metadata sidecar: original program location, assertion
   name, intended outcome, and which checks are final obligations versus inference
   probes. SMT-LIB alone cannot recover all of this information.
5. Publish per-frontend counts for parsing, sort checking, complete translation,
   Lean elaboration, unsupported semantics, and resource failures. Only count a
   fixture as supported when all its requested checks pass the contract.

Exit when several independently generated frontend suites work without manual SMT
editing and the add-fixture → diagnose → implement → check loop is routine.
Proof automation and feeding Lean proofs back into original frontends remain
separate integrations; a generic SMT importer alone cannot provide the latter.

## Stage 3: competition-scale coverage

Pin a specific SMT-COMP benchmark selection or SMT-LIB release and a CHC-COMP
edition, recording hashes, selection rules, and licensing. The full SMT-LIB archive
and the competition's selected inputs are different denominators. Use the official
[SMT-LIB benchmark index](https://smt-lib.org/benchmarks.shtml) and
[CHC-COMP benchmark/format links](https://chc-comp.github.io/).

Start with integer arithmetic/UF/arrays/ADTs and CHC LIA tracks, then BV/arrays and
quantified combinations; expand to Reals and strings as Stage 2 support becomes
ready. For initial engineering targets, aim at 90% complete elaboration in chosen
integer/UF tracks and CHC LIA tracks, and 80% in chosen BV tracks. These are proposed
targets, not measured coverage and not evidence of covering most of all competitions.

Run an isolated worker per benchmark with wall-time, memory, and Lean heartbeat
limits. Cache by input hash, translator revision, prelude revision, and toolchain.
Collect JSONL results distinguishing parse errors, sort errors, unsupported
semantics, translation errors, Lean errors, and resource limits. Count a partially
translated incremental file as incomplete. Report query counts separately from
file counts; report failures and exclusions explicitly.

Use shared subterms and split modules to manage size, with stable names and source
maps. Never increase elaboration limits blindly without recording the cost. Run
semantic regressions alongside the benchmark driver and audit representative output
per feature; huge numbers of files containing `sorry` provide little evidence of
translation correctness by themselves.

Define the eventual claim “most SMT-COMP and CHC-COMP benchmarks” before announcing
it: for example, at least 90% of each pinned competition selection completes
faithful supported translation and Lean elaboration within declared limits, with
per-track figures alongside the overall figures. Report uncovered theories and
timeouts in the denominator. If only selected tracks meet the threshold, say so.

Stage 3 CHC coverage uses the model-existence/refutation representation already
introduced above. It does not require implementing a CHC solver or proving every
benchmark. Richer CHC proof and counterexample workflows are the later Stage 4.
