# Ordered PR backlog: SMT/CHC translation, frontend tooling, Flex

Updated 2026-09-25. This is the current execution plan and supersedes the earlier
stage numbering in ROADMAP.md and FLEX-ARCHITECTURE.md.

Each checkbox is one numbered PR-sized task. Checked means its implementation is
present in the working tree; it does not mean committed, merged, or user-reviewed.

## The user's stages

1. Translate every benchmark/query in pinned SMT-COMP and CHC-COMP selections into
   faithful Lean statements with optional `sorry` theorem templates.
2. Supply tooling that lets existing frontends export unresolved queries into Lean.
3. Run translated CHCs through Flex and maintain a reproducible progress anchor.

## Scope and merge rules

- “All” means all input tasks and queries in the named, immutable selections chosen
  in PR 3. Start with named 2025 editions for which we inspected source material;
  adding another edition is a new lockfile and coverage comparison. Preserve all
  selected tracks; do not silently drop difficult theories, large files or timeouts.
- This is 97 concrete PRs for known work. PR 6 determines the exhaustive feature
  inventory. Any additional encountered feature (for example sequences, sets/bags,
  finite fields, cardinality, algebraic-value syntax or a solver extension) requires
  its own narrowly scoped PR with named operators and semantic checks before the
  Stage 1 release gate. There is deliberately no “implement everything else” PR.
- Each entry below is one reviewable change with a merge condition. A theory PR
  includes its operator/signature table, semantic definitions/mappings, focused
  edge-case regressions, and a small representative input/output fixture. It does
  not simultaneously add frontend integration or benchmark reporting.
- Partial implementation is allowed while progressing, but must report unsupported
  constructs accurately. Parsed, translated, elaborated, Flex-compatible, proved,
  refuted and unresolved are different states. No unknown operator is silently
  replaced by an uninterpreted one merely to make a file typecheck.
- Canonical statements and runtime definitions contain no `sorry` and no axioms
  asserting query validity. The separate generated theorem templates may contain
  `sorry`, as requested. Theory-model laws are explicit assumptions/interpretation
  fields with the correct outer quantification, not a way to assume a benchmark.
- Result metadata does not determine formula meaning. Ordinary refutation goals
  and CHC existential model-existence goals have explicit recorded task kinds.
- Shared architecture: source/dialect reader → scoped cvc5 parser driver → typed
  snapshots → ordinary VC or CHC builder → Lean context/reconstruction layer →
  deterministic source/project emitter. The cvc5 driver never solves. Flex is an
  independently pinned consumer of generated source in Stage 3.
- Keep parser/reconstruction dependency adapters small and pinned. Reuse audited
  lean-smt term mappings; add missing semantics rather than importing all of its
  solver workflow. Full corpus scanning may reveal parser limitations requiring
  their own precise lowering/binding PRs as well as theory PRs.
- The order is suitable for a single main implementation stream. Independent theory
  branches can proceed after the shared frontend/emitter. Frontend saved-dump
  adapters can proceed independently once their common CLI contract is stable.

## Checkpoints

- PR 28: complete minimal ordinary-SMT and CHC paths exist.
- PR 42: the original 12 files / 321 checks, including 4 CHC problems / 28 clauses,
  are a permanent regression anchor. This is an early Stage 1 checkpoint, not the
  Stage 1 completion criterion.
- PR 69: Stage 1 release gate over the complete pinned selections.
- PR 81: frontend tooling release.
- PR 97: recurring Flex benchmark anchor and progress dashboard.

The benchmark source mechanisms are documented by
[SMT-COMP 2025](https://smt-comp.github.io/2025/),
[SMT-LIB's release index](https://smt-lib.org/benchmarks.shtml), and
[CHC-COMP25's task/metadata documentation](https://github.com/chc-comp/chc-comp25-benchmarks).
The inspected CHC-COMP25 revision is
`ddd279cab0717db6effe69baad451a8eb04ffd86`; use its published task selections and
metadata rather than guessing filenames.

## Stage 1: competition translation

### Translation foundation

- [x] **1. Specify the translation contract.** Add [docs/SEMANTICS.md](SEMANTICS.md): ordinary SMT refutation versus CHC model existence; record requested goal separately from solver metadata; permit sorry only in proof templates.

   **Merge when:** A sat, unsat, and unknown version of one input produce the same underlying problem.

   **Implementation:** [SEMANTICS.md](SEMANTICS.md) defines this invariant and provides ordinary-SMT and CHC expected-output examples. Executable translator regressions follow with the implementation tasks.

- [ ] **2. Version the result manifest.** Define JSON fields for input/query IDs, source hashes, goal kind, required features, generated files, and separate translation/elaboration/proof outcomes.

   **Merge when:** Schema fixtures reject missing provenance and never equate typechecked with proved.

- [ ] **3. Lock the benchmark selections.** Add corpus.lock.json for complete named SMT-COMP and CHC-COMP editions; resolve CHC .set → .yml → input_files; record revision, track, and selection membership.

   **Merge when:** Every selected task resolves to an input; excluded/duplicate tasks are recorded rather than silently lost.

- [ ] **4. Fetch and verify the locked corpora.** Add a resumable corpus fetch command with archive/input hashes and a local cache; keep bulk data outside git.

   **Merge when:** A clean fetch reproduces the locked input list; a corrupted cached file is detected.

- [ ] **5. Read SMT-LIB commands with source spans.** Implement a source reader for parentheses, comments, quoted identifiers, strings, and escapes; retain original command bytes.

   **Merge when:** Fixtures containing parentheses inside strings and quoted names split into the correct commands and spans.

- [ ] **6. Inventory the complete corpus.** Scan locked inputs for commands, sorts, indexed operators, dialect extensions, and sizes; write feature-to-file and per-track reports.

   **Merge when:** Every locked input is scanned or gets an explicit scan error; the report identifies features not covered by this backlog.

- [ ] **7. Pin and compile the parser dependencies.** Build the selected lean-cvc5 and lean-smt pins; test current Lean 4.33.1 compatibility and explicitly align the translator pin if required.

   **Merge when:** A clean build loads the native parser and reconstruction APIs; the chosen versions are committed.

- [ ] **8. Implement a parser driver that never solves.** Invoke supported declaration/assertion commands through lean-cvc5, intercept check-sat, and return assertions.

   **Merge when:** A tiny HORN input returns typed assertions; an instrumented driver makes zero checkSat calls.

- [ ] **9. Track binding identity and source declarations.** Add a ledger for declarations, definitions, datatypes, original spellings, and unique IDs; alpha-rename user symbols that collide with cvc5 builtins.

   **Merge when:** The current set.card declaration parses after binding-aware renaming; unrelated builtin symbols retain their meaning.

- [ ] **10. Introduce the typed query representation.** Add sort, binder, term, declaration, and QuerySnapshot types; preserve binding IDs and source references through cvc5 conversion.

   **Merge when:** A typed IR dump distinguishes shadowed variables, records term sorts, and rejects dangling symbol references.

- [ ] **11. Implement push/pop snapshots.** Scope assertions and declarations according to the selected declaration policy; freeze the environment at every query.

   **Merge when:** Sibling declarations and popped assertions cannot leak into another query's snapshot.

- [ ] **12. Preserve define-fun and sort aliases.** Capture definition bodies in their declaration environment and expand supported definitions/aliases without losing dependencies.

   **Merge when:** A definition referencing a subsequently shadowed name still refers to its original binding.

- [ ] **13. Implement check-sat-assuming.** Add temporary Boolean assumptions to exactly one query snapshot, validating the allowed syntax against the input's SMT-LIB version.

   **Merge when:** The assumed query contains the extra hypotheses; the following plain check does not.

- [ ] **14. Implement resets and semantic options.** Handle reset, reset-assertions, and global-declarations; classify other options and non-query commands explicitly.

   **Merge when:** Fixtures reproduce assertion/declaration lifetimes; unimplemented semantic commands fail visibly.

- [ ] **15. Implement simultaneous let bindings.** Expand let using the pre-binding environment, with capture-safe substitution and shared term nodes.

   **Merge when:** A let whose right-hand sides reuse outer names has the SMT simultaneous-binding meaning.

- [ ] **16. Translate universal and existential binders.** Preserve sort annotations, shadowing, and body-only variables; give bound terms stable IDs.

   **Merge when:** Nested forall/exists fixtures preserve their binder scopes and elaborate.

- [ ] **17. Preserve annotations and assertion names.** Process annotated terms; retain :named and source metadata, and classify solver-only patterns separately.

   **Merge when:** Named assertions map to generated hypotheses; removing a pattern does not alter the asserted formula.

- [ ] **18. Build the Lean symbol/context bridge.** Create typed Lean variables for supported sorts/functions, populate userNames, and isolate reconstruction caches per snapshot.

   **Merge when:** Uninterpreted Int/Bool function applications reconstruct without unresolved or stale free variables.

- [ ] **19. Implement Boolean terms and equality.** Support Boolean constants, connectives, ite, equality, n-ary distinct and correct arities; use SMT Bool → Lean Prop.

   **Merge when:** Boolean arguments/results and proposition equality elaborate; finite truth-table checks match the intended operators.

- [ ] **20. Implement integer arithmetic and comparisons.** Handle exact large/negative literals, n-ary arithmetic, multiplication, abs, unary minus, and chained comparisons.

   **Merge when:** Reviewed arithmetic fixtures preserve associativity and elaborate with no machine-integer truncation.

- [ ] **21. Build ordinary SMT obligations.** Emit canonical assertion predicates and explicit universally quantified refutation goals; recover a final negated conclusion when equivalent.

   **Merge when:** The matrix-indexing fixture produces its intended bound obligation with every required hypothesis.

- [ ] **22. Emit deterministic Lean modules.** Add stable namespaces, escaped readable names, explicit types, dependency ordering, and source comments.

   **Merge when:** Two generations are byte-identical; colliding names produce distinct declarations.

- [ ] **23. Emit separate sorry proof templates.** Create theorem stubs referring to generated obligations; keep generated definitions/runtime free of sorry.

   **Merge when:** Proof holes occur only in designated theorem files; regenerating the same input leaves edited proof files intact.

- [ ] **24. Package a standalone Lean output project.** Write the toolchain, Lake configuration, generated imports, and one canonical runtime/prelude copy.

   **Merge when:** The output builds from a clean directory without the translator repository on its import path.

- [ ] **25. Run Lean and classify its diagnostics.** Add an elaboration runner with exit status, structured diagnostics, limits, and admitted-proof reporting.

   **Merge when:** A malformed statement fails; a valid statement with a sorry theorem is reported as elaborated and unproved.

- [ ] **26. Recognize and validate Horn clauses.** Introduce relation declarations and clause IR; identify relation-free theory guards, relation premises, and relation/False heads.

   **Merge when:** Accept facts and multi-premise rules; reject an explicitly negated body relation or disjunctive relation heads with a source location.

- [ ] **27. Normalize CHC predicate arguments.** Introduce fresh typed universal variables and equality guards for compound/repeated arguments; preserve clause origins.

   **Merge when:** The Flux head arguments normalize without changing the clause meaning or dropping any false-head clause.

- [ ] **28. Emit canonical CHC model-existence propositions.** Close all declared relations with leading existentials and conjoin universally quantified clauses; include nullary relations.

   **Merge when:** Linear/nonlinear and nullary examples elaborate; changing recorded status never negates or otherwise rewrites Problem.

### Theory support and the current-corpus checkpoint

- [ ] **29. Implement exact integer div/mod.** Use Euclidean division for nonzero divisors and explicit shared interpretation choices for zero cases.

   **Merge when:** Negative-divisor and repeated-zero-application regressions pass; Lean's fixed zero case is not silently substituted.

- [ ] **30. Implement BV arithmetic and comparisons.** Map modular arithmetic, bitwise operations, and signed/unsigned comparisons with explicit widths.

   **Merge when:** Exhaustive tiny-width cases and 32/64-bit boundaries agree with the chosen SMT semantics.

- [ ] **31. Implement BV extraction and width changes.** Add concat, extract, zero/sign extension, and repeat.

   **Merge when:** Boundary slices have exact widths; invalid indices fail; signed extension preserves the sign bit.

- [ ] **32. Implement BV shifts and rotations.** Add logical/arithmetic shifts and indexed rotations.

   **Merge when:** Zero, width-sized, and oversized amounts have the specified behavior.

- [ ] **33. Implement BV division and remainder.** Add unsigned/signed division, remainder, and signed modulo.

   **Merge when:** Zero divisors and minimum-signed-value divided by minus one match SMT semantics.

- [ ] **34. Implement BV/integer conversions.** Add the conversion spellings used in the corpus and encountered overflow predicates, with explicit signedness.

   **Merge when:** Negative/oversized integers wrap correctly; signed and unsigned conversion regressions distinguish their meanings.

- [ ] **35. Model extensional array carriers.** Introduce explicit array interpretations with select/store and read-over-write/extensionality laws; retain a justified native profile where applicable.

   **Merge when:** Array equality and updates have reviewed semantics without requiring every array carrier to be the full function space.

- [ ] **36. Close quantified-array interpretation parameters.** Quantify background array models in the correct direction for satisfiability/refutation, including nested array sorts and CHC relation domains.

   **Merge when:** A distinguishing quantified-array regression prevents accidental strengthening to full function arrays.

- [ ] **37. Implement constant arrays and Z3 array map.** Add typed dialect lowering and Lean semantics for constant arrays and the indexed map forms used by fixtures.

   **Merge when:** lh_sets_neg translates; parser surrogates reconstruct as real array operations, never unconstrained functions.

- [ ] **38. Generate monomorphic and mutually recursive datatypes.** Emit grouped inductives with constructors, nonemptiness handling, and dependency order.

   **Merge when:** Mutually recursive fixtures elaborate and preserve constructor disjointness/injectivity.

- [ ] **39. Generate parametric and nested datatypes.** Handle sort parameters, multiple instantiations, nested types, and constructor ascriptions.

   **Merge when:** Vec Int and nested PolySet.Lst fixtures elaborate with distinct correct type arguments.

- [ ] **40. Implement datatype selector interpretations.** Emit constructor equations and input-dependent arbitrary results for wrong constructors, with correct model quantification.

   **Merge when:** Repeated selector applications remain congruent and wrong-constructor values are not fixed to a global default.

- [ ] **41. Implement datatype testers and match.** Add qualified/unqualified testers, pattern branches, and catch-all binding.

   **Merge when:** Each constructor selects the right tester/branch; pattern variables cannot capture outer variables.

- [ ] **42. Lock the current 321-check regression suite.** Generate the entire existing tests directory and commit reviewed representative output plus its manifest.

   **Merge when:** All 12 files and 321 checks elaborate; the four CHC problems preserve their 28 source clauses. Flex solving is not required.

- [ ] **43. Support arbitrary nonempty uninterpreted sorts.** Emit interpretation parameters and nonemptiness requirements rather than one chosen opaque carrier.

   **Merge when:** Uninterpreted-sort validity ranges over all admissible carriers; model-existence quantifies interpretations existentially.

- [ ] **44. Translate recursive function definitions.** Implement the inventoried define-fun-rec/define-funs-rec forms using active scoped defining equations over function interpretations. Retain the equations even when assertions do not reference the function. For refutation, universally quantify interpretations and use equations as premises; for model existence, existentially quantify interpretations and conjoin equations.

   **Merge when:** Mutual/self-recursive fixtures preserve equations, including an unused recursive definition with no total solution. No reachability pruning deletes its constraint, and no fabricated Lean termination argument or new query-validity axiom appears.

- [ ] **45. Add an exact Real output profile.** Use Mathlib Real, exact numeric literals, arithmetic and ordering, and explicit division-at-zero interpretations.

   **Merge when:** Nonlinear Real fixtures elaborate; no decimal is rounded through a host float and Real is never replaced by Rat.

- [ ] **46. Implement mixed Int/Real operations.** Add to_real, floor-based to_int, and is_int.

   **Merge when:** Negative fractional values demonstrate floor behavior and exact coercions.

- [ ] **47. Introduce the SMT string carrier.** Represent the SMT codepoint domain, literals, concatenation, and character-count length.

   **Merge when:** Valid SMT codepoints missing from Lean Char remain representable; string length counts characters.

- [ ] **48. Implement string indexing and slicing.** Add at/substr with exact exceptional and clipping behavior.

   **Merge when:** Negative indices, zero/negative lengths, and out-of-range positions match the specification.

- [ ] **49. Implement string search and ordering.** Add prefix/suffix/contains, index-of, and lexicographic comparison operators present in the corpus.

   **Merge when:** Empty patterns and start-position boundary cases pass semantic regressions.

- [ ] **50. Implement literal string replacement.** Add first-occurrence and replace-all operations required by the inventory.

   **Merge when:** Overlapping and empty patterns use SMT behavior rather than host-library defaults.

- [ ] **51. Implement string numeric/codepoint conversions.** Add integer/string and codepoint/string conversions.

   **Merge when:** Invalid inputs, negative integers, leading zeros, and singleton requirements return the specified results.

- [ ] **52. Introduce regular-language semantics.** Represent RegLan values as languages and add membership, constants, Boolean language operators, concatenation, and star.

   **Merge when:** Quantified/uninterpreted RegLan values are not restricted to a syntax tree of constructible regexes.

- [ ] **53. Implement regex ranges and repetition.** Add ranges and indexed bounded/unbounded repetition forms from the corpus.

   **Merge when:** Empty-word/language and zero/lower/upper-bound cases have the specified membership semantics.

- [ ] **54. Implement regex-based replacement.** Add inventoried regex replacement operations with exact matching priority.

   **Merge when:** Leftmost/shortest and zero-length-match cases distinguish the implementation from literal replacement.

- [ ] **55. Introduce SMT floating-point values.** Define format-indexed values, literals, signed zeros, infinities, NaN, classification, comparisons, abs/neg, and min/max interpretation choices.

   **Merge when:** SMT equality and fp.eq are distinct where required; NaN is not treated as arbitrary unequal raw bit patterns.

- [ ] **56. Implement exact FP rounding.** Add all rounding modes over an exact arithmetic representation.

   **Merge when:** Halfway values, subnormals, underflow/overflow, and signed-zero boundaries pass reference checks.

- [ ] **57. Implement FP addition and subtraction.** Add the two arithmetic operators using the shared rounding implementation.

   **Merge when:** Tiny-format exhaustive tests cover cancellation and all exceptional value combinations.

- [ ] **58. Implement FP multiplication and division.** Add multiplication/division with exact special-value and rounding rules.

   **Merge when:** Tiny-format checks cover zero/infinity/NaN combinations and overflow/underflow.

- [ ] **59. Implement fused multiply-add.** Add fma with one final rounding.

   **Merge when:** A regression differs from separately rounded multiplication followed by addition.

- [ ] **60. Implement FP square root.** Add exact rounding of square roots and special-value handling.

   **Merge when:** Exact/inexact roots, negative inputs, signed zeros and rounding boundaries pass reference checks.

- [ ] **61. Implement FP remainder and integral rounding.** Add fp.rem and roundToIntegral.

   **Merge when:** Quotient ties, signed remainder zero, and each rounding mode match SMT semantics.

- [ ] **62. Implement FP format/bit conversions.** Add widening/narrowing and IEEE bit reinterpretation/encoding with specified NaN choices.

   **Merge when:** Specified round trips hold; ambiguous NaN encodings remain explicit interpretation choices.

- [ ] **63. Implement FP numeric conversions.** Add Real/BV↔FP numeric conversions and exceptional/out-of-range interpretations.

   **Merge when:** Signedness, rounding, NaN/infinity and out-of-range cases are covered without silently choosing unspecified values.

### Competition-scale execution and Stage 1 gate

- [ ] **64. Preserve shared terms during emission.** Emit repeated subterms once using local bindings without changing scope.

   **Merge when:** A synthetic DAG grows with distinct nodes rather than exponentially with repeated occurrences.

- [ ] **65. Split large sessions into stable modules.** Shard generated queries while keeping stable query IDs, imports, and source mappings.

   **Merge when:** Changing one shard does not renumber unrelated queries; every original check is still represented.

- [ ] **66. Build the isolated benchmark worker.** Run translation and Lean elaboration as separate bounded processes and emit one result per task/query.

   **Merge when:** Crashes and timeouts are classified; one failing task cannot abort or hide the remaining corpus.

- [ ] **67. Add resumable content-addressed benchmark runs.** Cache by input, translator, runtime, output profile, dependency, and toolchain hashes.

   **Merge when:** An unchanged run resumes; changing any semantic input invalidates the affected cache.

- [ ] **68. Publish per-track translation coverage.** Generate machine-readable and readable reports including unsupported inputs, partial sessions, and resource failures.

   **Merge when:** Totals reconcile with the locked selection; only fully translated/elaborated tasks count as successful.

- [ ] **69. Gate the complete pinned competition selections.** Add a release check joining inventory coverage, semantic regressions, query counts, and the full benchmark results.

   **Merge when:** Stage 1 passes only when every selected input and query translates faithfully and elaborates; unimplemented inventoried features block this PR's release gate.

## Stage 2: frontend tooling

### Frontend tooling

- [ ] **70. Stabilize the public CLI.** Expose inspect, translate, select-query and check commands, JSON output, documented exit codes, and stderr diagnostics.

   **Merge when:** An external script distinguishes unsupported input, generation failure and Lean failure without parsing prose.

- [ ] **71. Export an individual incremental query.** Package one selected snapshot with all visible declarations, definitions and provenance.

   **Merge when:** Selected-query output has the same typed problem as the corresponding whole-session snapshot.

- [ ] **72. Version the frontend metadata sidecar.** Accept original program locations, assertion names, frontend version and intended task without changing SMT semantics.

   **Merge when:** A source location round-trips from sidecar to generated theorem and diagnostics.

- [ ] **73. Import LiquidHaskell saved sessions.** Add a thin saved-dump adapter with available source/probe metadata.

   **Merge when:** All existing LiquidHaskell files import without manual edits and preserve check order.

- [ ] **74. Import Flux saved sessions and CHCs.** Distinguish Flux validity transcripts from its pre-solver CHC exports.

   **Merge when:** Existing Flux fixtures retain their task kind, source identity and recorded outcomes.

- [ ] **75. Import one Boogie/Dafny query log.** Pin one frontend version and capture its real exported format; add a saved-log adapter and small end-to-end fixture.

   **Merge when:** One documented frontend invocation produces an editable Lean obligation without hand-editing SMT.

- [ ] **76. Expose a reusable library entrypoint.** Separate file IO/CLI from translation and export stable request/result types over the versioned artifacts.

   **Merge when:** A small independent Lean client translates a supplied session and receives structured results.

- [ ] **77. Record a transparent solver session.** Add an opt-in subprocess wrapper that forwards supported SMT protocol commands/responses and records them.

   **Merge when:** Protocol fixtures preserve stdout, ordering and exit behavior; unsupported transports are explicit.

- [ ] **78. Export on unknown or timeout.** Connect the recorder to Lean export on configured failure triggers.

   **Merge when:** A deterministic fake solver exercises both paths; exporting never fabricates sat/unsat for the original frontend.

- [ ] **79. Preserve and reopen interactive proof work.** Add a project-open command, stable proof filenames and changed-obligation detection.

   **Merge when:** Regeneration preserves user edits and flags proofs whose underlying obligation changed.

- [ ] **80. Package distributable frontend tooling.** Publish reproducible binary/package build scripts and verify native dependency discovery on the supported OS/architectures.

   **Merge when:** A clean supported machine can run the documented install/import/check path.

- [ ] **81. Ship two complete frontend walkthroughs.** Add LiquidHaskell and Flux demos showing capture, selection, export, checking and interactive continuation.

   **Merge when:** Each demo runs from pinned fixtures and includes an unresolved or negative case with visible provenance.

## Stage 3: Flex and the recurring anchor

### Flex integration and recurring benchmark anchor

- [ ] **82. Create a pinned Flex consumer project.** Add a separate Lake workspace pinned to public Flex and its matching Lean version.

   **Merge when:** A clean build imports Flex and generated Lean source without reusing incompatible olean files.

- [ ] **83. Add the Flex export profile.** Emit the canonical existential CHC problem and portable runtime declarations into the Flex workspace.

   **Merge when:** Generated meaning and relation signatures match Stage 1; no lean-smt/cvc5 implementation imports leak into the target.

- [ ] **84. Check the Flex predicate contract.** Validate leading relation binders, full applications, guard/head forms and result types before invoking Flex.

   **Merge when:** An existential data witness is never accidentally registered as a predicate unknown.

- [ ] **85. Handle background interpretation parameters explicitly.** Keep theory models and underspecified nonpredicate functions distinct from relation unknowns; allow only justified witness/parameter adapters.

   **Merge when:** A benchmark needing extra model choices is handled explicitly or reported unsupported by Flex, never silently strengthened.

- [ ] **86. Implement a Flex shape-check command.** Use temporary goals with peelExistentialsAndIntro and exprFlat; compare normalized signatures and clauses, then discard meta state.

   **Merge when:** Well-formed true and false problems pass independently of any solver run; no incomplete theorem is installed.

- [ ] **87. Add structural Flex regression cases.** Cover nullary predicates, Prop-valued Bool arguments, repeated/compound arguments and clauses reduced to True.

   **Merge when:** Source-to-normalized clause accounting explains every simplification and preserves the intended predicates.

- [ ] **88. Add theory-specific Flex integration cases.** Run generated Int, BV, ADT and audited array cases through elaboration and shape checking.

   **Merge when:** The importer-generated fixtures pass representation checks; unsupported theory profiles remain explicit.

- [ ] **89. Enable Real-valued Flex input.** Add a separately pinned Real-capable consumer profile and the corresponding theory imports; retain exact Real semantics and compatible Flex/Mathlib toolchains.

   **Merge when:** A generated LRA CHC with mixed Prop/Real arguments elaborates and passes shape checking; no Rat substitution or incompatible olean import is used.

- [ ] **90. Run optional Flex proof attempts.** Generate isolated proof files invoking the pinned solver tactic with resource limits.

   **Merge when:** Only a complete theorem without transitive sorryAx is classified proved; proof dependencies are recorded, while residual goals, exceptions and timeouts remain unresolved.

- [ ] **91. Add qualifier-file support.** Load user-owned qualif declarations, record their hash and provide one sufficient cyclic-invariant example.

   **Merge when:** The qualifier file affects solver guidance only, never the canonical translated problem.

- [ ] **92. Add editable residual-goal workflows.** Provide witness-first and residual-goal proof templates using the pinned Flex tactics.

   **Merge when:** A user completes a small cyclic example interactively while the generated statement remains unchanged.

- [ ] **93. Add separately checked CHC refutations.** Allow explicit proofs of not Problem and classify them separately from positive Flex proofs.

   **Merge when:** A known unsafe example is refuted by a completed proof; failed invariant synthesis is never called unsat.

- [ ] **94. Record full Flex run evidence.** Extend results with problem hash, Flex/Lean/dependency revisions, qualifiers, tactics, resource settings and proof dependencies.

   **Merge when:** Every reported success is traceable to its exact configuration and checked artifact.

- [ ] **95. Compare two Flex revisions fairly.** Join results by stable task/problem identity and expose all differing controls.

   **Merge when:** Reports list solved/lost/remaining tasks and runtime changes; qualifier/corpus/config changes cannot masquerade as a pure Flex revision comparison.

- [ ] **96. Schedule the stable Flex anchor suite.** Add per-PR smoke checks and a scheduled full pinned-corpus run with retained results/artifacts.

   **Merge when:** An introduced known regression is detected; interrupted full runs resume and preserve historical comparisons.

- [ ] **97. Publish the Flex progress dashboard.** Render per-track translation, compatibility, proved/refuted/unresolved counts and comparable runtime histories.

   **Merge when:** Every displayed total reconciles with stored run evidence, and individual changed benchmarks link to their generated goals.

## Stage completion criteria

Stage 1 is complete only when every locked task and query has faithful supported
translation and Lean elaboration with the prescribed theorem holes, all semantic
regressions pass, and no unsupported input or resource failure remains hidden in
the denominator. If corpus inventory exposes more work, add specific PRs before
this gate; do not redefine “all” as the subset already handled.

Stage 2 is complete when the documented saved-query and live-fallback workflows
work from the supported frontends without manual SMT edits, retain source/query
identity, preserve proof edits, and never misreport export as a solver answer.

Stage 3 is complete when every selected CHC receives an explicit adapter/run result,
the known compatible anchor cases run reproducibly, and successive Flex revisions
can be compared with all controls recorded. Broad proof success is the improvement
metric, not a prerequisite for establishing the anchor. Unsupported Flex profiles
remain visible and become focused integration/solver PRs; they are not translation
successes counted as proofs.
