# Ordered PR backlog: working translation, frontend tooling, Flex

Updated 2026-09-28. This is the current execution plan and supersedes the earlier
ordering in ROADMAP.md and FLEX-ARCHITECTURE.md. PRs are ordered to get runnable
translation working first, extend it on real inputs, and add tooling when needed.

Each checkbox is one numbered PR-sized task. Checked means its implementation is
present in the working tree; it does not mean committed, merged, or user-reviewed.
Implement one PR at a time and stop for user review. Do not commit unless asked.

## The user's stages

1. Translate every benchmark/query in pinned SMT-COMP and CHC-COMP selections into
   faithful Lean statements with optional `sorry` theorem templates.
2. Supply tooling that lets existing frontends export unresolved queries into Lean.
3. Run translated CHCs through Flex and maintain a reproducible progress anchor.

## Implementation order

**Next: task 3.6, finish the repeatable Boolean demo.** Tasks 2.1–2.3
and 3.1–3.5 are implemented and verified on Lean 4.33.1. PR 2 is complete. PRs 2 and 3 have
commit-sized checklists below. Implement one subtask, run its checks, and stop for
user review before starting the next. These are intended commit boundaries;
leave changes uncommitted unless explicitly asked to commit. PR 1's semantic
contract is already present. The manifest work is deferred to PR 64.

The first runnable command arrives in PR 3, integer input in PR 4, and an unedited
existing CHC example in PR 8. These use the repository toolchain, ordinary generated
Lean files with statements followed by proof templates, and direct Lean checks. Implement only the
small parser/context/emitter pieces needed by each supported fragment, then extend
the same path. Later architecture PRs consolidate these working pieces.

Next, support real sessions and the theories needed by the original tests, then
ship their standalone demo at PR 37. Lock/download/inventory the competition corpus
after that checkpoint and extend translation against its missing features. Result
schemas, process isolation, caching, and coverage reporting enter when automating
those real runs. Public frontend APIs and Flex integration keep their own stages.

Every functionality PR must exercise the CLI or generated Lean output where
applicable and retain the earlier demos as regressions. Small fixtures and direct
Lean checks accompany the functionality they verify. Schemas, generic reporting,
and broad framework design must not become prerequisites for the first translation.

## Scope and merge rules

- “All” means all input tasks and queries in the named, immutable selections chosen
  in PR 38. Start with named 2025 editions for which we inspected source material;
  adding another edition is a new lockfile and coverage comparison. Preserve all
  selected tracks; do not silently drop difficult theories, large files or timeouts.
- This is 97 concrete PRs for known work. PR 40 determines the competition feature
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
  refuted and unresolved are different states, even before JSON reporting exists.
  No unknown operator is silently replaced with an uninterpreted one merely to
  make a file typecheck. Never silently skip an unsupported query in a session.
- Canonical statements and runtime definitions contain no `sorry` and no axioms
  asserting query validity. Separate generated theorem templates may contain
  `sorry`. Theory-model laws are explicit assumptions/interpretation fields with
  the correct outer quantification, not a way to assume a benchmark.
- Result metadata does not determine formula meaning. Ordinary refutation goals
  and CHC existential model-existence goals have explicit requested task kinds in
  the translator; their serialized contract is defined later.
- Shared target architecture: source/dialect reader → scoped cvc5 parser driver →
  typed snapshots → ordinary VC or CHC builder → Lean context/reconstruction layer
  → source/project emitter. Build its smallest usable path first and extend it
  without solving in cvc5. Flex is an independently pinned consumer in Stage 3.
- Keep dependency adapters small and pinned. Reuse audited lean-smt term mappings;
  add missing semantics rather than importing all of its solver workflow. Corpus
  scanning may reveal parser limitations requiring precise lowering/binding PRs
  as well as theory PRs.
- The sequence is one implementation stream. Later CLI/library/reporting contracts
  should follow the working translator's concrete inputs and outputs.

## Checkpoints

- PR 3: one ordinary Boolean input becomes a closed Lean statement and editable
  theorem in one `Query.lean`, which elaborates with the repository toolchain.
- PR 4: the same command translates integer queries.
- PR 8: the unedited lh_sum_rec CHC becomes an existential Lean problem; all three
  clauses are preserved and the generated files elaborate.
- PR 37: the original 12 files / 321 checks, including four CHC problems / 28 clauses,
  form a runnable standalone demo and permanent regression anchor. This is an early
  Stage 1 checkpoint, not the Stage 1 completion criterion.
- PRs 38–40: lock, fetch, and inventory the larger competition inputs.
- PRs 64–68: add result manifests and benchmark automation to the working translator.
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

## Stage 1: working translations, then competition coverage

### First runnable ordinary-SMT and CHC paths

- [x] **1. Specify the translation contract.** Add [docs/SEMANTICS.md](SEMANTICS.md): ordinary SMT refutation versus CHC model existence; record requested goal separately from solver metadata; permit sorry only in proof templates.

   **Merge when:** A sat, unsat, and unknown version of one input produce the same underlying problem.

   **Implementation:** [SEMANTICS.md](SEMANTICS.md) defines this invariant and provides ordinary-SMT and CHC expected-output examples. Executable translator regressions follow with the implementation tasks.

- [x] **2. Build and exercise the parser/reconstruction dependencies.** Pin the inspected lean-cvc5 and lean-smt revisions, check compatibility with Lean 4.33.1, and align the translator toolchain if needed. Add one executable smoke case that parses a closed Boolean assertion through the native API and reconstructs a Lean proposition without solving. Keep the adapter limited to the calls needed by the next PR.

   **Merge when:** A clean build runs the smoke case and Lean checks the reconstructed proposition; the exact dependency/toolchain pins are recorded. No solver check is executed.

   Each subtask below is one proposed commit. Add checks with the behavior they exercise; all earlier checks must keep passing. Module paths are proposed implementation locations, not existing files.

   - [x] **2.1. Pin and build the backend dependencies.** Update `lakefile.toml` and Lake's dependency lockfile for lean-smt `5bdc51674065a074ece67b04e10024e9f426ec1f`; verify resolved lean-cvc5 is `7e3365990661b697ccb30e92d6912f4cc6589322`. Add `Smt2Lean/Backend.lean` with the imports needed for cvc5 and the registered `Smt.Reconstruct.Prop`/`Builtin` reconstructors. Import it into the translator build so the dependency path is actually compiled. Test the current toolchain first; if incompatible, align the root and example project toolchains with upstream Lean 4.33.0 in this same change. Record the working setup in README.

      **Check:** `lake build` compiles the backend imports and links the executable; the example project still builds under its recorded toolchain. The lockfile contains immutable resolved revisions. This establishes compilation/linking; native parser execution is checked in 2.2.

      **Verified:** Root build passed (97 jobs), the linked CLI launched successfully, and the example build passed (4 jobs) on macOS arm64 / Lean 4.33.1. Both direct pins and all 12 resolved Git revisions were checked. The current toolchain works when building these backend modules from source; README documents skipping Mathlib's optional 4.33.0 cache hook during dependency updates.

   - [x] **2.2. Parse a closed assertion without invoking a query.** In `Smt2Lean/Backend.lean`, create the cvc5 solver/parser and add a small command-dispatch loop for a fixed smoke input containing `(assert (and true (not false)))` and `(check-sat)`. Invoke only the supported non-query commands, propagate native errors, intercept the check, and retrieve `getAssertions`. Register a `testReconstruction` executable rooted at `tests/backend/Reconstruction.lean`. Keep cvc5 values within their valid native environment lifetime.

      **Check:** `lake exe testReconstruction` obtains exactly one Bool-sorted assertion. A dispatch trace records the actual invoked command names and excludes check-sat; the adapter has no calls to `checkSat`, `checkSatAssuming`, or lean-smt's solving/query runners. Malformed input fails visibly. Use this small dispatcher as the basis of PR 3.

      **Verified:** `lake exe testReconstruction` checks one assertion with invocation trace `#[set-logic, assert]` and reconstructs the expected `True ∧ ¬False`. Parser rejection checks now live in `tests/backend/Parser.lean`, run with `lake exe testParser`: malformed input, invalid logic, check-sat-assuming, missing/repeated checks, and trailing commands are rejected. Unexpected command-response text is propagated as an error. Native terms are inspected in the driver's callback.

   - [x] **2.3. Reconstruct and check the smoke proposition.** Extend the same executable to run `Smt.Reconstruct.reconstructSort` and `reconstructTerm` in a Lean environment containing the registered reconstructors, using a fresh reconstruction context/state. Check the returned expression as the body of a `Prop` definition. This exercises the term path without proof reconstruction.

      **Check:** `lake exe testReconstruction` parses the input, reconstructs `True ∧ ¬False` (up to definitional equality), and installs a checked definition with no unresolved variables, metavariables, or admitted dependencies. It exits nonzero on any failed check. Document this one smoke command; PR 2 is complete only after it runs from a clean dependency build.

      **Verified:** The callback reconstructs both the sort and term, checks the expected proposition, and synchronously installs `Reconstruction.assertion : Prop := True ∧ ¬False` through Lean's kernel. The definition has no axiom dependencies or unresolved variables/goals. The smoke test and all parser rejection checks pass on Lean 4.33.1, including after a clean build of all required Lean modules and the C++ binding (98 jobs for both executables), reusing only the pinned native cvc5 1.3.2 SDK. Root and example builds also pass. The executable enables interpreter support and loads the registered reconstructors into its Lean environment. No solver query, proof reconstruction, or source-file emission is performed.

- [ ] **3. Translate one Boolean query end to end.** Replace the CLI stub with `smt2lean <input.smt2> --out <fresh-directory>`. Accept one flat query with Boolean constants/nullary declarations, assertions, true/false, not/and/or/implication/equality, and check-sat. Handle set-logic, status metadata, and exit explicitly. Use cvc5 for parsing/sorts and lean-smt reconstruction through a minimal local-variable map; intercept the check without solving. Emit one `Query.lean` with the closed refutation proposition first, followed by a proof template containing `sorry`. Reject unsupported commands/terms or multiple checks before emitting a successful result.

   **Merge when:** An ordinary Boolean fixture translates from disk and the generated file elaborates using the repository toolchain. Changing sat/unsat/unknown metadata leaves the proposition unchanged. Unsupported input fails visibly, canonical statements contain no admissions, and an instrumented driver makes zero checkSat calls. No manifest, general IR framework, or standalone project generator is required.

   Implement these six commits after PR 2, reviewing each before continuing:

   - [x] **3.1. Read and validate one flat Boolean query.** Extend the working backend to accept supplied SMT-LIB text, Boolean `declare-const`/nullary `declare-fun`, assertions, and exactly one check. Allow absent logic or the initial QF_UF/ALL profiles; handle nonsemantic set-info metadata and exit explicitly. Retain declaration identity and original names in a small internal query record. Validate Bool-only sorts and the supported Boolean term kinds before reconstruction. Read the whole input; reject missing/repeated checks, state changes after the check, unsupported commands/operators/sorts, and HORN input. Preserve parser diagnostics with the input name and command ordinal; exact source spans follow in PR 9.

      **Check:** Focused fixtures under `tests/translation/bool/` accept both declaration spellings and an empty assertion set. Int/function/quantifier/ite/push-pop/HORN cases and an unsupported command after a valid check fail. No source query command reaches native invocation and no unsupported term is converted to an uninterpreted placeholder.

      **Verified:** `lake exe testParser` passes 8 accepted cases from three combined fixtures and 26 rejected cases kept inline in the test runner. Checks cover native declaration identity, quoted names, unused declarations, all supported connectives, metadata independence, full-input validation, and error locations. The callback receives one internal `BoolQuery` only after validation; rejected inputs never reach it. Native invocation is limited to logic, declaration, and assertion commands. The existing parser/reconstruction smoke, all three executable builds, and the example build pass. Variable reconstruction and closed refutations are verified in tasks 3.2–3.3 below; file generation and the CLI are verified in tasks 3.4–3.5.

   - [x] **3.2. Reconstruct Boolean variables and connectives.** Add `Smt2Lean/Translate.lean`. Create fresh Lean `Prop` parameters for the declared Boolean constants and populate lean-smt's `userNames` map explicitly. Reuse the registered term reconstructors for true/false, not/and/or/implication, and Boolean equality; preserve operand order and the parser's supported arities. Use fresh internal binder names so SMT names cannot accidentally resolve to existing Lean declarations. Keep reconstruction caches local to the translation.

      **Check:** Reconstructed assertions have type `Prop` and agree with handwritten equivalents, including multi-operand connectives and implication order. An SMT constant named `|True|` is a parameter, not Lean's `True`; undeclared/unmapped names fail. Translating two inputs in succession does not share variables.

      **Verified:** `lake exe testTranslation` checks the combined fixture against handwritten propositions. Fresh local `Prop` parameters populate Lean-SMT's `userNames`; native declaration identities are checked before reconstruction can fall back to Lean globals. The test covers both declaration forms, quoted names, unused parameters, all supported connectives, chained equality, and implication order. A reconstruction inside another reconstruction uses distinct variables; removing the declaration map fails. Each call starts with fresh caches. cvc5 lowers chained equality to binary equalities, matching the upstream reconstructor's arity.

   - [x] **3.3. Build the closed ordinary refutation.** In the same translation module, universally quantify the Boolean interpretation parameters and build `(A₁ ∧ … ∧ Aₙ) → False`; use `True` for an empty assertion set. Produce one closed `Refutation : Prop` definition and check it in Lean. Identify the task through the definition name; file comments follow in 3.4; solver-status metadata never selects the target.

      **Check:** Contradictory assertions `p` and `not p` produce the expected refutation, while a single `p` assertion and an empty assertion set retain their different, possibly false obligations. Compare with handwritten expected propositions. No free variables, unresolved metavariables, `sorry`, or query-validity axioms enter the statement; sat/unsat/unknown/absent metadata variants have the same target.

      **Verified:** `defineRefutation` universally quantifies every declaration, including unused ones, and installs a safe `Refutation : Prop` definition through the synchronous Lean kernel API. Closure and axiom-dependency checks reject unresolved variables or admissions. `lake exe testTranslation` passes eight handwritten comparisons: the combined fixture, contradiction under four metadata variants, a single assertion, an empty query, and an empty query with an unused declaration. This step checks in-memory definitions; file emission is verified in 3.4 below. The propositions are not proved.

   - [x] **3.4. Emit statements and proofs in one file.** Add `Smt2Lean/Emit.lean` to render `Query.lean` with a Statements section containing the closed definition, followed by a Proofs section declaring a theorem with `by sorry`. For this Boolean fragment the emitted code uses Lean core, without translator or cvc5 imports. Write only after parsing, validation, and reconstruction succeed; require a new output directory so existing proof work cannot be overwritten.

      **Check:** Generate a temporary `Query.lean` and compile it with Lean core. The re-elaborated statement agrees with the in-memory target and has no axiom dependencies; only the following proof template contains an admission. Invalid input produces no generated files; an existing destination is refused unchanged.

      **Verified:** `Smt2Lean/Emit.lean` renders the checked expression with Lean's printer, rejecting truncated output, and exclusively creates a fresh directory for `Query.lean`. `lake exe testTranslation` re-elaborates all eight statements using Lean core, compares them with the original expressions, checks for axiom dependencies, compiles each generated file with an isolated `LEAN_PATH`, and verifies that an attempted rewrite preserves edited proof work. The Statements section remains axiom-free; only the following Proofs section contains `sorry`.

   - [x] **3.5. Connect file translation to the CLI.** Replace `Main.lean`'s argument echo with `smt2lean <input.smt2> --out <fresh-directory>`, connecting file reading, the validated backend, reconstruction, and emission. Add `--help`; use exit 0 for generation, 2 for invalid arguments, and 1 for input/translation/output failures, with diagnostics on stderr. Report the generated path and that the theorem is unfinished; generation alone must not be reported as a proof or a completed external Lean check.

      **Check:** `lake exe smt2lean tests/translation/bool/contradiction.smt2 --out <new-path>` generates `Query.lean`. Missing files, bad arguments, unsupported input, and existing output directories return the documented failure status. This commit delivers the user-facing translation command.

      **Verified:** The CLI connects file reading, complete query validation, reconstruction, and emission. `--help` exits 0; invalid arguments exit 2; input, translation, and output failures exit 1 on stderr. Successful generation reports the path and an unfinished proof. `lake env python3 tests/cli.py` checks all three fixtures, missing files, invalid arguments, unsupported/malformed/repeated queries, existing directories/files/symlinks, and output failures. Invalid input creates no output directory; existing proof work remains unchanged.

   - [ ] **3.6. Make the Boolean demo repeatable.** Add `tests/translation/run-bool.sh` to exercise the actual CLI and check generated files in fresh temporary directories with the repository's Lean toolchain. Reuse the fixtures/checks introduced above; add a reviewed expected output and a README walkthrough showing generation, Lean checking, and opening the theorem for editing. Keep the harness limited to these Boolean cases.

      **Check:** The documented walkthrough and script pass for contradictory, satisfiable, empty-assertion, and metadata-variant inputs, and verify failure for unsupported/repeated-query input. Every generated statement elaborates independently of its unfinished theorem. The unchanged PR 2 smoke test also passes. This completes PR 3; integer translation begins in PR 4.

- [ ] **4. Translate integer queries through the working command.** Extend the Boolean path with Int declarations, exact large/negative literals, n-ary arithmetic, multiplication, abs, unary minus, and chained comparisons. Add a small standalone integer-bound example with its own supported declarations; the unedited frontend sessions follow once their preambles and scopes are supported.

   **Merge when:** The same CLI produces an editable, well-typed integer obligation. Reviewed arithmetic fixtures preserve associativity and exact values without machine-integer truncation; unsupported div/mod is still rejected explicitly.

- [ ] **5. Extend the Lean context bridge to Int/Bool functions.** Generalize the minimal declaration map from the first translator to typed function/relation parameters, populate userNames, and keep reconstruction contexts and caches local to each translation. Keep the generated definitions closed over every required interpretation.

   **Merge when:** Int-valued functions and Int/Bool-valued predicate arguments/results translate through the CLI without unresolved or stale free variables; separate input files cannot share accidental bindings.

- [ ] **6. Translate universal and existential binders.** Extend the working term translator with forall/exists, preserving sort annotations, shadowing, body-only variables, and bound-term identity. Initially cover Int and Bool using the existing context bridge.

   **Merge when:** Nested forall/exists fixtures translate through the CLI and elaborate with their original scopes, including Bool variables used as data.

- [ ] **7. Recognize and validate integer Horn clauses.** Add the relation declarations and minimal typed clause records needed for the CHC path. Recognize relation-free theory guards, relation premises, and relation/False heads in the already supported Int/Bool fragment. Validate all clauses before emitting a CHC goal; report errors by input/query/clause until exact source spans arrive.

   **Merge when:** Accept facts, multi-premise rules, nullary relations, and the clauses in lh_sum_rec; reject an explicitly negated body relation or disjunctive relation heads with the offending clause identified. No Flex integration is needed.

- [ ] **8. Translate the first existing CHC file end to end.** Connect the Horn validator to the existing CLI and emitter. For HORN input, close all declared relations with leading existentials and conjoin universally quantified clauses; include nullary relations. Generate the positive `Problem` proposition and a separate `sorry` theorem independently of recorded status. Preserve original predicate arguments at this point; normalization follows as its own PR.

   **Merge when:** The unedited tests/chc/lh_sum_rec.smt2 produces a Lean problem with its one relation and all three clauses, and both statement/proof-template files elaborate. Linear/nonlinear and nullary fixtures also elaborate; sat/unsat/unknown metadata never negates Problem. Document the runnable CHC demo in README.

### Extend the working path to real frontend sessions

- [ ] **9. Add precise source spans to the working translator.** Implement a source reader for parentheses, comments, quoted identifiers, strings, and escapes; retain original command bytes and attach locations to the existing parser driver, errors, and generated comments.

   **Merge when:** Fixtures containing parentheses inside strings and quoted names split into the correct commands/spans; a translation error identifies its original input location without changing earlier demo output meaning.

- [ ] **10. Track binding identity and source declarations.** Add a ledger for declarations, definitions, datatypes, original spellings, and unique IDs; alpha-rename user symbols that collide with cvc5 builtins.

   **Merge when:** The current set.card declaration parses after binding-aware renaming; unrelated builtin symbols retain their meaning.

- [ ] **11. Consolidate the working pipeline into typed query snapshots.** Extract the term, sort, binder, declaration, and QuerySnapshot structures actually used by the Boolean, integer, and CHC paths. Preserve binding IDs and source references through cvc5 conversion; keep the implementation private and only generalize what upcoming scope handling needs.

   **Merge when:** The existing demos still translate and elaborate; a typed IR dump distinguishes shadowed variables, records term sorts, and rejects dangling symbol references. No serialized IR or public library API is introduced.

- [ ] **12. Translate push/pop sessions query by query.** Extend the existing single-query path to multiple checks. Scope assertions and declarations according to the selected declaration policy, freeze the environment at each check, and emit one named obligation per snapshot.

   **Merge when:** A two-check session produces two elaborating obligations; sibling declarations and popped assertions cannot leak between snapshots, and an unsupported query cannot silently disappear.

- [ ] **13. Preserve define-fun and sort aliases.** Capture definition bodies in their declaration environment and expand supported definitions/aliases without losing dependencies. Account explicitly for unused nonrecursive frontend preambles: retain and sort-check them in the source ledger, and omit them from Lean only when dependency/semantic analysis establishes they do not constrain the query. Active unsupported terms still fail; recursive defining equations must never be discarded this way.

   **Merge when:** A definition referencing a subsequently shadowed name retains its original binding. Paired preamble-used/preamble-unused fixtures demonstrate the allowed omission; the shared String/array preamble cannot accidentally become an extra condition on an integer-only goal.

- [ ] **14. Implement simultaneous let bindings.** Expand let using the pre-binding environment, with capture-safe substitution and shared term nodes.

   **Merge when:** A let whose right-hand sides reuse outer names has the SMT simultaneous-binding meaning.

- [ ] **15. Implement check-sat-assuming.** Add temporary Boolean assumptions to exactly one query snapshot, validating the allowed syntax against the input's SMT-LIB version.

   **Merge when:** The assumed query contains the extra hypotheses; the following plain check does not.

- [ ] **16. Implement resets and semantic options.** Handle reset, reset-assertions, and global-declarations; classify other options and non-query commands explicitly.

   **Merge when:** Fixtures reproduce assertion/declaration lifetimes; unimplemented semantic commands fail visibly.

- [ ] **17. Preserve annotations and assertion names.** Process annotated terms; retain :named and source metadata, and classify solver-only patterns separately.

   **Merge when:** Named assertions map to generated hypotheses; removing a pattern does not alter the asserted formula.

- [ ] **18. Complete Boolean operators and arities.** Extend the working Boolean mapping with ite, n-ary distinct, supported n-ary operator forms, and explicit arity validation. Keep SMT Bool mapped uniformly to Lean Prop, including function arguments/results and equality.

   **Merge when:** Boolean arguments/results and proposition equality elaborate; finite truth-table checks match the intended operators, and malformed arities fail explicitly.

- [ ] **19. Generalize ordinary obligations and recover readable conclusions.** Extend the existing refutation builder to full scoped snapshots and explicit admissibility premises. Recover a final negated conclusion as an equivalent hypothesis-to-conclusion obligation where justified. Keep the canonical refutation available and close all required interpretation parameters.

   **Merge when:** A minimal matrix-bound fixture using supported declarations yields its intended arithmetic obligation with every hypothesis. The recovered and canonical forms are equivalent; the unedited frontend file remains part of the full current-suite gate.

- [ ] **20. Normalize CHC predicate arguments.** Introduce fresh typed universal variables and equality guards for compound/repeated arguments; preserve clause origins.

   **Merge when:** The Flux head arguments normalize without changing the clause meaning or dropping any false-head clause.

- [ ] **21. Emit deterministic Lean modules.** Add stable namespaces, escaped readable names, explicit types, dependency ordering, and source comments.

   **Merge when:** Two generations are byte-identical; colliding names produce distinct declarations.

- [ ] **22. Preserve edited proof templates during regeneration.** Add stable theorem references and safe regeneration to the emitted statement and proof sections. Leave existing edited proofs intact; fail visibly on an incompatible obligation change until the later interactive workflow supports reconciliation. Keep definitions/runtime free of sorry.

   **Merge when:** Regenerating an unchanged input preserves a manually edited proof section byte-for-byte; changed obligations cannot silently attach an old proof to a new statement, and holes occur only in designated proof templates.

### Complete the theories used by the current tests

- [ ] **23. Implement exact integer div/mod.** Use Euclidean division for nonzero divisors and explicit shared interpretation choices for zero cases.

   **Merge when:** Negative-divisor and repeated-zero-application regressions pass; Lean's fixed zero case is not silently substituted.

- [ ] **24. Implement BV arithmetic and comparisons.** Map modular arithmetic, bitwise operations, and signed/unsigned comparisons with explicit widths.

   **Merge when:** Exhaustive tiny-width cases and 32/64-bit boundaries agree with the chosen SMT semantics.

- [ ] **25. Implement BV extraction and width changes.** Add concat, extract, zero/sign extension, and repeat.

   **Merge when:** Boundary slices have exact widths; invalid indices fail; signed extension preserves the sign bit.

- [ ] **26. Implement BV shifts and rotations.** Add logical/arithmetic shifts and indexed rotations.

   **Merge when:** Zero, width-sized, and oversized amounts have the specified behavior.

- [ ] **27. Implement BV division and remainder.** Add unsigned/signed division, remainder, and signed modulo.

   **Merge when:** Zero divisors and minimum-signed-value divided by minus one match SMT semantics.

- [ ] **28. Implement BV/integer conversions.** Add the conversion spellings used in the corpus and encountered overflow predicates, with explicit signedness.

   **Merge when:** Negative/oversized integers wrap correctly; signed and unsigned conversion regressions distinguish their meanings.

- [ ] **29. Model extensional array carriers.** Introduce explicit array interpretations with select/store and read-over-write/extensionality laws; retain a justified native profile where applicable.

   **Merge when:** Array equality and updates have reviewed semantics without requiring every array carrier to be the full function space.

- [ ] **30. Close quantified-array interpretation parameters.** Quantify background array models in the correct direction for satisfiability/refutation, including nested array sorts and CHC relation domains.

   **Merge when:** A distinguishing quantified-array regression prevents accidental strengthening to full function arrays.

- [ ] **31. Implement constant arrays and Z3 array map.** Add typed dialect lowering and Lean semantics for constant arrays and the indexed map forms used by fixtures.

   **Merge when:** lh_sets_neg translates; parser surrogates reconstruct as real array operations, never unconstrained functions.

- [ ] **32. Generate monomorphic and mutually recursive datatypes.** Emit grouped inductives with constructors, nonemptiness handling, and dependency order.

   **Merge when:** Mutually recursive fixtures elaborate and preserve constructor disjointness/injectivity.

- [ ] **33. Generate parametric and nested datatypes.** Handle sort parameters, multiple instantiations, nested types, and constructor ascriptions.

   **Merge when:** Vec Int and nested PolySet.Lst fixtures elaborate with distinct correct type arguments.

- [ ] **34. Implement datatype selector interpretations.** Emit constructor equations and input-dependent arbitrary results for wrong constructors, with correct model quantification.

   **Merge when:** Repeated selector applications remain congruent and wrong-constructor values are not fixed to a global default.

- [ ] **35. Implement datatype testers and match.** Add qualified/unqualified testers, pattern branches, and catch-all binding.

   **Merge when:** Each constructor selects the right tester/branch; pattern variables cannot capture outer variables.

### Package and demonstrate the current tests

- [ ] **36. Package a standalone Lean output project.** Write the toolchain, Lake configuration, generated imports, and one canonical runtime/prelude copy.

   **Merge when:** The output builds from a clean directory without the translator repository on its import path.

- [ ] **37. Ship the current 321-query demo and regression suite.** Generate the entire original tests/smt and tests/chc corpus, add a small generate-and-Lean-check regression script, and check in reviewed representative output. Document a fresh-checkout walkthrough that translates a supplied file, checks the standalone output, and opens its editable theorem. Keep this harness simple: file/query counts, exit codes, and readable failures are sufficient.

   **Merge when:** All original 12 files and 321 checks elaborate; the four CHC problems preserve their 28 source clauses. The walkthrough works, unsupported examples fail visibly, and theorem holes are described as unfinished proofs. A JSON manifest, corpus downloader, benchmark service, and Flex solving are not prerequisites.

### Choose and inspect the larger competition inputs

- [ ] **38. Lock the competition inputs after the current demo works.** Add corpus.lock.json for complete named SMT-COMP and CHC-COMP editions; resolve CHC .set → .yml → input_files and record revision, track, and selection membership. This input lock defines the larger coverage target for an already functioning translator.

   **Merge when:** Every selected task resolves to an input; excluded/duplicate tasks are recorded rather than silently lost.

- [ ] **39. Fetch and verify the locked corpora.** Add a resumable corpus fetch command with archive/input hashes and a local cache; keep bulk data outside git.

   **Merge when:** A clean fetch reproduces the locked input list; a corrupted cached file is detected.

- [ ] **40. Inventory competition features against the working translator.** Scan the locked inputs for commands, sorts, indexed operators, dialect extensions, and sizes. Write feature-to-file and per-track reports, then use concrete unsupported examples to confirm or extend the following theory PRs.

   **Merge when:** Every locked input is scanned or gets an explicit scan error; every missing feature maps to a named implementation PR. This inventory does not block the earlier local demos.

### Extend translation against competition features

- [ ] **41. Support arbitrary nonempty uninterpreted sorts.** Emit interpretation parameters and nonemptiness requirements rather than one chosen opaque carrier.

   **Merge when:** Uninterpreted-sort validity ranges over all admissible carriers; model-existence quantifies interpretations existentially.

- [ ] **42. Translate recursive function definitions.** Implement the inventoried define-fun-rec/define-funs-rec forms using active scoped defining equations over function interpretations. Retain the equations even when assertions do not reference the function. For refutation, universally quantify interpretations and use equations as premises; for model existence, existentially quantify interpretations and conjoin equations.

   **Merge when:** Mutual/self-recursive fixtures preserve equations, including an unused recursive definition with no total solution. No reachability pruning deletes its constraint, and no fabricated Lean termination argument or new query-validity axiom appears.

- [ ] **43. Add an exact Real output profile.** Use Mathlib Real, exact numeric literals, arithmetic and ordering, and explicit division-at-zero interpretations.

   **Merge when:** Nonlinear Real fixtures elaborate; no decimal is rounded through a host float and Real is never replaced by Rat.

- [ ] **44. Implement mixed Int/Real operations.** Add to_real, floor-based to_int, and is_int.

   **Merge when:** Negative fractional values demonstrate floor behavior and exact coercions.

- [ ] **45. Introduce the SMT string carrier.** Represent the SMT codepoint domain, literals, concatenation, and character-count length.

   **Merge when:** Valid SMT codepoints missing from Lean Char remain representable; string length counts characters.

- [ ] **46. Implement string indexing and slicing.** Add at/substr with exact exceptional and clipping behavior.

   **Merge when:** Negative indices, zero/negative lengths, and out-of-range positions match the specification.

- [ ] **47. Implement string search and ordering.** Add prefix/suffix/contains, index-of, and lexicographic comparison operators present in the corpus.

   **Merge when:** Empty patterns and start-position boundary cases pass semantic regressions.

- [ ] **48. Implement literal string replacement.** Add first-occurrence and replace-all operations required by the inventory.

   **Merge when:** Overlapping and empty patterns use SMT behavior rather than host-library defaults.

- [ ] **49. Implement string numeric/codepoint conversions.** Add integer/string and codepoint/string conversions.

   **Merge when:** Invalid inputs, negative integers, leading zeros, and singleton requirements return the specified results.

- [ ] **50. Introduce regular-language semantics.** Represent RegLan values as languages and add membership, constants, Boolean language operators, concatenation, and star.

   **Merge when:** Quantified/uninterpreted RegLan values are not restricted to a syntax tree of constructible regexes.

- [ ] **51. Implement regex ranges and repetition.** Add ranges and indexed bounded/unbounded repetition forms from the corpus.

   **Merge when:** Empty-word/language and zero/lower/upper-bound cases have the specified membership semantics.

- [ ] **52. Implement regex-based replacement.** Add inventoried regex replacement operations with exact matching priority.

   **Merge when:** Leftmost/shortest and zero-length-match cases distinguish the implementation from literal replacement.

- [ ] **53. Introduce SMT floating-point values.** Define format-indexed values, literals, signed zeros, infinities, NaN, classification, comparisons, abs/neg, and min/max interpretation choices.

   **Merge when:** SMT equality and fp.eq are distinct where required; NaN is not treated as arbitrary unequal raw bit patterns.

- [ ] **54. Implement exact FP rounding.** Add all rounding modes over an exact arithmetic representation.

   **Merge when:** Halfway values, subnormals, underflow/overflow, and signed-zero boundaries pass reference checks.

- [ ] **55. Implement FP addition and subtraction.** Add the two arithmetic operators using the shared rounding implementation.

   **Merge when:** Tiny-format exhaustive tests cover cancellation and all exceptional value combinations.

- [ ] **56. Implement FP multiplication and division.** Add multiplication/division with exact special-value and rounding rules.

   **Merge when:** Tiny-format checks cover zero/infinity/NaN combinations and overflow/underflow.

- [ ] **57. Implement fused multiply-add.** Add fma with one final rounding.

   **Merge when:** A regression differs from separately rounded multiplication followed by addition.

- [ ] **58. Implement FP square root.** Add exact rounding of square roots and special-value handling.

   **Merge when:** Exact/inexact roots, negative inputs, signed zeros and rounding boundaries pass reference checks.

- [ ] **59. Implement FP remainder and integral rounding.** Add fp.rem and roundToIntegral.

   **Merge when:** Quotient ties, signed remainder zero, and each rounding mode match SMT semantics.

- [ ] **60. Implement FP format/bit conversions.** Add widening/narrowing and IEEE bit reinterpretation/encoding with specified NaN choices.

   **Merge when:** Specified round trips hold; ambiguous NaN encodings remain explicit interpretation choices.

- [ ] **61. Implement FP numeric conversions.** Add Real/BV↔FP numeric conversions and exceptional/out-of-range interpretations.

   **Merge when:** Signedness, rounding, NaN/infinity and out-of-range cases are covered without silently choosing unspecified values.

### Scale working output before automating benchmark runs

- [ ] **62. Preserve shared terms during emission.** Emit repeated subterms once using local bindings without changing scope.

   **Merge when:** A synthetic DAG grows with distinct nodes rather than exponentially with repeated occurrences.

- [ ] **63. Split large sessions into stable modules.** Shard generated queries while keeping stable query IDs, imports, and source mappings.

   **Merge when:** Changing one shard does not renumber unrelated queries; every original check is still represented.

### Add benchmark tooling to the working translator

- [ ] **64. Version the result manifest from real translator outputs.** Define the machine-readable contract now that ordinary/CHC translation, generated projects, and representative competition inputs exist. Record input/query IDs, source hashes, requested goal kind, required features, generated files, and separate translation/elaboration/proof outcomes. Derive it from the working pipeline's data and the benchmark worker's concrete needs.

   **Merge when:** Manifests describe real generated ordinary/CHC artifacts; schema fixtures reject missing provenance and never equate typechecked with proved.

   **Deferred work:** No schema draft is currently present in the working tree. Build it from actual translator outputs when this PR is reached; it does not constrain earlier implementation. Stop for review after each subtask.

   - [ ] **64.1. Record a candidate provenance schema.** Create `schemas/manifest.schema.json` and document field conventions in `schemas/README.md`, covering input paths/hashes, query IDs/locations, required features, and generated files.
   - [ ] **64.2. Reconcile the draft with real outputs and requested tasks.** Check the working emitter's artifacts and source references; distinguish ordinary SMT refutation from CHC model existence, keeping source kind and requested target separate from solver metadata.
   - [ ] **64.3. Define independent result fields.** Separate recorded solver answers, translation, Lean elaboration, and proof completion; identify the exact proof target.
   - [ ] **64.4. Add Lean manifest types and JSON serialization.** Implement `Smt2Lean/Manifest.lean` against the revised schema, including reference and source-location validation.
   - [ ] **64.5. Add example manifests from actual translations.** Include successful translation, an unsupported query, and a typechecked theorem template containing `sorry`.
   - [ ] **64.6. Add manifest validation tests.** Round-trip valid manifests, reject malformed/provenance-free records, and ensure elaboration never implies proof completion.

- [ ] **65. Automate Lean checks with independent result classification.** Wrap the Lean invocations already used by the demos in a bounded elaboration runner with structured diagnostics and admitted-proof reporting. Populate the newly defined manifest from actual results; retain the simple local checking path.

   **Merge when:** A malformed statement fails; a valid statement with a sorry theorem is recorded as elaborated and unproved. Solver metadata, translation, elaboration, and completed proof status remain independent.

- [ ] **66. Build the isolated benchmark worker.** Run translation and Lean elaboration as separate bounded processes and emit one result per task/query.

   **Merge when:** Crashes and timeouts are classified; one failing task cannot abort or hide the remaining corpus.

- [ ] **67. Add resumable content-addressed benchmark runs.** Cache by input, translator, runtime, output profile, dependency, and toolchain hashes.

   **Merge when:** An unchanged run resumes; changing any semantic input invalidates the affected cache.

- [ ] **68. Publish per-track translation coverage.** Generate machine-readable and readable reports including unsupported inputs, partial sessions, and resource failures.

   **Merge when:** Totals reconcile with the locked selection; only fully translated/elaborated tasks count as successful.

- [ ] **69. Gate the complete pinned competition selections.** Add a release check joining inventory coverage, semantic regressions, query counts, and the full benchmark results.

   **Merge when:** Stage 1 passes only when every selected input and query translates faithfully and elaborates; unimplemented inventoried features block this PR's release gate.

## Stage 2: frontend tooling

### Integrate the working translator with external frontends

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
