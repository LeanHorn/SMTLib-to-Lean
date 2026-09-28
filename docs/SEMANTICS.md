# Translation contract

This document specifies what a supported SMT-LIB → Lean translation must mean.
It is the contract for task 1 in [PR-PLAN.md](PR-PLAN.md), covering more than the
Boolean fragment currently supported by the CLI. The architecture and investigated
dependencies are described in [FLEX-ARCHITECTURE.md](FLEX-ARCHITECTURE.md).

The required result is a faithful, well-typed statement with an optional unfinished
theorem template. Neither successful elaboration nor a theorem containing `sorry`
establishes that the statement is true or provable.

## 1. Translate a query snapshot

Each `check-sat` or supported `check-sat-assuming` identifies one query. Its meaning
includes:

- All active assertions and that check's temporary assumptions.
- Visible declarations with their binding identities, sorts, and arities.
- Definition bodies resolved in the environments where they were defined.
- Applicable datatype semantics and active recursive defining equations.
- Background theory semantics and semantic options affecting that snapshot.

The translator must respect declaration and assertion lifetimes, including
`push`, `pop`, resets, and supported declaration-scope options. Temporary
assumptions must not leak into another query. Identically spelled symbols in
different scopes must not accidentally share an interpretation.

Ordinary abbreviations may be expanded or omitted when irrelevant, provided their
meaning and dependencies are preserved. Recursive defining equations remain
constraints even when assertions never mention the defined function: those
equations can themselves rule out every interpretation.

Every source query must receive an explicit outcome. A session with an unsupported
or failed query is incomplete, even if its other queries translate successfully.

## 2. Close over the complete interpretation

For a query `q`, use the following semantic specification:

```text
I                    = the interpretation parameters needed by q
Admissible_q(I)       = the required theory laws and active defining equations
Assertions_q(I)       = the conjunction of active assertions and temporary assumptions

Satisfiable_q         := ∃ I, Admissible_q(I) ∧ Assertions_q(I)
Refutation_q          := ∀ I, Admissible_q(I) → Assertions_q(I) → False
```

This notation is a contract, not a requirement to emit a single record named `I`.
The printer may expose readable parameters and hypotheses instead.

Interpretations include more than declared constants: they include uninterpreted
functions, arbitrary nonempty uninterpreted carriers, unknown CHC relations, and
any background models or unspecified operator results required by the theory.
For example, a quantified-array encoding may need an admissible array carrier
with select/store operations rather than one fixed function space.

A native Lean type or operation may discharge an interpretation parameter only
when its adequacy is established for the supported fragment. Choosing convenient
interpretations must not strengthen a validity claim or change model existence.
The desired conclusion and recorded solver answer must never be inserted into
`Admissible_q` as assumptions.

For supported inputs, the translated model-existence proposition must represent
the source query's model existence, and its refutation proposition must represent
the absence of such a model under the same theory semantics. This is a semantic
requirement, not something implied by passing the Lean typechecker.

## 3. Select the task explicitly

The requested task is separate from recorded results:

| Input kind | Default requested task | Meaning |
| --- | --- | --- |
| Ordinary SMT verification query | Refutation | No admissible interpretation satisfies the active assertions |
| CHC assertion system | Model existence | Relation interpretations exist that satisfy every clause |

A caller may explicitly request model existence or refutation where supported.
The generated declaration and its accompanying metadata must identify the chosen
task. The input kind and explicit request determine the task; `sat`, `unsat`,
`unknown`, missing answers, or a timeout do not switch it automatically.

For an ordinary query containing hypotheses `H` and a final assertion `¬ G`, a
readable goal `H → G` may replace the closed refutation of `H ∧ ¬ G` using
classical equivalence. The transformation must preserve all other assumptions,
interpretation parameters, and their quantification. A syntactic final negation
does not establish that the recovered conclusion is true.

## 4. Keep CHC model existence positive

A CHC problem has the canonical shape:

```text
∃ relation interpretations,
  (∀ clause_1 locals, constraints → relation premises → head) ∧
  ... ∧
  (∀ clause_n locals, constraints → relation premises → head)
```

Each head is a relation application or `False`. Preserve facts, multiple relation
premises, mutual recursion, and every false-head clause. All clause variables,
including variables occurring only in the body, remain universally quantified.
A nullary relation has Lean type `Prop`.

The displayed form assumes the background interpretation has already been accounted
for. If a problem also needs background interpretation parameters, retain their
correct model-existence quantification. Do not disguise nonpredicate choices as
unknown relations just to fit Flex's existing interface.

The canonical `Problem : Prop` stays positive for every recorded status. A requested
CHC refutation is a separate task `¬ Problem`. Failure to construct a witness for
`Problem` is not evidence for `¬ Problem`.

Z3 fixedpoint `rule`/`query` input is a separate dialect whose query asks about
derivability. It must be rejected until an explicit adapter accounts for its
semantics and result polarity; it must not silently enter the assert/check-sat path.

## 5. Solver metadata must not change the statement

Recorded `; SMT Says:` comments, `:status` fields, benchmark verdicts, and observed
solver responses are evidence/provenance metadata, never Lean premises or proofs.
Inconsistent or absent metadata must not change the assertion system.

With semantic input, output profile, and requested task held fixed, changing only
recorded status must preserve the canonical propositions and chosen proof target,
up to renaming and the documented semantics-preserving normalizations. Comments,
diagnostics, source positions, and raw-source hashes may differ; byte-identical
artifacts are not required when their provenance changes.

The following are contract examples for future executable translator regressions.
They are hand-written expected outputs, not output already produced by the CLI.

### Ordinary SMT example

```smt2
(declare-fun x () Int)
(assert (= x 0))
(assert (not (>= x 0)))
(check-sat)
```

Its canonical propositions and recovered verification condition can be written:

```lean
namespace OrdinaryContractExample

def Assertions (x : Int) : Prop := x = 0 ∧ ¬ (0 ≤ x)
def ModelExists : Prop := ∃ x : Int, Assertions x
def Refutation : Prop := ∀ x : Int, Assertions x → False
def VerificationCondition : Prop := ∀ x : Int, x = 0 → 0 ≤ x

end OrdinaryContractExample
```

| Recorded answer attached to this same query | Canonical propositions | Requested default task |
| --- | --- | --- |
| `sat` | The definitions above | `Refutation` |
| `unsat` | The definitions above | `Refutation` |
| `unknown` | The definitions above | `Refutation` |
| No answer / timeout | The definitions above | `Refutation` |

The conflicting labels deliberately exercise independence from metadata; the table
does not claim that every label is a correct solver answer for this query.

### CHC example

```smt2
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (y Int))
  (=> (and (Inv x) (<= x 10) (= y (+ x 1))) (Inv y))))
(assert (forall ((x Int)) (=> (and (Inv x) (> x 15)) false)))
(check-sat)
```

The expected model-existence statement is:

```lean
namespace HornContractExample

def Problem : Prop :=
  ∃ Inv : Int → Prop,
    (∀ x : Int, x = 0 → Inv x) ∧
    (∀ x y : Int, Inv x → x ≤ 10 → y = x + 1 → Inv y) ∧
    (∀ x : Int, Inv x → x > 15 → False)

end HornContractExample
```

| Recorded status for this same clause system | Canonical proposition | Requested default task |
| --- | --- | --- |
| `sat` | `Problem` above | `Problem` |
| `unsat` | `Problem` above | `Problem` |
| `unknown` | `Problem` above | `Problem` |
| No answer / timeout | `Problem` above | `Problem` |

An explicitly requested refutation would target `¬ Problem` in every row.

## 6. Preserve theory semantics

Each supported theory/operator mapping must state its applicability conditions and
cover its exceptional cases. In particular:

- Use uniform SMT `Bool` → Lean `Prop` for the initial profile, including Boolean
  data and relation arguments. Boolean equality may use proposition equality or
  its equivalent `↔`; do not confuse a Boolean value with a proof of that value.
- Preserve nonempty SMT domains, exact integers/reals, bitvector widths and
  signedness, and datatype constructor semantics.
- Preserve unspecified results as consistent interpretations. Division by zero
  and wrong-constructor selectors must not become convenient fixed defaults or
  fresh unrelated values at each occurrence. Quantify these choices universally
  for refutation and existentially for model existence.
- Do not silently substitute `Rat` for `Real`, native Lean strings for a different
  required character domain, or full function arrays for arbitrary quantified
  array models. Such mappings need an applicable semantic justification.
- Expanding definitions, normalizing predicate arguments, recovering conclusions,
  or pruning unused declarations must preserve the complete closed problem.

A fragment may reject cases it cannot faithfully represent. Unsupported syntax,
operators, dialects, or semantic options must produce an explicit diagnostic with
the affected source location. Assertions must never be dropped or unsupported
builtins replaced with unconstrained functions merely to obtain elaboration.

## 7. Confine admissions to proof templates

Canonical statement definitions and their semantic dependencies must not contain
`sorry`, admitted definitions, or new axioms asserting benchmark validity.
Theory laws belong in explicit admissibility assumptions or justified runtime
semantics, not unchecked claims that a particular query is true.

Separate editable theorem templates may contain unfinished proofs, for example:

```lean
theorem ordinary_pending : OrdinaryContractExample.Refutation := by
  sorry
```

Generated statements must not import unfinished proof templates. One admitted
benchmark theorem must not be used to interpret or validate another query.
Existing foundational axioms and any proof dependencies/trust settings must be
distinguished from new query-specific assumptions when proof results are reported.

## 8. Report outcomes separately

| Outcome | What it establishes |
| --- | --- |
| Parsed / sort-checked | The frontend accepted the syntax and sorts |
| Supported translation | The query was translated using the declared semantic contract for its fragment |
| Lean-elaborated | The generated declarations are well-typed |
| Admitted template | A theorem still has an unfinished proof, even if its file elaborates |
| Flex-compatible | The generated problem matches the supported Flex representation |
| Proved | A completed proof of the explicitly requested proposition, with dependencies recorded and no admitted proof dependency |
| Refuted | A completed proof of the negation of an explicitly named reference proposition, not merely a failed proof attempt |
| Unresolved / failed | An explicit unsupported case, remaining goal, error, or resource limit |

These outcomes must remain distinguishable; their concrete serialization belongs
to the later manifest task in [PR-PLAN.md](PR-PLAN.md). Always record the exact
proved target and requested task kind. For
example, a completed proof of a requested `¬ Problem` both completes that task and
refutes the canonical `Problem`; it does not refute `¬ Problem`. These descriptions
are related observations, not mutually exclusive verdicts with an implicit polarity.

Parsing or elaboration alone does not establish semantic preservation. No solver
timeout, tactic failure, missing qualifier, or incomplete proof is an
unsatisfiability certificate.

## 9. Review and later regression obligations

For this documentation task, review the interpretation closure, task defaults,
status-invariance examples, and admission boundaries above. As the corresponding
implementation tasks land, the regression suite must check:

- Identical semantic input and requested task with `sat`, `unsat`, `unknown`, and
  absent metadata yields the same canonical propositions and proof targets.
- Scope changes, temporary assumptions, and defining equations affect precisely
  their intended snapshots, while metadata changes affect only provenance.
- Every normalization preserves its closed problem, including background choices.
- Pure statements elaborate without admitted semantic dependencies; theorem holes
  remain confined to designated proof templates and are reported as unfinished.
- Unsupported or partial translation is visible and is not counted as complete.

This contract does not add a parser, translator, manifest implementation, solver,
or Flex adapter. Those are separate numbered tasks in the PR plan.
