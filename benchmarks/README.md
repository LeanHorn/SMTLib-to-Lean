# Translation benchmark anchor

Run SMT-LIB files through the existing translator and independently check the
generated Lean. The runner uses Python's standard library on macOS/Linux.
It never invokes an SMT solver or Flex. Proof templates remain unproved.

Build once, then run from the repository root:

```sh
lake build smt2lean

# Every .smt2 file below a directory, in sorted order.
lake env python3 benchmarks/run.py /path/to/queries --out benchmarks/results/my-run

# Specific files, including files from different directories.
lake env python3 benchmarks/run.py /path/one.smt2 /other/two.smt2 \
  --out benchmarks/results/two-queries

# A text file with one path per line, or a CSV with a path column.
lake env python3 benchmarks/run.py --list /path/queries.txt \
  --out benchmarks/results/list-run
```

List paths are relative to the list file's directory; `--root` overrides that
base. Absolute paths work too. Text lists allow blank lines and `#` comments.
CSV selections can pin each input with a `sha256` column and carry source/task
metadata in other columns. A hash mismatch is recorded and the file is not run.
Repeated paths are run once; distinct paths with identical content remain distinct.
The output directory must be new. Existing runs are never overwritten.

The runner passes `--max-rec-depth 4096` to `smt2lean` by default. Use
`--max-rec-depth N` to override it; `N` must be positive. The value is recorded
in `run.json` and each translation command, and emitted as `set_option maxRecDepth N`
in `Query.lean`. Translation, statement checks, and template checks use that setting.

## The first ten inputs

```sh
lake env python3 benchmarks/run.py \
  --list benchmarks/pilot-10.csv \
  --root ../SMTLib-benchmarks/corpora \
  --out benchmarks/results/pilot-10
```

The manifest pins five **SMT-LIB 2025** inputs and five **CHC-COMP 2026** inputs,
15,070 input bytes in total. It records input/archive hashes, source URLs,
CHC snapshot revision, category membership, and task metadata paths/hashes.
This SMT portion comes from the SMT-LIB release, not the official SMT-COMP
2025 task selection. No large archive needs extracting for this pilot.

| # | Source / category | Feature to inspect |
| --- | --- | --- |
| 1 | TwoSquares / QF_UFLIA | Uninterpreted carrier and integer functions |
| 2 | MathSAT / QF_UFLIA | Nested lets, conditionals, large conjunction |
| 3 | Arrays decision-procedure example / QF_AUFLIA | Stores, extensionality, functions |
| 4 | Store commutation / QF_AUFLIA | Nested stores and array equality |
| 5 | Barrett datatype regression / QF_DT | Mutual recursion, selectors, testers |
| 6 | Aeval / LIA-Lin | Loop invariant with conditional update |
| 7 | RustHorn Fibonacci / LIA | Multiple relation premises and Bool arguments |
| 8 | Sally / LRA-Lin | Real arithmetic and nested lets |
| 9 | RustHorn mutable borrows / ADT-LIA | Records and selectors in Horn clauses |
| 10 | Eldarica REVE / BV-Lin | 32-bit relation arguments and signed comparison |

These were chosen for small, readable examples across implemented features before
running translation. All ten remain in the selection regardless of outcome.
The CHC entries were checked against their category `.set` files and YAML
`input_files` mappings. Recorded solver verdicts are provenance only; some tasks
are satisfiable and some are unsatisfiable. They do not determine translation
success or imply that an emitted theorem can be proved.

This is a runner/translation pilot, not a competition-wide coverage estimate.
The input manifests are tracked; raw corpora and run outputs stay local.

## Fifty-input expansion

```sh
lake env python3 benchmarks/run.py \
  --list benchmarks/pilot-50.csv \
  --root ../SMTLib-benchmarks/corpora \
  --out benchmarks/results/pilot-50-rerun
```

`pilot-50.csv` retains the original ten entries and adds twenty SMT-LIB and twenty
CHC-COMP inputs: 25 of each, 313,309 input bytes total. It uses the same runner,
translator binary, and limits as the ten-input baseline. Choose a new output name
for each rerun.

The SMT categories contain 8 QF_UFLIA, 9 QF_AUFLIA, and 8 QF_DT inputs. The CHC
selection covers all eleven available categories, including arrays and mixed
Int/Real arithmetic. New candidates are 300 bytes–16 KiB, except mixed Int/Real
CHCs, which allow up to 64 KiB because this snapshot has no examples below 16 KiB.
Only existing CHC category references with resolvable input mappings are eligible.

Within each category quota, choose a currently least-represented source family,
breaking ties by SHA-256 of `smt2lean-pilot-50-v1` concatenated with the corpus-relative
input path. Added inputs must have new paths and new content hashes. Selection
was frozen before translation; unsuccessful inputs remain in the results. This
is a small-input expansion, not a full-corpus coverage estimate.

The first run completed with **48/50 passing**: 23/25 SMT inputs and 25/25 CHC
inputs. `dlx-regfile` could not print the complete proposition; `vlsat3_b40`
translated but exceeded Lean's recursion-depth limit during checking. All original
ten inputs still passed. See the local `benchmarks/results/pilot-50/summary.md`
and `results.csv` for outputs, timings and diagnostics. The runner and limits were
unchanged; both failures remain in the fixed selection.

## 150 distinct inputs

`pilot-100-new.csv` adds 100 inputs whose paths and SHA-256 hashes are disjoint
from `pilot-50.csv`. `pilot-150.csv` contains the original 50 followed by those
100: 75 SMT-LIB and 75 CHC-COMP inputs, 998,777 bytes total. All 150 paths and
content hashes are distinct. The same size caps and family-balancing rule apply,
with tie-breaking seed `smt2lean-pilot-150-v1`.

Run the complete selection into a new directory:

```sh
lake env python3 benchmarks/run.py \
  --list benchmarks/pilot-150.csv \
  --root ../SMTLib-benchmarks/corpora \
  --out benchmarks/results/pilot-150-rerun
```

For the initial expansion, only the new 100 are executed, at
`benchmarks/results/pilot-100-new/`. The combined report at
`benchmarks/results/pilot-150/` reuses the existing 50 results after checking
matching runner/binary hashes, Lean/dependency versions, and limits. Each copied
case preserves its original result, run identity, logs, timings and generated
output. It is explicitly an aggregate, with no single 150-input wall-time claim.

Results: **98/100 new inputs passed**, giving **146/150 overall** (71/75 SMT,
75/75 CHC). The four retained failures are `dlx-regfile` (complete proposition
printing) and `vlsat3_b40`, `hash_uns_04_17`, `hash_sat_05_16` (Lean recursion-depth
limits). No inputs were replaced, no limits were increased, and no translator or
runner changes were made for the expansion. All proof templates remain unproved.

## What a run records

```text
my-run/
  summary.md                # Counts, timings, links to each generated Query.lean
  results.csv               # One row per selected input, including failures
  run.json                  # Revision, binary/runner hashes, versions, limits
  selection.json            # Exact paths and optional selection metadata
  lean-toolchain            # Pinned Lean version
  lake-manifest.json        # Dependency revisions
  lakefile.toml
  runner.py                 # Runner source used for this run
  working-tree.patch        # Tracked changes relative to the recorded revision
  cases/001-name/
    Input.smt2              # Exact bytes given to the translator
    result.json             # Commands, exit codes, timings, hashes, diagnostics
    translation.*.log
    statements.*.log
    template.*.log
    generated/
      Query.lean            # Original generated statements and sorry templates
      Statements.lean       # Statements/helpers checked separately
```

Translation success and the two Lean checks have separate statuses. A row passes
only if translation succeeds, every input check has a generated goal, and both
Lean checks succeed. Statement checking uses `--error=hasSorry` to reject
admissions while retaining ordinary lint warnings. Template checking permits
`sorry`; warning counts and admission counts are recorded separately. Lean logs
use its JSON diagnostic format. No proof is reported as completed.

`unsupported` means the translator explicitly returned `cvc5.Error.unsupported`.
Other native/backend errors, reconstruction errors, Lean errors, timeouts,
signals, missing inputs, hash mismatches, and size limits remain distinct.
The CLI does not yet provide structured parser-vs-reconstruction diagnostics;
the original diagnostic and exit code are always retained. Support is not inferred
from a benchmark's logic name. A successful typecheck alone does not establish
semantic correctness; the existing semantic regressions remain necessary.

Input query counts come from a lightweight top-level command scan that ignores
comments, strings, and quoted symbols. They are bookkeeping, not input validation.
Multi-query files count as one selected file and record their query counts
separately. A failed session cannot count as a partial success.

Timings are wall-clock seconds for separate translator/Lean processes, including
startup and imports; they exclude the build. Cold caches can affect these figures.
Generated files and logs are preserved, including successful outputs for review.
Source comments point to the saved `Input.smt2`; results also retain its original path.

## Bounds and reruns

Defaults: one input at a time, 30 seconds for translation, 60 seconds for each
Lean check, 10 MiB per input, 16 MiB per generated/log file, and Lean's `-M2048`
checker allocation limit. See `--help` to change them. Timeouts kill the stage's
process group. The translator has no hard RSS limit, and the per-file limit is
not a total run storage budget. Keep the selection small until measured.

Results are saved after each input. Interrupting a stage records that interruption;
remaining inputs stay `not_run`. This runner has no resume/cache machinery.
Rerun into a new directory and compare the fixed input hashes and outcomes.
The run metadata identifies dirty working trees as well as exact executable and
runner hashes. Rebuilding is the caller's responsibility.

Exit codes: `0` all selected inputs passed; `1` at least one non-passing result;
`2` invalid invocation/setup; `130` interrupted. A nonzero result does not discard
the report or stop later inputs after an ordinary per-input failure.

Runner regression tests (included in `tests/run.sh`):

```sh
lake env python3 tests/anchor.py
```
