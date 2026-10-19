This corpus contains 2,935 benchmark files: 1,609 from SMT-COMP 2025 and 1,326 from CHC suites. The ten local archives repackage complete upstream divisions or suite directories with unchanged source bytes; their filenames are local names.

| Local archive | Exact upstream source and directory | Files |
| --- | --- | ---: |
| [smtcomp-2025-QF_UFLIA.tar.gz](smt-queries/smtcomp-2025-QF_UFLIA.tar.gz) | [single_query.tar.gz][smt2025] · `single_query/QF_UFLIA/` | 300 |
| [smtcomp-2025-QF_AUFLIA.tar.gz](smt-queries/smtcomp-2025-QF_AUFLIA.tar.gz) | [single_query.tar.gz][smt2025] · `single_query/QF_AUFLIA/` | 534 |
| [smtcomp-2025-QF_DT.tar.gz](smt-queries/smtcomp-2025-QF_DT.tar.gz) | [single_query.tar.gz][smt2025] · `single_query/QF_DT/` | 352 |
| [smtcomp-2025-QF_AUFBV.tar.gz](smt-queries/smtcomp-2025-QF_AUFBV.tar.gz) | [single_query.tar.gz][smt2025] · `single_query/QF_AUFBV/` | 75 |
| [smtcomp-2025-QF_UFNRA.tar.gz](smt-queries/smtcomp-2025-QF_UFNRA.tar.gz) | [single_query.tar.gz][smt2025] · `single_query/QF_UFNRA/` | 48 |
| [smtcomp-2025-LIA.tar.gz](smt-queries/smtcomp-2025-LIA.tar.gz) | [single_query.tar.gz][smt2025] · `single_query/LIA/` | 300 |
| [tricera-adt-arr.tar.gz](smt-queries/tricera-adt-arr.tar.gz) | [TriCera snapshot][tricera] · [`adt-arr/`](https://github.com/chc-comp/tricera-adt-arr/tree/0214c9fb4845013dc9ec5d1f8c4376efc6c6e365/adt-arr) | 635 |
| [chccomp-2026-rust-horn.tar.gz](smt-queries/chccomp-2026-rust-horn.tar.gz) | [CHC-COMP 2026 snapshot][chc2026] · [`rust-horn/`](https://github.com/chc-comp/chc-comp26-benchmarks/tree/b4fa7a708e5863bbcdb5de50d692ead3a67cbedc/rust-horn) | 73 |
| [chccomp-2026-sally-chc-benchmarks.tar.gz](smt-queries/chccomp-2026-sally-chc-benchmarks.tar.gz) | [CHC-COMP 2026 snapshot][chc2026] · [`sally-chc-benchmarks/`](https://github.com/chc-comp/chc-comp26-benchmarks/tree/b4fa7a708e5863bbcdb5de50d692ead3a67cbedc/sally-chc-benchmarks) | 179 |
| [chccomp-2026-ringen-adt-benchmarks.tar.gz](smt-queries/chccomp-2026-ringen-adt-benchmarks.tar.gz) | [CHC-COMP 2026 snapshot][chc2026] · [`ringen-adt-benchmarks/`](https://github.com/chc-comp/chc-comp26-benchmarks/tree/b4fa7a708e5863bbcdb5de50d692ead3a67cbedc/ringen-adt-benchmarks) | 439 |
| **Total** | | **2,935** |

Counts include duplicates, five empty TriCera controls, and one RInGen file without a query. The separate 965-file Flex corpus is excluded. TriCera is an upstream stress suite, not a claimed competition selection.

Archives are not tracked in Git. Each retains upstream attribution and source metadata. [inputs.csv](inputs.csv) records per-file hashes, [SHA256SUMS](SHA256SUMS) records archive hashes, and [sources.json](sources.json) records provenance. No evaluation was run during corpus preparation.

Original download timestamps were not recorded. The sibling corpus inventory (`SMTLib-benchmarks/metadata/archives.json`) was created on 2026-10-02 UTC; these ten archives were repackaged and SHA-256 verified on 2026-10-18. Sources are pinned to Zenodo record **16887742**, TriCera commit `0214c9fb4845013dc9ec5d1f8c4376efc6c6e365`, and CHC-COMP 2026 commit `b4fa7a708e5863bbcdb5de50d692ead3a67cbedc`; upstream archive hashes are in [sources.json](sources.json).

### Solver baseline

Software verified on **2026-10-18**:

| Software | Version | Role |
| --- | --- | --- |
| Z3 / Spacer | [4.15.4](https://github.com/Z3Prover/z3/releases/tag/z3-4.15.4) | Same Z3 executable; SMT / CHC |
| cvc5 CLI | [1.3.2](https://github.com/cvc5/cvc5/releases/tag/cvc5-1.3.2), git `86cecd8` | SMT |
| Eldarica, native arm64 | [2.3](https://github.com/uuverifiers/eldarica/releases/tag/v2.3) | CHC |
| Python | 3.9.6 | Runner |
| Lean | 4.33.1 | Later translator evaluation |
| cloc | 2.08 | Later LOC measurement |

The fresh baseline launched on **2026-10-18 at 15:54 UTC (23:54 Hong Kong)** using unchanged inputs: 1,609 SMT files × Z3/cvc5 and 1,326 CHC files × Spacer/Eldarica, totaling **5,870 runs**. Each process gets a **300-second wall deadline**, including startup, a sampled-RSS limit of **4 GiB per solver group**, and a **16 MiB cap per stdout/stderr log**. Four workers share a Mac16,12 with 10 CPUs and 24 GiB RAM; the background run uses `nice 10`. These are shared-machine wall times, not dedicated CPU times.

Invocation from the repository root (the existing run is already active; use a new output directory for another run):

```sh
caffeinate -is nice -n 10 python3 scripts/evaluate_solvers.py \
  --out evaluation/results/solvers-300s-2026-10-18-fresh \
  --z3 /opt/homebrew/Cellar/z3/4.15.4/bin/z3 \
  --cvc5 /opt/homebrew/Caskroom/cvc5/1.3.2/cvc5-macOS-arm64-static/bin/cvc5 \
  --eldarica evaluation/tools/eldarica-2.3 \
  --timeout 300 --workers 4 --memory-mb 4096 --log-mb 16
```

The run directory `results/solvers-300s-2026-10-18-fresh/` contains the runner snapshot, `metadata.json` (timestamps, binary hashes, raw versions and exact commands), incremental `results.jsonl`/`results.csv`, `progress.json`, `summary.json`, `candidates.csv`, and raw `logs/`. Summaries report answer/error/timeout/memory/log-cap counts, solved percentages, successful-runtime median/p95/max, and disagreements. Distinct-input candidates require both solvers to time out or return `unknown`; errors and empty/queryless controls are excluded. Results are preliminary until `progress.json` reports `complete`; current progress is updated every five seconds. The launch does not establish that 50–100 candidates exist.

[smt2025]: https://zenodo.org/records/16887742/files/single_query.tar.gz?download=1
[tricera]: https://github.com/chc-comp/tricera-adt-arr/archive/0214c9fb4845013dc9ec5d1f8c4376efc6c6e365.zip
[chc2026]: https://github.com/chc-comp/chc-comp26-benchmarks/archive/b4fa7a708e5863bbcdb5de50d692ead3a67cbedc.zip

The original `results/solvers-300s-2026-10-18/` attempt failed during timeout cleanup; its 11 records are excluded. The fresh run repeats every solver/input pair from zero. Before restart, five targeted cleanup tests passed and a 20-job native-solver smoke run completed, including six timeouts.

### Translation evaluation (RQ1/RQ2)

Evaluate one complete archive at a time, starting with the **300 distinct QF_UFLIA inputs**. The first run is `results/translation-QF_UFLIA-2026-10-19/` (directory date is Hong Kong local time; metadata timestamps are UTC). It uses one worker alongside the solver baseline, a 300-second deadline per translation/Lean-check stage, 4 GiB sampled process-group RSS, and `maxRecDepth=4096`. Build time is excluded; subprocess wall times include startup and monitoring/cleanup overhead. Shared-machine times are preliminary performance measurements.

```sh
lake build smt2lean
caffeinate -is nice -n 10 lake env python3 scripts/evaluate_translation.py \
  --archive smtcomp-2025-QF_UFLIA.tar.gz \
  --out evaluation/results/translation-QF_UFLIA-2026-10-19 \
  --generated evaluation/generated/smtcomp-2025-QF_UFLIA
```

The runner verifies archive/input hashes, translates each file independently, checks statements with `--error=hasSorry`, and separately checks the complete proof template. It compares input query counts to emitted goals. Failures remain in the denominator; typechecking does not establish semantic equivalence. Generated files retain their original basenames, with preserved relative subdirectories and unchanged translator output bytes.

Incremental `results.csv`/`results.jsonl`, stage logs, `progress.json`, and `summary.json` record outcomes, separate stage times, bytes, code LOC, lexical tokens, and size ratios. Metadata pins the translator/Lean/cloc binaries, source hashes, exact commands, limits, and runner snapshots. `cloc` 2.08 counts physical code lines after comment-aware masking (custom SMT-LIB language, native Lean); Lean size metrics exclude proof stubs and import/option/namespace scaffolding. Token conventions and counting projections are saved with the run. Size summaries cover fully typechecked inputs, and include the ten largest token expansions. Empty/queryless controls and duplicate hashes are identified separately.

The three-input, 30-second preflight is separate from the full run: two inputs passed and one translation timed out. All inputs are repeated with the full limits. The runner stops after this archive; it does not start the next archive automatically.

Run with AC power and the lid open. `caffeinate -is` prevents idle sleep (and asserts against system sleep on AC power) for the command's lifetime; the display may sleep. The original runs above started without this guard and experienced confirmed macOS sleep events. Their elapsed counters exclude suspend time; retain results as exploratory, and repeat timing measurements under controlled conditions. On 2026-10-19 at 00:31 UTC, `caffeinate -is -w 81861` was attached to the existing solver runner; `results/solvers-300s-2026-10-18-fresh/sleep-prevention.json` records the guard. This does not repair earlier measurements or protect against shutdown or closing the lid.

The QF_AUFLIA run launched on **2026-10-19 at 00:57 UTC** in `results/translation-QF_AUFLIA-2026-10-19/`, writing Lean files to `generated/smtcomp-2025-QF_AUFLIA/`. It covers **534 files (533 distinct contents)** with the same pinned translator binary, one worker, 300 seconds per stage, 4 GiB sampled process-group RSS, and `maxRecDepth=4096`. `caffeinate -is` was attached from the start. Concurrent solver work makes these exploratory shared-machine timings. The runner stops after this archive.

QF_AUFLIA completed with **533/534 passing**; `scrambled295901.smt2` translated but reached Lean's default 200,000-heartbeat limit while checking an assertion definition. QF_AUFBV (**75 distinct files**) launched next on **2026-10-19 at 01:45 UTC**, using the unchanged translator and limits, with `caffeinate -is` from launch. Its records are in `results/translation-QF_AUFBV-2026-10-19/` and Lean output in `generated/smtcomp-2025-QF_AUFBV/`. It also stops after its archive; timings remain exploratory while solvers run concurrently.

LIA (**300 distinct inputs**) launched on **2026-10-19 at 02:10 UTC**, using the same pinned translator, one worker, 300 seconds per stage, 4 GiB sampled process-group RSS, and `maxRecDepth=4096`, with `caffeinate -is` from launch. Records are in `results/translation-LIA-2026-10-19/` and Lean output in `generated/smtcomp-2025-LIA/`. At the user's request, it overlaps QF_AUFBV and four solver workers, so timings remain exploratory shared-machine measurements. The runner stops after LIA.

LIA completed with **300/300 passing**. QF_AUFBV completed with **38/75 passing**; its 37 failures comprise 11 memory limits, 10 wall-time limits, 7 recursion limits, and 9 heartbeat limits. QF_UFNRA (**48 distinct files**) launched next on **2026-10-19 at 03:07 UTC**, using the unchanged translator/limits and `caffeinate -is` from launch. Records are in `results/translation-QF_UFNRA-2026-10-19/`, with output in `generated/smtcomp-2025-QF_UFNRA/`. This run stops after its archive; concurrent solver work means its timings are exploratory.

The automatic continuation queue uses `scripts/evaluation_queue.py --out evaluation/results/evaluation-queue-2026-10-19`, wrapped in `caffeinate -is`. It reuses completed runs, waits for QF_UFNRA, then evaluates QF_DT (352), RustHorn (73), Sally (179), RInGen (439), and TriCera (635) sequentially. It also watches the existing solver baseline. Its `progress.json` covers the full 2,935-input translation corpus and 5,870 solver runs; final combined results and a macOS notification follow completion of both. Translator and runner pins remain fixed. An infrastructure failure produces a failure notification rather than a completion claim. Keep the Mac plugged in with the lid open; analysis and fixes follow completion.
