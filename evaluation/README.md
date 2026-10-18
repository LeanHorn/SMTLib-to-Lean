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

The baseline launched on **2026-10-18 at 15:33 UTC (23:33 Hong Kong)** using unchanged inputs: 1,609 SMT files × Z3/cvc5 and 1,326 CHC files × Spacer/Eldarica, totaling **5,870 runs**. Each process gets a **300-second wall deadline**, including startup, a sampled-RSS limit of **4 GiB per solver group**, and a **16 MiB cap per stdout/stderr log**. Four workers share a Mac16,12 with 10 CPUs and 24 GiB RAM; the background run uses `nice 10`. These are shared-machine wall times, not dedicated CPU times.

Invocation from the repository root (the existing run is already active; use a new output directory for another run):

```sh
nice -n 10 python3 scripts/evaluate_solvers.py \
  --out evaluation/results/solvers-300s-2026-10-18 \
  --z3 /opt/homebrew/Cellar/z3/4.15.4/bin/z3 \
  --cvc5 /opt/homebrew/Caskroom/cvc5/1.3.2/cvc5-macOS-arm64-static/bin/cvc5 \
  --eldarica evaluation/tools/eldarica-2.3 \
  --timeout 300 --workers 4 --memory-mb 4096 --log-mb 16
```

The run directory `results/solvers-300s-2026-10-18/` contains the runner snapshot, `metadata.json` (timestamps, binary hashes, raw versions and exact commands), incremental `results.jsonl`/`results.csv`, `progress.json`, `summary.json`, `candidates.csv`, and raw `logs/`. Summaries report answer/error/timeout/memory/log-cap counts, solved percentages, successful-runtime median/p95/max, and disagreements. Distinct-input candidates require both solvers to time out or return `unknown`; errors and empty/queryless controls are excluded. Results are preliminary until `progress.json` reports `complete`; current progress is updated every five seconds. The launch does not establish that 50–100 candidates exist.

[smt2025]: https://zenodo.org/records/16887742/files/single_query.tar.gz?download=1
[tricera]: https://github.com/chc-comp/tricera-adt-arr/archive/0214c9fb4845013dc9ec5d1f8c4376efc6c6e365.zip
[chc2026]: https://github.com/chc-comp/chc-comp26-benchmarks/archive/b4fa7a708e5863bbcdb5de50d692ead3a67cbedc.zip
