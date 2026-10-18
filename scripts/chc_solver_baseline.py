#!/usr/bin/env python3
"""Run Spacer/Eldarica on the translated CHC corpus, preserving inputs and logs."""

import argparse
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
import csv
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import signal
import subprocess
import tarfile
import time

ROOT = Path(__file__).resolve().parents[1]
CORPUS = ROOT / "benchmarks/chc-smtlib"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inputs():
    """Use translation manifests for paths; check hashes against archived sources."""
    with (CORPUS / "manifest.csv").open() as stream:
        pins = defaultdict(list)
        for row in csv.DictReader(stream):
            pins[(Path(row["archive"]).name, row["sha256"])].append(row)
    cases = []
    suites = json.loads((CORPUS / "generated/summary.json").read_text())["suites"]
    for suite in suites:
        name = suite["suite"]
        manifest = "manifest.json" if name == "extra-small-lia" else f"{name}-manifest.json"
        data = json.loads((CORPUS / "generated" / manifest).read_text())
        with tarfile.open(CORPUS / "archives" / f"{name}.tar.gz") as archive:
            labels = {}
            for member in archive:
                if not member.name.endswith(".yml"):
                    continue
                text = archive.extractfile(member).read().decode()
                source = re.search(r"(?m)^input_files:\s*([^\n]+)$", text)
                verdict = re.search(r"expected_verdict:\s*(true|false)\b", text)
                if not source or not verdict:
                    continue
                filename = source[1].strip().strip("\"'")
                if not re.fullmatch(r"[^\s]+\.smt2", filename):
                    raise ValueError(f"Unsupported input_files label format: {member.name}")
                key = str(Path(member.name).parent / filename)
                label = "sat" if verdict[1] == "true" else "unsat"
                placeholder = "placeholder" in text.lower()
                labels[key] = dict(expected=None if placeholder else label,
                                   expected_source=None if placeholder else "CHC-COMP expected_verdict",
                                   declared_verdict=label, placeholder_verdict=placeholder,
                                   label_file=member.name)
            for entry in data["files"]:
                path = Path(data["input_root"]) / entry["input"]
                sha = digest(path)
                rows = [r for r in pins[(f"{name}.tar.gz", sha)]
                        if r["archive_member"].endswith("/" + entry["input"])]
                if len(rows) != 1:
                    raise ValueError(f"Input missing or changed from pinned corpus: {path}")
                label = labels.get(rows[0]["archive_member"], dict(expected=None,
                    expected_source=None, declared_verdict=None, placeholder_verdict=False, label_file=None))
                if label["expected"] is None and name == "hoice-regressions":
                    expected = next((p for p in Path(entry["input"]).parts[:-1]
                                     if p in ("sat", "unsat")), None)
                    label.update(expected=expected,
                                 expected_source="upstream sat/unsat directory" if expected else None)
                cases.append(dict(suite=name, input=entry["input"], path=str(path),
                                  sha256=sha, **label))
    return cases


def classify(stdout, stderr, code, timed_out):
    answers = re.findall(r"^(sat|unsat|unknown)\s*$", stdout, re.M)
    combined = stdout + "\n" + stderr
    if timed_out or re.search(r"(?im)^\s*(timeout|time limit exceeded)\s*$", combined):
        return "timeout"
    # Ignore ordinary warnings, but never count an answer following a rejected assertion.
    if re.search(r"(?im)^\s*(\(error\b|error\b|exception\b)", combined):
        return "error"
    if code != 0:
        return "error"
    return answers[0] if len(answers) == 1 else "error"


def run_one(case, solver, prefix, timeout, output):
    command = prefix + [case["path"]]
    stem = Path("logs") / solver / case["suite"] / case["input"]
    out_path = output / (str(stem) + ".stdout")
    err_path = output / (str(stem) + ".stderr")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    start = time.monotonic()
    timed_out = False
    with out_path.open("wb") as stdout, err_path.open("wb") as stderr:
        proc = subprocess.Popen(command, stdout=stdout, stderr=stderr, start_new_session=True)
        try:
            proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(proc.pid, signal.SIGKILL)
            proc.wait()
    elapsed = time.monotonic() - start
    stdout = out_path.read_text(errors="replace")
    stderr = err_path.read_text(errors="replace")
    status = classify(stdout, stderr, proc.returncode, timed_out)
    mismatch = status in ("sat", "unsat") and case["expected"] is not None and status != case["expected"]
    return dict(case, solver=solver, status=status, seconds=round(elapsed, 6),
                returncode=proc.returncode, expected_mismatch=mismatch, command=command,
                stdout=str(out_path.relative_to(output)), stderr=str(err_path.relative_to(output)))


def summarize(records):
    totals = {}
    suites = {}
    for solver in sorted({r["solver"] for r in records}):
        selected = [r for r in records if r["solver"] == solver]
        totals[solver] = dict(Counter(r["status"] for r in selected))
        totals[solver]["solved"] = sum(r["status"] in ("sat", "unsat") for r in selected)
        totals[solver]["expected_mismatches"] = sum(r["expected_mismatch"] for r in selected)
        for suite in sorted({r["suite"] for r in selected}):
            subset = [r for r in selected if r["suite"] == suite]
            suites.setdefault(suite, {})[solver] = dict(Counter(r["status"] for r in subset))
    paired = defaultdict(dict)
    for r in records:
        paired[(r["suite"], r["input"])][r["solver"]] = r["status"]
    conflicts = [dict(suite=k[0], input=k[1], answers=v) for k, v in paired.items()
                 if set(v.values()) == {"sat", "unsat"}]
    solved_any = sum(any(s in ("sat", "unsat") for s in v.values()) for v in paired.values())
    solved_both = sum(len(v) == 2 and all(s in ("sat", "unsat") for s in v.values())
                      for v in paired.values())
    return dict(totals=totals, suites=suites, solved_by_either=solved_any,
                solved_by_both=solved_both, disagreements=conflicts)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--z3", default="z3")
    parser.add_argument("--eldarica", required=True)
    parser.add_argument("--timeout", type=int, default=30)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.timeout < 1 or args.workers < 1:
        parser.error("timeout and workers must be positive")
    solvers = {"spacer": str(Path(shutil.which(args.z3) or args.z3).resolve()),
               "eldarica": str(Path(shutil.which(args.eldarica) or args.eldarica).resolve())}
    versions = {}
    for name, binary in solvers.items():
        versions[name] = subprocess.check_output(
            [binary, "--version" if name == "spacer" else "-h"],
            stderr=subprocess.STDOUT, timeout=15, text=True).splitlines()[0]
    cases = inputs()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    prefixes = {"spacer": [solvers["spacer"], "-smt2", "smt.logic=HORN", "fp.engine=spacer",
                            f"timeout={args.timeout * 1000}"],
                "eldarica": [solvers["eldarica"], "-horn", "-hsmt", f"-t:{args.timeout}"]}
    metadata = dict(started_utc=datetime.now(timezone.utc).isoformat(),
                    timeout_seconds=args.timeout, workers=args.workers, inputs=len(cases),
                    platform=platform.platform(), versions=versions, commands=prefixes,
                    solver_sha256={k: digest(Path(v)) for k, v in solvers.items()},
                    runner_sha256=digest(Path(__file__)),
                    timing="Process wall time including startup; concurrent runs; external hard deadline.",
                    inputs_note="Original inputs unchanged. smt.logic=HORN selects HORN for four inputs lacking set-logic.",
                    labels_note="Upstream expected verdicts are comparison labels, not independently checked proofs.")
    (output / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
    records = []
    start = time.monotonic()
    with (output / "results.jsonl").open("w") as stream, ThreadPoolExecutor(args.workers) as pool:
        jobs = [pool.submit(run_one, case, name, prefixes[name], args.timeout, output)
                for case in cases for name in solvers]
        for future in as_completed(jobs):
            result = future.result()
            records.append(result)
            stream.write(json.dumps(result) + "\n")
            stream.flush()
            if len(records) % 100 == 0 or len(records) == len(jobs):
                print(f"{len(records)}/{len(jobs)} runs; {time.monotonic()-start:.1f}s; "
                      f"{dict(Counter(r['status'] for r in records))}", flush=True)
    records.sort(key=lambda r: (r["suite"], r["input"], r["solver"]))
    fields = ["suite", "input", "solver", "status", "seconds", "expected", "expected_mismatch",
              "returncode", "sha256", "path", "stdout", "stderr"]
    with (output / "results.csv").open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fields, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(records)
    summary = summarize(records)
    summary["wall_seconds"] = round(time.monotonic() - start, 3)
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary["totals"], indent=2), flush=True)


if __name__ == "__main__":
    main()
