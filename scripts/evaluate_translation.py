#!/usr/bin/env python3
"""Evaluate exactly one pinned archive; never advance automatically to another suite."""

import argparse
from collections import Counter
import csv
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import tarfile
import threading
import time
from types import SimpleNamespace

import evaluate_solvers as processes
import evaluation_metrics as metrics

ROOT = Path(__file__).resolve().parents[1]
CORPUS = ROOT / "evaluation"
EXE = ROOT / ".lake/build/bin/smt2lean"


def prepare(archive_name):
    """Check only the selected archive and its complete manifest, preserving source bytes."""
    archive_key = "smt-queries/" + archive_name
    sources = json.loads((CORPUS / "sources.json").read_text())
    entries = [a for a in sources["archives"] if a["archive"] == archive_key]
    if len(entries) != 1:
        raise ValueError("Select an archive filename from evaluation/smt-queries")
    entry = entries[0]
    pins = dict((line.split(None, 1)[1], line.split(None, 1)[0])
                for line in (CORPUS / "SHA256SUMS").read_text().splitlines() if line.strip())
    archive = processes.safe_path(CORPUS, archive_key)
    if processes.digest(archive) != entry["sha256"] or pins[archive_key] != entry["sha256"]:
        raise ValueError("Archive hash mismatch")
    with (CORPUS / "inputs.csv").open(newline="") as stream:
        rows = [r for r in csv.DictReader(stream) if r["archive"] == archive_key]
    if len(rows) != entry["files"] or len({r["archive_member"] for r in rows}) != len(rows):
        raise ValueError("Archive/manifest count mismatch or duplicate paths")
    extraction = CORPUS / "extracted" / archive_name.removesuffix(".tar.gz")
    seen, inputs = set(), set()
    with tarfile.open(archive, "r:gz") as stream:
        for member in stream:
            dest = processes.safe_path(extraction, member.name)
            if member.name in seen or not (member.isfile() or member.isdir()):
                raise ValueError("Duplicate or nonregular archive member: " + member.name)
            seen.add(member.name)
            if member.isdir():
                continue
            if member.name.endswith(".smt2"):
                inputs.add(member.name)
            data = stream.extractfile(member).read()
            if dest.exists():
                if dest.read_bytes() != data:
                    raise ValueError("Existing extraction differs: " + str(dest))
            else:
                dest.parent.mkdir(parents=True, exist_ok=True)
                dest.write_bytes(data)
    if inputs != {r["archive_member"] for r in rows}:
        raise ValueError("Manifest does not enumerate every SMT-LIB file in the archive")
    for row in rows:
        path = processes.safe_path(extraction, row["archive_member"])
        if path.stat().st_size != int(row["bytes"]) or processes.digest(path) != row["sha256"]:
            raise ValueError("Input hash/size mismatch: " + str(path))
        row["path"] = str(path)
    return entry, sorted(rows, key=lambda r: r["archive_member"])


def stage_status(result, translation=False):
    """Classify process completion, without applying the solver-answer classifier."""
    reason = result["limit_reason"]
    if reason == "wall_timeout":
        return "timeout"
    if reason:
        return reason
    if result["returncode"] == 0:
        return "passed"
    if translation and 'cvc5.Error.unsupported' in result.get("diagnostic", ""):
        return "unsupported"
    return "error"


def run_stage(command, name, case, args, out):
    # Reuse the tested process-group cleanup, log caps and RSS monitoring. The
    # solver wrapper appends `path`; use it for this command's final argument.
    job = dict(archive=case["archive"], archive_member=case["archive_member"], path=command[-1])
    result = processes.run_one(job, name, command[:-1],
                               SimpleNamespace(timeout=args.timeout, log_mb=16), out)
    result["diagnostic"] = "\n".join((out / result[k]).read_text(errors="replace")
                                       for k in ("stdout", "stderr"))
    result["status"] = stage_status(result, name == "translation")
    result["warning_count"] = len(re.findall(r"(?m)^.*\bwarning:", result["diagnostic"]))
    result["sorry_warnings"] = len(re.findall(r"declaration uses [`']sorry[`']", result["diagnostic"]))
    result["diagnostic"] = result["diagnostic"][:4000]
    for key in ("archive", "archive_member", "path", "solver", "answers", "timeout_method"):
        result.pop(key, None)
    return result


def check_case(case, args, out, generated, lean):
    record = dict(case, stages={}, outcome="not_run", translation_status="not_run",
                  statements_status="not_run", template_status="not_run", metrics_status="not_run")
    identity = hashlib.sha256(case["archive_member"].encode()).hexdigest()[:20]
    artifacts = out / "cases" / identity
    artifacts.mkdir(parents=True)
    record["artifacts"] = str(artifacts.relative_to(out))
    source = Path(case["path"])
    if processes.digest(source) != case["sha256"]:
        raise ValueError("Input changed during evaluation: " + str(source))
    text = source.read_bytes().decode("utf-8")
    record["input_bytes"] = source.stat().st_size
    try:
        record.update(metrics.source_info(text))
    except metrics.LexicalError as exc:
        record.update(outcome="input_inspection_error", reason=str(exc))
        return record
    record["control"] = record["query_count"] == 0 or record["constraint_count"] == 0
    temporary = artifacts / "translation"
    translated = run_stage([str(EXE), str(source), "--out", str(temporary),
                            "--max-rec-depth", str(args.max_rec_depth)], "translation", case, args, out)
    record["stages"]["translation"] = translated
    record["translation_status"] = translated["status"]
    record["translation_seconds"] = translated["seconds"]
    if translated["status"] != "passed":
        record["outcome"] = "translation_" + translated["status"]
        return record
    query = temporary / "Query.lean"
    if not query.is_file():
        record["outcome"] = "output_error"
        record["reason"] = "Successful translator produced no Query.lean"
        return record
    destination = processes.safe_path(generated, case["output_relative"])
    destination.parent.mkdir(parents=True, exist_ok=True)
    query.rename(destination)
    temporary.rmdir()
    record["generated"] = os.path.relpath(destination, ROOT)
    record["output_sha256"] = processes.digest(destination)
    output = destination.read_bytes().decode("utf-8")
    record["output_bytes"] = destination.stat().st_size
    try:
        statements, _ = metrics.split_generated_source(output)
    except metrics.LexicalError as exc:
        record.update(outcome="output_inspection_error", reason=str(exc))
        return record
    # These exact generated goal names distinguish complete queries from helpers.
    record["emitted_queries"] = len(re.findall(
        r"(?m)^(?:noncomputable )?def (?:Refutation|Problem|Model|Safe)(?:_\d+)? : Prop\s*:=", statements))
    standalone = artifacts / "Statements.lean"
    standalone.write_text(statements)
    for name, path, extra in (("statements", standalone, ["--error=hasSorry"]),
                              ("template", destination, [])):
        checked = run_stage([str(lean), "-j1", "-M", str(args.memory_mb), *extra, str(path)],
                            name, case, args, out)
        record["stages"][name] = checked
        record[name + "_status"] = checked["status"]
        record[name + "_seconds"] = checked["seconds"]
        if processes.STOP.is_set():
            break
    record["outcome"] = ("passed" if record["emitted_queries"] == record["query_count"]
                         else "query_count_mismatch")
    for name in ("statements", "template"):
        if record[name + "_status"] != "passed":
            record["outcome"] = name + "_" + record[name + "_status"]
            break
    try:
        record.update(metrics.measure(text, output, artifacts / "metrics", args.cloc))
        record["metrics_status"] = "passed"
    except Exception as exc:
        record["metrics_status"] = "error"
        record["metrics_error"] = repr(exc)
    return record


def summarize(records):
    passed = [r for r in records if r["outcome"] == "passed"]
    substantive = [r for r in records if not r.get("control", True)]
    summary = dict(completed=len(records), passed=len(passed),
        outcomes=dict(Counter(r["outcome"] for r in records)),
        substantive_inputs=len(substantive), substantive_passed=sum(r["outcome"] == "passed" for r in substantive),
        controls=sum(r.get("control", False) for r in records),
        distinct_contents=len({r["sha256"] for r in records}),
        metrics_errors=sum(r["metrics_status"] == "error" for r in records))
    for stage in ("translation", "statements", "template"):
        summary[stage + "_outcomes"] = dict(Counter(r[stage + "_status"] for r in records))
        summary[stage + "_successful_seconds"] = processes.runtime(
            [r[stage + "_seconds"] for r in records if r[stage + "_status"] == "passed"])
    measured = [r for r in passed if r["metrics_status"] == "passed"]
    summary["size_metrics_passed_inputs"] = len(measured)
    for name in ("input_bytes", "output_bytes", "output_statement_bytes", "input_code_loc",
                 "output_code_loc", "input_tokens", "output_tokens", "code_loc_ratio", "token_ratio",
                 "byte_ratio", "statement_byte_ratio"):
        values = [r[name] for r in measured if r.get(name) is not None]
        summary[name] = processes.runtime(values)
        if name.endswith(("bytes", "loc", "tokens")):
            summary[name]["total"] = sum(values)
    summary["largest_expansions"] = [dict(source_path=r["source_path"], generated=r["generated"],
        token_ratio=r["token_ratio"], code_loc_ratio=r["code_loc_ratio"], byte_ratio=r["byte_ratio"])
        for r in sorted(measured, key=lambda r: r["token_ratio"] or 0, reverse=True)[:10]]
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", required=True, help="One filename, e.g. smtcomp-2025-QF_UFLIA.tar.gz")
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--generated", type=Path, required=True)
    parser.add_argument("--timeout", type=float, default=300)
    parser.add_argument("--memory-mb", type=int, default=4096)
    parser.add_argument("--max-rec-depth", type=int, default=4096)
    parser.add_argument("--cloc", default=shutil.which("cloc"))
    parser.add_argument("--limit", type=int, help="Smoke run only; metadata marks this incomplete archive")
    args = parser.parse_args()
    if min(args.timeout, args.memory_mb, args.max_rec_depth,
           args.limit if args.limit is not None else 1) <= 0 or not args.cloc:
        parser.error("Positive limits and an installed cloc are required")
    if not os.environ.get("LEAN_PATH"):
        parser.error("Launch with lake env python3 scripts/evaluate_translation.py so pinned dependencies are available")
    os.chdir(ROOT)
    args.out, args.generated = args.out.resolve(), args.generated.resolve()
    if args.out.exists() or args.generated.exists():
        parser.error("Output directories must be new; refusing to overwrite a run")
    entry, cases = prepare(args.archive)
    parent = Path(os.path.commonpath([str(Path(c["archive_member"]).parent) for c in cases]))
    for case in cases:
        case["output_relative"] = str(Path(case["archive_member"]).relative_to(parent).with_suffix(".lean"))
    if len({c["output_relative"].lower() for c in cases}) != len(cases):
        parser.error("Generated filename collision")
    if args.limit:
        cases = cases[:args.limit]
    args.out.mkdir(parents=True)
    args.generated.mkdir(parents=True)
    lean = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip()) / "bin/lean"
    def output(command):
        return subprocess.check_output(command, text=True).strip()
    metadata = dict(started_utc=processes.utc(), pid=os.getpid(), archive=entry, total=len(cases),
        complete_archive=not args.limit, arguments={k: str(v) if isinstance(v, Path) else v for k, v in vars(args).items()},
        workers=1, working_directory=str(ROOT), python=sys.version, git_commit=output(["git", "rev-parse", "HEAD"]),
        git_status=output(["git", "status", "--short"]),
        lean_version=output([str(lean), "--version"]), lean_sha256=processes.digest(lean),
        translator_sha256=processes.digest(EXE), cloc_version=output([args.cloc, "--version"]),
        cloc_sha256=processes.digest(Path(args.cloc).resolve()),
        timing="Shared-machine wall time per subprocess; includes startup, polling and process cleanup; excludes build and metrics.",
        memory=f"{args.memory_mb} MiB process-group RSS sampled once per second; Lean also receives -M; no peak claim for unsampled short jobs.",
        lean_path=os.environ.get("LEAN_PATH"), solver_run="solvers-300s-2026-10-18-fresh",
        size_population="Ratios/summaries use fully typechecked inputs; raw metrics retained for all translated files.")
    code = [ROOT / "Main.lean", ROOT / "Smt2Lean.lean", *sorted((ROOT / "Smt2Lean").rglob("*.lean")),
            ROOT / "lean-toolchain", ROOT / "lakefile.toml", ROOT / "lake-manifest.json"]
    metadata["source_hashes"] = {str(p.relative_to(ROOT)): processes.digest(p) for p in code}
    for name in ("evaluate_translation.py", "evaluation_metrics.py", "evaluate_solvers.py"):
        shutil.copyfile(ROOT / "scripts" / name, args.out / name)
    metadata["runner_hashes"] = {p.name: processes.digest(p) for p in args.out.glob("*.py")}
    processes.atomic_json(args.out / "metadata.json", metadata)
    processes.atomic_json(args.out / "inputs.json", cases)
    (args.out / "runner.pid").write_text(str(os.getpid()) + "\n")
    records, monitor_errors, current = [], [], {}
    progress_lock = threading.Lock()
    start = time.monotonic()
    def progress(state):
        with progress_lock:
            processes.atomic_json(args.out / "progress.json", dict(updated_utc=processes.utc(), state=state,
                pid=os.getpid(), completed=len(records), total=len(cases), current=current,
                wall_seconds=round(time.monotonic()-start, 3), outcomes=dict(Counter(r["outcome"] for r in records))))
    finished = threading.Event()
    def monitor():
        while not finished.wait(1):
            try:
                processes.sample_memory(args.memory_mb)
                progress("running")
            except Exception as exc:
                monitor_errors.append(repr(exc))
                processes.STOP.set()
                return
    for sig in (signal.SIGINT, signal.SIGTERM):
        signal.signal(sig, lambda *_: processes.STOP.set())
    worker = threading.Thread(target=monitor, daemon=True)
    worker.start()
    state = "failed"
    fields = ["suite", "source_path", "sha256", "generated", "outcome", "translation_status", "statements_status",
              "template_status", "metrics_status", "query_count", "emitted_queries", "control", "translation_seconds",
              "statements_seconds", "template_seconds", "input_bytes", "output_bytes", "output_statement_bytes",
              "input_code_loc", "output_code_loc", "input_tokens", "output_tokens", "code_loc_ratio", "token_ratio",
              "byte_ratio", "statement_byte_ratio", "artifacts"]
    try:
        progress("running")
        with (args.out / "results.jsonl").open("w") as stream, (args.out / "results.csv").open("w", newline="") as csvfile:
            writer = csv.DictWriter(csvfile, fields, extrasaction="ignore")
            writer.writeheader()
            csvfile.flush()
            for case in cases:
                if processes.STOP.is_set():
                    break
                current = dict(source_path=case["source_path"], started_utc=processes.utc())
                record = check_case(case, args, args.out, args.generated, lean)
                records.append(record)
                stream.write(json.dumps(record) + "\n")
                stream.flush()
                writer.writerow(record)
                csvfile.flush()
                processes.atomic_json(args.out / "summary.json", summarize(records))
                print(f'{len(records)}/{len(cases)} {record["outcome"]} {case["source_path"]}', flush=True)
            state = "complete" if len(records) == len(cases) and not processes.STOP.is_set() else "interrupted"
            if monitor_errors:
                raise RuntimeError("; ".join(monitor_errors))
    except Exception as exc:
        processes.atomic_json(args.out / "failure.json", dict(error=repr(exc), current=current, utc=processes.utc()))
        state = "failed"
        raise
    finally:
        finished.set()
        worker.join(timeout=5)
        processes.atomic_json(args.out / "summary.json", summarize(records))
        progress(state)
    return 0 if state == "complete" else 1


if __name__ == "__main__":
    sys.exit(main())
