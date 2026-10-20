#!/usr/bin/env python3
"""Evaluate exactly one pinned archive; never advance automatically to another suite."""

import argparse
from collections import Counter
import csv
import hashlib
import importlib
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

if __package__:
    from . import solvers as processes, metrics
else:
    # Resume executes a copied worker beside its provenance, using frozen helpers.
    snapshot = None
    if "--resume-campaign" in sys.argv:
        campaign = Path(sys.argv[sys.argv.index("--resume-campaign") + 1]).resolve()
        metadata = json.loads((campaign / "metadata.json").read_text())
        os.environ["SMT2LEAN_PROJECT_ROOT"] = metadata["root"]
        snapshot = campaign / "snapshot"
        sys.path.insert(0, str(snapshot))
    legacy = snapshot is not None and (snapshot / "evaluate_translation.py").exists()
    processes = importlib.import_module("evaluate_solvers" if legacy else "solvers")
    metrics = importlib.import_module("evaluation_metrics" if legacy else "metrics")

ROOT = Path(os.environ.get("SMT2LEAN_PROJECT_ROOT", Path(__file__).resolve().parents[2])).resolve()
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
    for key in ("archive", "archive_member", "path", "solver", "answers", "timeout_method",
                "expected_mismatch"):
        result.pop(key, None)
    return result


def _check_case(case, args, out, generated, lean):
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
    if processes.STOP.is_set():
        return record
    try:
        record.update(metrics.measure(text, output, artifacts / "metrics", args.cloc))
        record["metrics_status"] = "passed"
    except Exception as exc:
        record["metrics_status"] = "error"
        record["metrics_error"] = repr(exc)
    return record


def failure_category(stage):
    """Keep resource failures separate from unsupported syntax and other errors."""
    reason, diagnostic = stage.get("limit_reason"), stage.get("diagnostic", "")
    if reason:
        return reason
    if "excessive memory consumption" in diagnostic:
        return "memory_limit"
    if "maximum recursion depth" in diagnostic:
        return "recursion_limit"
    if "heartbeats" in diagnostic:
        return "heartbeat_limit"
    if "expected at least one check-sat" in diagnostic:
        return "missing_check_sat"
    return stage["status"]


def check_case(case, args, out, generated, lean):
    record = _check_case(case, args, out, generated, lean)
    if processes.STOP.is_set():
        record["input_metrics_status"] = "not_run"
        return record
    # Static measurements stay outside timed subprocess stages and never alter
    # the benchmark outcome. Failed translations still get input measurements.
    try:
        text = Path(case["path"]).read_bytes().decode("utf-8")
        if "input_code_loc" not in record:
            record.update(metrics.measure_input(text, out / record["artifacts"] / "input-metrics", args.cloc))
        elif "input_structure" not in record:
            record["input_structure"] = metrics.input_structure(text)
        record["input_metrics_status"] = "passed"
    except Exception as exc:
        record.update(input_metrics_status="error", input_metrics_error=repr(exc))
    if record.get("generated") and "output_structure" not in record:
        try:
            record["output_structure"] = metrics.generated_structure(
                (ROOT / record["generated"]).read_bytes().decode("utf-8"))
        except Exception as exc:
            record.update(metrics_status="error", metrics_error=repr(exc))
    for stage in record["stages"].values():
        stage["failure_category"] = None if stage["status"] == "passed" else failure_category(stage)
    failure = next(((name, stage) for name, stage in record["stages"].items()
                    if stage["status"] != "passed"), None)
    record["failed_stage"] = failure[0] if failure else None
    record["failure_category"] = failure[1]["failure_category"] if failure else None
    record["measured_stage_seconds"] = sum(s["seconds"] for s in record["stages"].values())
    if record["translation_status"] == record["statements_status"] == "passed":
        record["translation_and_statements_seconds"] = record["translation_seconds"] + record["statements_seconds"]
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
    summary["input_metrics_errors"] = sum(r.get("input_metrics_status") == "error" for r in records)
    summary["failure_categories"] = dict(Counter(r["failure_category"] for r in records
                                                if r.get("failure_category")))
    summary["input_size_all_attempted"] = {
        name: processes.runtime([r[name] for r in records if name in r])
        for name in ("input_bytes", "input_code_loc", "input_tokens")}
    for field, population, names in (
        ("input_structure", records, ("max_parenthesis_depth", "quantifier_count", "let_count",
                                      "declaration_count", "bitvec_width_min", "bitvec_width_max")),
        ("output_structure", measured, ("declaration_count", "largest_declaration_tokens",
                                        "max_delimiter_depth", "binder_token_count", "let_count")),
    ):
        summary[field] = {name: processes.runtime([r[field][name] for r in population
            if r.get(field, {}).get(name) is not None]) for name in names}
    summary["translation_and_statements_seconds"] = processes.runtime(
        [r["translation_and_statements_seconds"] for r in passed if "translation_and_statements_seconds" in r])
    for stage in ("translation", "statements", "template"):
        stages = [r["stages"][stage] for r in records if stage in r["stages"]]
        summary[stage + "_sampled_peak_rss_kb"] = processes.runtime(
            [s["sampled_peak_rss_kb"] for s in stages if s.get("sampled_peak_rss_kb") is not None])
        summary[stage + "_all_attempt_seconds"] = processes.runtime([s["seconds"] for s in stages])
        summary[stage + "_failed_attempt_seconds_total"] = sum(
            s["seconds"] for s in stages if s["status"] != "passed")
    summary["total_token_ratio"] = (sum(r["output_tokens"] for r in measured) /
                                    sum(r["input_tokens"] for r in measured)
                                    if sum(r["input_tokens"] for r in measured) else None)
    groups = {}
    for r in records:
        groups.setdefault(r["sha256"], []).append(r)
    summary["distinct_content_outcomes"] = dict(Counter(
        "mixed" if len({r["outcome"] for r in rows}) > 1 else rows[0]["outcome"]
        for rows in groups.values()))
    for field in ("suite", "logic"):
        groups = {}
        for r in records:
            groups.setdefault(str(r.get(field)), []).append(r)
        summary["by_" + field] = {key: dict(total=len(rows),
            passed=sum(r["outcome"] == "passed" for r in rows),
            controls=sum(r.get("control", False) for r in rows),
            distinct_contents=len({r["sha256"] for r in rows}),
            outcomes=dict(Counter(r["outcome"] for r in rows))) for key, rows in groups.items()}
    return summary



digest = processes.digest
CSV_FIELDS = [
    "suite", "archive", "archive_member", "source_path", "sha256", "generated",
    "outcome", "translation_status", "statements_status", "template_status",
    "metrics_status", "query_count", "emitted_queries", "control",
    "translation_seconds", "statements_seconds", "template_seconds",
    "input_bytes", "output_bytes", "output_statement_bytes",
    "input_code_loc", "output_code_loc", "input_tokens", "output_tokens",
    "code_loc_ratio", "token_ratio", "byte_ratio", "statement_byte_ratio",
    "artifacts", "input_metrics_status", "failed_stage", "failure_category",
    "translation_and_statements_seconds", "measured_stage_seconds",
]

def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def read_records(directory, cases, generated, runner, audit):
    """Only already-auditable records, including expected failures, may be retained."""
    expected = {(case["archive"], case["archive_member"]): case for case in cases}
    require(len(expected) == len(cases), "Duplicate input identities")
    data = (directory / "results.jsonl").read_bytes()
    require(not data or data.endswith(b"\n"), "Reconcile truncated results before resuming")
    records, seen = [], set()
    for line in data.splitlines():
        record = json.loads(line)
        key = audit.validate_record(record, expected, generated, runner, directory)
        require(key not in seen, "Duplicate retained record: " + str(key))
        seen.add(key)
        records.append(record)
    return records, expected, seen


def rebase_record(record, attempt, directory, runner):
    """The frozen runner emits paths relative to its private attempt directory."""
    def relative(name):
        return str(runner.processes.safe_path(attempt, name).relative_to(directory))
    if record.get("artifacts"):
        record["artifacts"] = relative(record["artifacts"])
    for stage in record.get("stages", {}).values():
        for channel in ("stdout", "stderr"):
            if channel in stage:
                stage[channel] = relative(stage[channel])
    return record


def write_csv(directory, records):
    temporary = directory / "results.csv.tmp"
    with temporary.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, CSV_FIELDS, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(records)
    temporary.replace(directory / "results.csv")


def error_record(case, exc):
    """Keep a failed attempt discoverable even when check_case raises before returning."""
    identity = hashlib.sha256(case["archive_member"].encode()).hexdigest()[:20]
    return dict(case, artifacts="cases/" + identity, stages={}, outcome="runner_error",
                translation_status="not_run", statements_status="not_run",
                template_status="not_run", metrics_status="not_run",
                input_metrics_status="error", reason=repr(exc))


def run_archive(directory, attempt, args, cases, records, expected, seen, runner, audit, lean):
    processes = runner.processes
    current, monitor_errors = {}, []
    finished, progress_lock = threading.Event(), threading.Lock()
    start = time.monotonic()

    def progress(state):
        with progress_lock:
            processes.atomic_json(directory / "progress.json", dict(
                updated_utc=processes.utc(), state=state, pid=os.getpid(),
                completed=len(records), total=len(cases), current=current,
                complete_archive=state == "complete",
                wall_seconds=round(time.monotonic() - start, 3),
                outcomes=dict(Counter(row["outcome"] for row in records))))

    def monitor():
        while not finished.wait(1):
            try:
                processes.sample_memory(args.memory_mb)
                progress("running")
            except Exception as exc:
                monitor_errors.append(repr(exc))
                processes.STOP.set()
                return

    handlers = {}
    for sig in (signal.SIGINT, signal.SIGTERM):
        handlers[sig] = signal.signal(sig, lambda *_: processes.STOP.set())
    worker = threading.Thread(target=monitor, daemon=True)
    worker.start()
    state = "failed"
    try:
        progress("running")
        write_csv(directory, records)
        processes.atomic_json(directory / "summary.json", runner.summarize(records))
        with (directory / "results.jsonl").open("a") as stream, \
                (directory / "results.csv").open("a", newline="") as csvfile:
            writer = csv.DictWriter(csvfile, CSV_FIELDS, extrasaction="ignore")
            for case in cases:
                key = (case["archive"], case["archive_member"])
                if key in seen:
                    continue
                if processes.STOP.is_set():
                    break
                current = dict(source_path=case["source_path"], started_utc=processes.utc())
                destination = processes.safe_path(args.generated, case["output_relative"])
                require(not destination.exists(), "Unreconciled generated output: " + str(destination))
                try:
                    record = runner.check_case(case, args, attempt, args.generated, lean)
                except Exception as exc:
                    record = error_record(case, exc)
                rebase_record(record, attempt, directory, runner)
                # Persist invalid/interrupted attempts as well; a later reconciliation
                # must inspect and back them up instead of silently losing the attempt.
                stream.write(json.dumps(record) + "\n")
                stream.flush()
                os.fsync(stream.fileno())
                records.append(record)
                writer.writerow(record)
                csvfile.flush()
                processes.atomic_json(directory / "summary.json", runner.summarize(records))
                print(f'{len(records)}/{len(cases)} {record["outcome"]} {case["source_path"]}',
                      flush=True)
                audit.validate_record(record, expected, args.generated, runner, directory)
                seen.add(key)
            require(not monitor_errors, "; ".join(monitor_errors))
            state = ("complete" if len(seen) == len(cases) and not processes.STOP.is_set()
                     else "interrupted")
    except Exception as exc:
        state = "interrupted" if processes.STOP.is_set() else "failed"
        processes.atomic_json(directory / "failure.json", dict(
            error=repr(exc), current=current, utc=processes.utc()))
        print(repr(exc), file=sys.stderr, flush=True)
    finally:
        finished.set()
        worker.join(timeout=5)
        for sig, handler in handlers.items():
            signal.signal(sig, handler)
        if monitor_errors:
            state = "failed"
            processes.atomic_json(directory / "failure.json", dict(
                error="; ".join(monitor_errors), current=current, utc=processes.utc()))
        write_csv(directory, records)
        processes.atomic_json(directory / "summary.json", runner.summarize(records))
        progress(state)
    return 0 if state == "complete" else 1



def resume_archive_main(argv):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--resume-campaign", dest="campaign", required=True, type=Path)
    parser.add_argument("--archive", required=True)
    parser.add_argument("--session", required=True)
    options = parser.parse_args(argv)
    require(re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_.-]*", options.session),
            "Session must be a single safe filename component")
    campaign = options.campaign.resolve()
    metadata = json.loads((campaign / "metadata.json").read_text())
    require(options.archive in dict(metadata["schedule"]), "Archive is not in campaign schedule")
    root = Path(metadata["root"]).resolve()
    os.environ["SMT2LEAN_PROJECT_ROOT"] = str(root)
    os.chdir(root)
    snapshot = campaign / "snapshot"
    legacy = (snapshot / "evaluate_translation.py").exists()
    names = (("evaluate_translation", "evaluation_metrics", "evaluate_solvers", "evaluation_campaign")
             if legacy else ("translation", "metrics", "solvers", "campaign"))
    hashes = {}
    for name in names:
        path = snapshot / (name + ".py")
        hashes[path.name] = digest(path)
        require(hashes[path.name] == metadata["pins"].get(str(path)),
                "Pinned runner changed: " + str(path))
    sys.path.insert(0, str(snapshot))
    runner = importlib.import_module(names[0])
    audit = importlib.import_module(names[3])
    for name in names:
        require(Path(sys.modules[name].__file__).resolve() == snapshot / (name + ".py"),
                "Failed to import pinned runner: " + name)
    label = options.archive.removesuffix(".tar.gz")
    directory = campaign / "archives" / label
    original = audit.read_json(directory / "metadata.json")
    args = SimpleNamespace(**original["arguments"])
    args.out, args.generated, args.translator = (
        Path(args.out).resolve(), Path(args.generated).resolve(), Path(args.translator).resolve())
    require(args.archive == options.archive and args.out == directory and
            args.generated == Path(metadata["arguments"]["generated"]).resolve() / label and
            args.translator == snapshot / "smt2lean", "Original archive paths differ")
    require(original["workers"] == 1 and original["check_equivalence"] is False and
            args.timeout == 300 and args.memory_mb == 4096 and args.max_rec_depth == 4096 and
            args.limit is None and original["complete_archive"], "Original archive policy differs")
    require(original["working_directory"] == str(root), "Original working directory differs")
    require(os.environ.get("LEAN_PATH") == original["lean_path"] and original["lean_path"],
            "Launch in the original pinned LEAN_PATH environment")
    require(not (directory / "failure.json").exists(), "Reconcile failure.json before resuming")
    require(args.generated.is_dir(), "Original generated directory is missing")
    for name in audit.RUNNERS:
        require(original["runner_hashes"][name] == hashes[name], "Archive runner hashes differ")
    runner.EXE = args.translator
    lean = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip()) / "bin/lean"
    for tool, pin in ((args.translator, "translator_sha256"),
                      (lean, "lean_sha256"), (Path(args.cloc).resolve(), "cloc_sha256")):
        require(digest(tool) == original[pin] == metadata["pins"].get(str(tool)),
                "Original tool pin differs: " + str(tool))
    cases = audit.read_json(directory / "inputs.json")
    require(len(cases) == original["total"] == dict(metadata["schedule"])[options.archive] and
            all(case["archive"] == "smt-queries/" + options.archive for case in cases),
            "Original input manifest coverage differs")
    require(len({case["output_relative"].lower() for case in cases}) == len(cases),
            "Generated filename collision")
    records, expected, seen = read_records(directory, cases, args.generated, runner, audit)
    for case in cases:
        destination = runner.processes.safe_path(args.generated, case["output_relative"])
        require((case["archive"], case["archive_member"]) in seen or not destination.exists(),
                "Reconcile generated output before resuming: " + str(destination))
    attempt = directory / "attempts" / options.session
    provenance = attempt.with_suffix(attempt.suffix + ".json")
    require(not provenance.exists(), "Resume session provenance already exists")
    attempt.mkdir(parents=True)
    audit.atomic_json(provenance, dict(
        session=options.session, started_utc=audit.utc(), pid=os.getpid(),
        archive=options.archive, campaign=str(campaign), attempt_directory=str(attempt),
        worker=str(Path(__file__).resolve()), worker_sha256=digest(__file__),
        pinned_runner_hashes=hashes, retained_count=len(records), total=len(cases),
        arguments=original["arguments"], original_metadata_sha256=digest(directory / "metadata.json"),
        original_results_sha256=digest(directory / "results.jsonl")))
    (directory / "runner.pid").write_text(str(os.getpid()) + "\n")
    return run_archive(directory, attempt, args, cases, records, expected, seen, runner, audit, lean)


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    if "--resume-campaign" in argv:
        return resume_archive_main(argv)
    global EXE
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", required=True, help="One filename, e.g. smtcomp-2025-QF_UFLIA.tar.gz")
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--generated", type=Path, required=True)
    parser.add_argument("--timeout", type=float, default=300)
    parser.add_argument("--memory-mb", type=int, default=4096)
    parser.add_argument("--max-rec-depth", type=int, default=4096)
    parser.add_argument("--cloc", default=shutil.which("cloc"))
    parser.add_argument("--translator", type=Path, default=EXE,
                        help="Pinned translator executable; does not rebuild it")
    parser.add_argument("--limit", type=int, help="Smoke run only; metadata marks this incomplete archive")
    args = parser.parse_args(argv)
    EXE = args.translator.resolve()
    if min(args.timeout, args.memory_mb, args.max_rec_depth,
           args.limit if args.limit is not None else 1) <= 0 or not args.cloc:
        parser.error("Positive limits and an installed cloc are required")
    if not os.environ.get("LEAN_PATH"):
        parser.error("Launch with lake env python3 scripts/evaluate.py translate so pinned dependencies are available")
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
        lean_path=os.environ.get("LEAN_PATH"), check_equivalence=False,
        size_population="Ratios/summaries use fully typechecked inputs; raw metrics retained for all translated files.")
    code = [ROOT / "Main.lean", ROOT / "Smt2Lean.lean", *sorted((ROOT / "Smt2Lean").rglob("*.lean")),
            ROOT / "lean-toolchain", ROOT / "lakefile.toml", ROOT / "lake-manifest.json"]
    metadata["source_hashes"] = {str(p.relative_to(ROOT)): processes.digest(p) for p in code}
    for name in ("translation.py", "metrics.py", "solvers.py", "campaign.py"):
        shutil.copyfile(Path(__file__).resolve().parent / name, args.out / name)
    metadata["runner_hashes"] = {p.name: processes.digest(p) for p in args.out.glob("*.py")}
    processes.atomic_json(args.out / "metadata.json", metadata)
    processes.atomic_json(args.out / "inputs.json", cases)
    (args.out / "runner.pid").write_text(str(os.getpid()) + "\n")
    audit = importlib.import_module((__package__ + ".campaign") if __package__ else "campaign")
    expected = {(case["archive"], case["archive_member"]): case for case in cases}
    return run_archive(args.out, args.out, args, cases, [], expected, set(),
                       sys.modules[__name__], audit, lean)


if __name__ == "__main__":
    sys.exit(main())
