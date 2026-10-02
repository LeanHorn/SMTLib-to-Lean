#!/usr/bin/env python3
"""Run a fixed selection through smt2lean and Lean; no solving or proof claims."""

import argparse
from collections import Counter
import csv
from datetime import datetime, timezone
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import re
import resource
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / ".lake/build/bin/smt2lean"
MIB = 1024 * 1024
FIELDS = [
    "id", "path", "source", "category", "kind", "logic", "sha256", "input_bytes",
    "input_queries", "emitted_queries", "outcome", "translation_status",
    "statements_status", "template_status", "statements_warnings", "template_warnings",
    "template_admissions", "translation_seconds",
    "statements_seconds", "template_seconds", "total_seconds", "output_bytes",
    "proof_status", "reason", "artifacts",
]


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def write_json(path, value):
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)


def select_inputs(paths, lists, root=None):
    """Directories recurse over .smt2; explicit missing files remain reportable."""
    entries = {}

    def add(path, metadata):
        path = path.resolve()
        if path.is_dir():
            candidates = sorted(path.rglob("*.smt2"))
            if not candidates:
                raise ValueError(f"No .smt2 files in {path}")
            for candidate in candidates:
                add(candidate, metadata)
            return
        record = entries.setdefault(str(path), {"path": str(path), "selection": {}})
        for key, value in metadata.items():
            if key == "path" or not value:
                continue
            previous = record["selection"].get(key)
            if previous and previous != value:
                raise ValueError(f"Conflicting {key} for {path}")
            record["selection"][key] = value

    for path in paths:
        add(Path(path), {})
    for listing in lists:
        listing = Path(listing).resolve()
        base = root or listing.parent
        with listing.open(newline="") as stream:
            if listing.suffix == ".csv":
                reader = csv.DictReader(stream)
                if "path" not in (reader.fieldnames or []):
                    raise ValueError(f"CSV needs a path column: {listing}")
                for row in reader:
                    if not row.get("path") or None in row:
                        raise ValueError(f"Invalid CSV row in {listing}: {row}")
                    add(base / row["path"], row)
            else:
                for line in stream:
                    line = line.strip()
                    if line and not line.startswith("#"):
                        add(base / line, {})
    if not entries:
        raise ValueError("Select at least one input file or directory")
    return list(entries.values())


def source_info(text):
    """Count top-level checks, ignoring comments/strings/quoted symbols; no validation."""
    tokens = re.finditer(r';[^\n]*|"(?:[^\"]|\"\")*"|\|[^|]*\||[()]|[^\s();"|]+', text)
    depth, header, queries, logics = 0, [], 0, []
    for match in tokens:
        token = match.group()
        if token.startswith(";"):
            continue
        if token == "(":
            if depth == 0:
                header = []
            depth += 1
        elif token == ")":
            if depth == 1 and header:
                queries += header[0] in ("check-sat", "check-sat-assuming")
                if header[0] == "set-logic" and len(header) > 1:
                    logics.append(header[1])
            depth -= 1
        elif depth == 1 and len(header) < 2:
            header.append(token)
    unique = list(dict.fromkeys(logics))
    kind = "CHC" if unique == ["HORN"] else "mixed" if "HORN" in unique else "SMT"
    return {"input_queries": queries, "logic": ";".join(unique), "kind": kind}


def diagnostic(path):
    # Keep the full bounded log on disk, and a short diagnostic in the table.
    with path.open("rb") as stream:
        message = stream.read(4096).decode("utf-8", errors="replace")
    return message.strip()


def run_process(command, directory, label, timeout, file_limit, *, cwd, env):
    stdout = directory / f"{label}.stdout.log"
    stderr = directory / f"{label}.stderr.log"
    started = time.perf_counter()
    result = {"command": list(map(str, command)), "cwd": str(cwd),
              "stdout": stdout.name, "stderr": stderr.name, "exit_code": None}

    def limits():
        resource.setrlimit(resource.RLIMIT_FSIZE, (file_limit, file_limit))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

    with stdout.open("wb") as out, stderr.open("wb") as err:
        try:
            child = subprocess.Popen(result["command"], cwd=cwd, env=env,
                                     stdout=out, stderr=err, start_new_session=True,
                                     preexec_fn=limits)
        except (OSError, subprocess.SubprocessError) as error:
            result.update(status="launch_error", reason=str(error))
        else:
            try:
                code = child.wait(timeout=timeout)
                result["exit_code"] = code
                result["status"] = ("passed" if code == 0 else
                                    "resource_limit" if code == -signal.SIGXFSZ else
                                    "crash" if code < 0 else "error")
            except (subprocess.TimeoutExpired, KeyboardInterrupt) as error:
                try:
                    os.killpg(child.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                result["exit_code"] = child.wait()
                result["status"] = "timeout" if isinstance(error, subprocess.TimeoutExpired) else "interrupted"
    result["seconds"] = round(time.perf_counter() - started, 6)
    if result["status"] != "passed":
        result.setdefault("reason", diagnostic(stderr) or diagnostic(stdout) or result["status"])
    return result


def check_case(record, directory, args, lean, env):
    """Always leave the source snapshot and stage logs beside generated output."""
    path = Path(record["path"])
    record["input_bytes"] = path.stat().st_size
    if record["input_bytes"] > args.max_input_mib * MIB:
        record.update(outcome="input_limit", reason="Input exceeds --max-input-mib")
        return
    data = path.read_bytes()
    record.update(input_bytes=len(data), sha256=sha256(data))
    if len(data) > args.max_input_mib * MIB:
        record.update(outcome="input_limit", reason="Input grew beyond --max-input-mib")
        return
    expected = record["selection"].get("sha256")
    if expected and expected != record["sha256"]:
        record.update(outcome="hash_mismatch", reason=f"Expected SHA-256 {expected}")
        return
    source = directory / "Input.smt2"
    source.write_bytes(data)
    record.update(source_info(data.decode("utf-8")))
    generated = directory / "generated"

    def stage(label, command, *, checking=False):
        result = run_process(command, directory, label,
                             args.lean_timeout if checking else args.translation_timeout,
                             args.max_file_mib * MIB, cwd=generated if checking else ROOT, env=env)
        if checking:
            warnings, admissions, first_error = Counter(), 0, None
            with (directory / result["stdout"]).open(errors="replace") as stream:
                for line in stream:
                    try:
                        message = json.loads(line)
                    except json.JSONDecodeError:
                        continue
                    if not isinstance(message, dict):
                        continue
                    if message.get("severity") == "warning":
                        warnings[message.get("kind", "unknown")] += 1
                    admissions += message.get("kind") == "hasSorry"
                    if message.get("severity") == "error" and first_error is None:
                        first_error = message.get("data", "Lean error")
            result.update(warnings=dict(warnings), admissions=admissions)
            record[label + "_warnings"] = sum(warnings.values())
            if label == "template":
                record["template_admissions"] = admissions
            if first_error:
                result["reason"] = first_error
        # Only the backend's explicit error variant means "unsupported".
        if label == "translation" and result["status"] == "error":
            message = diagnostic(directory / result["stderr"])
            if re.search(r"(?m)^smt2lean: cvc5\.Error\.unsupported\b", message):
                result["status"] = "unsupported"
            elif re.search(r"(?m)^smt2lean: cvc5\.Error\.", message):
                result["status"] = "backend_error"
        record["stages"][label] = result
        record[label + "_status"] = result["status"]
        record[label + "_seconds"] = result["seconds"]
        if result["status"] != "passed":
            record.update(outcome=label + "_" + result["status"], reason=result.get("reason", ""))
        return result["status"] == "passed"

    if not stage("translation", [EXE, source, "--out", generated]):
        return
    query = generated / "Query.lean"
    rendered = query.read_bytes()
    record.update(output_bytes=len(rendered), output_sha256=sha256(rendered))
    if len(rendered) > args.max_file_mib * MIB:
        record.update(outcome="output_limit", reason="Query.lean exceeds --max-file-mib")
        return
    statements, separator, proofs = rendered.decode("utf-8").partition("\n-- Proofs\n")
    if not separator:
        record.update(outcome="output_error", reason="Missing emitted -- Proofs boundary")
        return
    goals = re.findall(r"(?m)^(?:noncomputable )?def ((?:Refutation|Problem)(?:_\d+)?) : Prop", statements)
    record.update(emitted_queries=len(goals), goals=goals)
    if not goals or len(goals) != record["input_queries"]:
        record.update(outcome="output_error", reason="Emitted goal count differs from input checks")
        return
    (generated / "Statements.lean").write_text(statements + "\n")
    # Every helper/statement must check without admissions; only templates allow sorry.
    common = [lean, "--json", "-j1", f"-M{args.lean_memory_mib}"]
    statements_ok = stage("statements", [*common, "--error=hasSorry", "Statements.lean"], checking=True)
    if record["statements_status"] == "interrupted":
        return
    saved_failure = (record["outcome"], record.get("reason", ""))
    template_ok = stage("template", [*common, "Query.lean"], checking=True)
    if statements_ok and template_ok:
        record.update(outcome="passed", reason="")
    elif not statements_ok and record["template_status"] != "interrupted":
        record["outcome"], record["reason"] = saved_failure


def save_results(output, records, run):
    with (output / "results.csv").open("w", newline="") as stream:
        writer = csv.DictWriter(stream, FIELDS, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(records)
    outcomes = Counter(r["outcome"] for r in records)
    run["outcomes"] = dict(sorted(outcomes.items()))
    write_json(output / "run.json", run)
    lines = ["# Translation anchor", "", f"Run status: **{run['status']}**. Selected files: **{len(records)}**.",
             "", "Passing means translation, admission-free statement checking, and template checking succeeded.",
             "All proof templates remain **unproved**. Timings are separate process wall times, including startup/imports.",
             "", "| Input kind | Selected | Passed |", "| --- | ---: | ---: |"]
    for kind in sorted({r.get("kind", "unknown") for r in records}):
        selected = [r for r in records if r.get("kind", "unknown") == kind]
        lines.append(f"| {kind} | {len(selected)} | {sum(r['outcome'] == 'passed' for r in selected)} |")
    lines += ["", "| Outcome | Files |", "| --- | ---: |"]
    lines += [f"| {name} | {count} |" for name, count in sorted(outcomes.items())]
    lines += ["", "| Task | Category / logic | Outcome | Translation s | Statements s | Template s | Lean output |",
              "| --- | --- | --- | ---: | ---: | ---: | --- |"]
    for r in records:
        link = f"[{r['id']}]({r['artifacts']}/result.json)" if r["outcome"] != "not_run" else r["id"]
        query = r['artifacts'] + '/generated/Query.lean'
        lean_link = f"[Query.lean]({query})" if (output / query).is_file() else "—"
        category = (r.get("category") or r.get("logic") or "unknown").replace("|", "\\|").replace("\n", " ")
        lines.append(f"| {link} | {category} | {r['outcome']} | " +
                     " | ".join(str(r.get(key + "_seconds", "—")) for key in ("translation", "statements", "template")) + f" | {lean_link} |")
    for r in records:
        if r.get("reason"):
            lines += ["", f"**{r['id']}**: " + " ".join(r["reason"].split())[:500]]
    (output / "summary.md").write_text("\n".join(lines) + "\n")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="*", help="SMT-LIB files or directories (recursive)")
    parser.add_argument("--list", action="append", default=[], help="Text paths or CSV with a path column")
    parser.add_argument("--root", type=Path, help="Base for relative paths in --list (default: list's directory)")
    parser.add_argument("--out", required=True, type=Path, help="New run directory; never overwrite a run")
    parser.add_argument("--translation-timeout", type=float, default=30)
    parser.add_argument("--lean-timeout", type=float, default=60, help="Seconds per Lean check")
    parser.add_argument("--max-input-mib", type=int, default=10)
    parser.add_argument("--max-file-mib", type=int, default=16, help="Per output/log file limit")
    parser.add_argument("--lean-memory-mib", type=int, default=2048)
    args = parser.parse_args(argv)
    for key in ("translation_timeout", "lean_timeout", "max_input_mib", "max_file_mib", "lean_memory_mib"):
        if not math.isfinite(getattr(args, key)) or getattr(args, key) <= 0:
            parser.error(f"{key.replace('_', '-')} must be positive")
    try:
        records = select_inputs(args.paths, args.list, args.root.resolve() if args.root else None)
        if not EXE.is_file():
            raise ValueError("Build the translator first: lake build smt2lean")
        if not os.environ.get("LEAN_PATH"):
            raise ValueError("Run under Lake: lake env python3 benchmarks/run.py ...")
        prefix = subprocess.check_output(["lean", "--print-prefix"], cwd=ROOT, text=True, timeout=30).strip()
        lean = Path(prefix) / "bin/lean"
        output = args.out.resolve()
        output.mkdir(parents=True, exist_ok=False)
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        parser.error(str(error))
    env = dict(os.environ)
    env["LEAN_PATH"] = os.pathsep.join(str((ROOT / p).resolve()) for p in env["LEAN_PATH"].split(os.pathsep) if p)
    for i, record in enumerate(records, 1):
        stem = re.sub(r"[^A-Za-z0-9._-]", "_", Path(record["path"]).stem)[:60]
        record.update(id=f"{i:03d}-{stem}", outcome="not_run", proof_status="unproved",
                      translation_status="not_run", statements_status="not_run", template_status="not_run",
                      stages={}, emitted_queries=0, source=record["selection"].get("source", ""),
                      category=record["selection"].get("category", ""))
        record["artifacts"] = "cases/" + record["id"]
    write_json(output / "selection.json", records)
    for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
        (output / name).write_bytes((ROOT / name).read_bytes())
    (output / "runner.py").write_bytes(Path(__file__).read_bytes())
    patch = subprocess.check_output(["git", "diff", "HEAD", "--binary"], cwd=ROOT)
    (output / "working-tree.patch").write_bytes(patch)
    run = {"status": "running", "started_utc": datetime.now(timezone.utc).isoformat(),
           "arguments": vars(args) | {"out": str(output), "root": str(args.root) if args.root else None},
           "translator_revision": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
           "git_status": subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT, text=True),
           "translator_sha256": sha256(EXE.read_bytes()), "runner_sha256": sha256(Path(__file__).read_bytes()),
           "lean_version": subprocess.check_output([str(lean), "--version"], text=True).strip(),
           "platform": platform.platform(), "python": platform.python_version(),
           "lean_path": env["LEAN_PATH"], "selected_files": len(records),
           "limits_note": "Sequential POSIX processes; per-stage wall time and per-file size limits. Lean -M bounds checker allocation; no translator RSS limit."}
    save_results(output, records, run)
    try:
        for record in records:
            directory = output / record["artifacts"]
            directory.mkdir(parents=True)
            started = time.perf_counter()
            try:
                check_case(record, directory, args, lean, env)
            except (OSError, UnicodeError) as error:
                record.update(outcome="input_error" if record["translation_status"] == "not_run" else "artifact_error", reason=str(error))
            except KeyboardInterrupt:
                record.update(outcome="interrupted", reason="Interrupted by user")
            record["total_seconds"] = round(time.perf_counter() - started, 6)
            write_json(directory / "result.json", record)
            save_results(output, records, run)
            print(f"[{record['id']}] {record['outcome']}", flush=True)
            if record["outcome"].endswith("interrupted"):
                run["status"] = "interrupted"
                break
        else:
            run["status"] = "complete"
    finally:
        if run["status"] == "running":
            run["status"] = "interrupted"
        run["finished_utc"] = datetime.now(timezone.utc).isoformat()
        save_results(output, records, run)
    print(f"Results: {output / 'summary.md'}")
    return 130 if run["status"] == "interrupted" else int(any(r["outcome"] != "passed" for r in records))


if __name__ == "__main__":
    sys.exit(main())
