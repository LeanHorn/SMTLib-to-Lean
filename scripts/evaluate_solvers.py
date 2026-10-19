#!/usr/bin/env python3
"""Verify/extract the evaluation corpus and measure original inputs with SMT/CHC solvers."""

import argparse
from collections import Counter, defaultdict, deque
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import csv
from datetime import datetime, timezone
import hashlib
import json
import math
import os
from pathlib import Path, PurePosixPath
import platform
import re
import select
import shutil
import signal
import statistics
import subprocess
import tarfile
import threading
import time

CORPUS = Path(__file__).resolve().parents[1] / "evaluation"
STOP = threading.Event()
LOCK = threading.Lock()
ACTIVE = {}
SOLVED = {"sat", "unsat"}


def utc():
    return datetime.now(timezone.utc).isoformat()


def digest(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def safe_path(root, name):
    parts = PurePosixPath(name).parts
    if not parts or PurePosixPath(name).is_absolute() or ".." in parts or "\\" in name:
        raise ValueError("Unsafe archive/manifest path: " + name)
    path = root.joinpath(*parts)
    if any(p.is_symlink() for p in (path, *path.parents)):
        raise ValueError("Symlink in extraction path: " + str(path))
    return path


def prepare():
    sources = json.loads((CORPUS / "sources.json").read_text())
    pins = {line.split(None, 1)[1]: line.split(None, 1)[0]
            for line in (CORPUS / "SHA256SUMS").read_text().splitlines() if line.strip()}
    archives = {a["archive"]: a for a in sources["archives"]}
    if set(pins) != set(archives):
        raise ValueError("Archive lists in sources.json and SHA256SUMS differ")
    labels, roots = {}, {}
    for name, entry in archives.items():
        archive = safe_path(CORPUS, name)
        if digest(archive) != entry["sha256"] or pins[name] != entry["sha256"]:
            raise ValueError("Archive hash mismatch: " + name)
        root = safe_path(CORPUS / "extracted", archive.name.removesuffix(".tar.gz"))
        roots[name] = root
        seen = set()
        with tarfile.open(archive, "r:gz") as stream:
            for member in stream:
                dest = safe_path(root, member.name)
                if member.name in seen or not (member.isfile() or member.isdir()):
                    raise ValueError("Duplicate or nonregular archive member: " + member.name)
                seen.add(member.name)
                if member.isdir():
                    dest.mkdir(parents=True, exist_ok=True)
                    continue
                data = stream.extractfile(member).read()
                dest.parent.mkdir(parents=True, exist_ok=True)
                if dest.exists():
                    if not dest.is_file() or dest.read_bytes() != data:
                        raise ValueError("Existing extracted file differs: " + str(dest))
                else:
                    dest.write_bytes(data)
                if member.name.endswith((".yml", ".yaml")):
                    raw = data.decode("utf-8", errors="replace")
                    match = re.search(r"(?m)^input_files:\s*([^\n]+)$", raw)
                    if match:
                        reference = match[1].strip().strip("\"'")
                        if not re.fullmatch(r"[^\s\[\],]+\.smt2", reference):
                            raise ValueError("Unsupported YAML input_files: " + member.name)
                        target = str(PurePosixPath(member.name).parent / reference)
                        safe_path(root, target)
                        labels.setdefault((name, target), []).append(dict(file=member.name, raw=raw))
    with (CORPUS / "inputs.csv").open(newline="") as stream:
        cases = list(csv.DictReader(stream))
    seen = set()
    for case in cases:
        key = (case["archive"], case["archive_member"])
        if key in seen:
            raise ValueError("Duplicate manifest input: " + str(key))
        seen.add(key)
        path = safe_path(roots[case["archive"]], case["archive_member"])
        if not path.is_file() or path.stat().st_size != int(case["bytes"]) or digest(path) != case["sha256"]:
            raise ValueError("Input size/hash mismatch: " + str(path))
        # Commands at line starts avoid mistaking comments or ordinary strings for queries.
        text = path.read_text(errors="replace")
        has_query = bool(re.search(r"(?m)^\s*\(\s*(?:check-sat(?:-assuming)?|query)\b", text))
        has_assert = bool(re.search(r"(?m)^\s*\(\s*(?:assert|rule)\b", text))
        case.update(path=str(path), bytes=int(case["bytes"]), has_query=has_query, has_assert=has_assert,
                    candidate_eligible=has_query and has_assert, yaml_labels=labels.get(key, []),
                    smt_status=re.findall(r"\(set-info\s+:status\s+(sat|unsat|unknown)\s*\)", text))
    if len(cases) != sources["file_count"]:
        raise ValueError("Input count differs from sources.json")
    return cases


def atomic_json(path, data):
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(data, indent=2) + "\n")
    temporary.replace(path)


def group_members(proc):
    """Only live processes owned by us in the session created for this solver."""
    result = subprocess.run(["ps", "-axo", "pid=,pgid=,uid=,stat="],
                            capture_output=True, text=True, timeout=3, check=True)
    members = []
    for line in result.stdout.splitlines():
        pid, pgid, uid, state = line.split()
        if int(pgid) == proc.pid and int(uid) == os.getuid() and not state.startswith("Z"):
            members.append(int(pid))
    return members


def kill(proc):
    """Return a diagnostic if termination fails; cleanup must never raise."""
    # An unreaped child still reserves its PID; do not send a group signal
    # using a reaped child's PID, which could since have been reused.
    if proc.returncode is None:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
            return None
        except ProcessLookupError:
            return None
        except PermissionError:
            pass
        except OSError as exc:
            return "Cannot terminate solver group: " + repr(exc)
    # Target verified owned PIDs if group signaling was denied, or descendants
    # retain log pipes after their parent has already exited.
    try:
        members = set(group_members(proc))
        if proc.poll() is None:
            members.add(proc.pid)
        for pid in sorted(members, key=lambda pid: pid == proc.pid):
            try:
                os.kill(pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
    except (OSError, subprocess.SubprocessError) as exc:
        return "Cannot terminate solver processes: " + repr(exc)
    return None


def capture(pipe, path, cap, exceeded, stop, failures):
    size = 0
    try:
        with pipe, path.open("wb") as stream:
            os.set_blocking(pipe.fileno(), False)
            while not stop.is_set():
                if not select.select([pipe], [], [], 0.1)[0]:
                    continue
                block = os.read(pipe.fileno(), 65536)
                if not block:
                    return
                remaining = max(0, cap - size)
                stream.write(block[:remaining])
                size += len(block)
                if size > cap:
                    exceeded.set()
    except OSError as exc:
        failures.append("Cannot capture solver output: " + repr(exc))


def classify(stdout, stderr, code, reason):
    combined = stdout + "\n" + stderr
    answers = re.findall(r"(?m)^\s*(sat|unsat|unknown)\s*$", stdout)
    # Rejected assertions, parser failures and unsupported commands invalidate later answers.
    error = re.search(r"(?im)^\s*(?:\(error\b|error\b|exception\b|fatal\b|unsupported\b)", combined)
    internal_timeout = re.search(
        r"(?im)^\s*(?:timeout|time limit exceeded|.*timed out|cvc5 interrupted by timeout\.)\s*$", combined)
    if error or reason in {"memory_limit", "output_limit", "interrupted", "launch_error", "cleanup_error", "capture_error"}:
        status = "error"
    elif reason == "wall_timeout" or internal_timeout:
        status = "timeout"
    elif code != 0 or len(answers) != 1:
        status = "error"
    else:
        status = answers[0]
    return status, answers, "internal_report" if internal_timeout and not reason else reason


def run_one(case, solver, prefix, args, out):
    command = prefix + [case["path"]]
    identity = hashlib.sha256((case["archive"] + ":" + case["archive_member"]).encode()).hexdigest()[:20]
    paths = [out / "logs" / solver / (identity + suffix) for suffix in (".stdout", ".stderr")]
    paths[0].parent.mkdir(parents=True, exist_ok=True)
    started, start = utc(), time.monotonic()
    state = dict(reason=None, peak_rss_kb=0)
    proc, readers, failure = None, [], None
    overflow = threading.Event()
    stop_readers = threading.Event()
    capture_failures, cleanup_failures = [], []
    try:
        if STOP.is_set():
            state["reason"] = "interrupted"
        else:
            proc = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
            with LOCK:
                ACTIVE[proc.pid] = state
            for pipe, path in zip((proc.stdout, proc.stderr), paths):
                reader = threading.Thread(target=capture,
                    args=(pipe, path, args.log_mb * 1024**2, overflow, stop_readers, capture_failures))
                reader.start()
                readers.append(reader)
            while proc.poll() is None:
                reason = ("interrupted" if STOP.is_set() else "capture_error" if capture_failures
                          else "output_limit" if overflow.is_set()
                          else state["reason"] or ("wall_timeout" if time.monotonic() - start >= args.timeout else None))
                if reason:
                    state["reason"] = reason
                    break
                time.sleep(0.05)
    except Exception as exc:
        failure, state["reason"] = str(exc), "launch_error"
    finally:
        try:
            if proc:
                error = kill(proc)
                if error:
                    cleanup_failures.append(error)
                try:
                    proc.wait(timeout=3)
                    survivors = group_members(proc)
                    deadline = time.monotonic() + 1
                    while survivors and time.monotonic() < deadline:
                        time.sleep(0.05)
                        survivors = group_members(proc)
                    if survivors:
                        cleanup_failures.append("Solver group still has live PIDs: " + str(survivors))
                except (OSError, subprocess.SubprocessError) as exc:
                    cleanup_failures.append("Cannot confirm solver termination: " + repr(exc))
            for reader in readers:
                reader.join(timeout=1)
            if any(reader.is_alive() for reader in readers):
                cleanup_failures.append("Solver output pipes did not close")
            stop_readers.set()
            for reader in readers:
                reader.join(timeout=1)
        finally:
            if proc:
                with LOCK:
                    ACTIVE.pop(proc.pid, None)
    if cleanup_failures:
        failure, state["reason"] = "; ".join(cleanup_failures), "cleanup_error"
        STOP.set()  # Do not dispatch more work if resource limits cannot be enforced.
    elif capture_failures:
        failure, state["reason"] = "; ".join(capture_failures), "capture_error"
    elapsed = time.monotonic() - start
    if overflow.is_set() and not state["reason"]:
        state["reason"] = "output_limit"
    for path in paths:
        path.touch(exist_ok=True)
    status, answers, reason = classify(*(p.read_text(errors="replace") for p in paths),
                                        proc.returncode if proc else None, state["reason"])
    return dict(case, solver=solver, status=status, answers=answers, failure=failure, limit_reason=reason,
                pid=proc.pid if proc else None, started_utc=started, ended_utc=utc(), seconds=round(elapsed, 6),
                returncode=proc.returncode if proc else None, sampled_peak_rss_kb=state["peak_rss_kb"] or None,
                command=command, stdout=str(paths[0].relative_to(out)), stderr=str(paths[1].relative_to(out)),
                timeout_method=reason if reason in {"wall_timeout", "internal_report"} else None)


def sample_memory(memory_mb):
    with LOCK:
        active = dict(ACTIVE)
    if not active:
        return
    result = subprocess.run(["ps", "-axo", "pgid=,rss="], capture_output=True, text=True, timeout=3)
    if result.returncode:
        raise RuntimeError("Cannot sample solver memory: " + result.stderr.strip())
    totals = defaultdict(int)
    for line in result.stdout.splitlines():
        group, rss = map(int, line.split())
        if group in active:
            totals[group] += rss
    for pid, state in active.items():
        state["peak_rss_kb"] = max(state["peak_rss_kb"], totals[pid])
        if totals[pid] > memory_mb * 1024:
            state["reason"] = "memory_limit"


def runtime(values):
    values = sorted(values)
    return dict(count=len(values), median=statistics.median(values),
                p95=values[math.ceil(0.95 * len(values)) - 1], maximum=max(values)) if values else dict(count=0)


def summarize(records):
    groups, pairs = defaultdict(list), defaultdict(dict)
    for record in records:
        groups[("all", record["solver"])].append(record)
        groups[(record["suite"], record["solver"])].append(record)
        pairs[(record["archive"], record["archive_member"])][record["solver"]] = record
    totals, suites = {}, {}
    for (suite, solver), rows in sorted(groups.items()):
        solved = sum(r["status"] in SOLVED for r in rows)
        problems = sum(r["candidate_eligible"] for r in rows)
        solved_problems = sum(r["status"] in SOLVED and r["candidate_eligible"] for r in rows)
        value = dict(runs=len(rows), problem_inputs=problems, outcomes=dict(Counter(r["status"] for r in rows)),
                     control_outcomes=dict(Counter(r["status"] for r in rows if not r["candidate_eligible"])),
                     limits=dict(Counter(r["limit_reason"] for r in rows if r["limit_reason"])),
                     solved=solved, solved_percent=round(100 * solved / len(rows), 3),
                     solved_problem_inputs=solved_problems,
                     solved_problem_percent=round(100 * solved_problems / problems, 3) if problems else None,
                     successful_seconds=runtime([r["seconds"] for r in rows if r["status"] in SOLVED]),
                     timeout_seconds=runtime([r["seconds"] for r in rows if r["status"] == "timeout"]))
        (totals if suite == "all" else suites.setdefault(suite, {}))[solver] = value
    disagreements, candidates, neither, complete = [], {}, 0, 0
    for pair in pairs.values():
        if len(pair) != 2:
            continue
        complete += 1
        first = next(iter(pair.values()))
        states = {name: r["status"] for name, r in pair.items()}
        neither += not any(s in SOLVED for s in states.values())
        if set(states.values()) == SOLVED:
            disagreements.append(dict(suite=first["suite"], source_path=first["source_path"], answers=states))
        if first["candidate_eligible"] and all(s in {"timeout", "unknown"} for s in states.values()):
            candidate = candidates.setdefault(first["sha256"], dict(suite=first["suite"], source_path=first["source_path"],
                sha256=first["sha256"], bytes=first["bytes"], statuses=states,
                seconds={name: r["seconds"] for name, r in pair.items()}, duplicate_paths=[]))
            candidate["duplicate_paths"].append(first["source_path"])
    return dict(totals=totals, suites=suites, complete_pairs=complete, neither_solved=neither,
                disagreements=disagreements, candidate_distinct_contents=len(candidates)), sorted(candidates.values(), key=lambda r: r["sha256"])


def write_progress(out, records, total, started, state):
    summary, candidates = summarize(records)
    atomic_json(out / "summary.json", summary)
    with (out / "candidates.csv").open("w", newline="") as stream:
        fields = ["suite", "source_path", "sha256", "bytes", "statuses", "seconds", "duplicate_paths"]
        writer = csv.DictWriter(stream, fields)
        writer.writeheader()
        writer.writerows({k: json.dumps(v) if isinstance(v, (dict, list)) else v for k, v in r.items()} for r in candidates)
    with LOCK:
        pids = sorted(ACTIVE)
    progress = dict(updated_utc=utc(), state=state, pid=os.getpid(), solver_pids=pids,
                    completed=len(records), total=total, remaining=total-len(records),
                    wall_seconds=round(time.monotonic()-started, 3), outcomes=dict(Counter(r["status"] for r in records)))
    atomic_json(out / "progress.json", progress)
    print(json.dumps(progress), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare-only", action="store_true")
    parser.add_argument("--out", type=Path)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--timeout", type=int, default=300)
    parser.add_argument("--memory-mb", type=int, default=4096)
    parser.add_argument("--log-mb", type=int, default=16, help="Maximum bytes per stdout/stderr log, in MiB")
    parser.add_argument("--limit", type=int, help="Smoke test: number of interleaved input paths, each with two solvers")
    parser.add_argument("--z3", default="z3")
    parser.add_argument("--cvc5", default="cvc5")
    parser.add_argument("--eldarica")
    args = parser.parse_args()
    if not 1 <= args.workers <= 4 or min(args.timeout, args.memory_mb, args.log_mb) < 1 or (args.limit is not None and args.limit < 1):
        parser.error("workers must be 1..4; timeout, memory-mb, log-mb and limit must be positive")
    if not args.prepare_only and (args.out is None or args.eldarica is None):
        parser.error("running requires --out and --eldarica")
    cases = prepare()
    print("Verified and extracted {} inputs ({} candidate-eligible)".format(len(cases), sum(c["candidate_eligible"] for c in cases)), flush=True)
    if args.prepare_only:
        return
    for sig in (signal.SIGINT, signal.SIGTERM):
        signal.signal(sig, lambda *_: STOP.set())
    binaries, versions = {}, {}
    for name in ("z3", "cvc5", "eldarica"):
        binary = Path(shutil.which(getattr(args, name)) or getattr(args, name)).resolve()
        binaries[name] = str(binary)
        version = subprocess.run([str(binary), "-h" if name == "eldarica" else "--version"],
                                 capture_output=True, text=True, timeout=15)
        versions[name] = dict(path=str(binary), sha256=digest(binary), stdout=version.stdout,
                              stderr=version.stderr, returncode=version.returncode)
    prefixes = dict(z3=[binaries["z3"], "-smt2", "timeout={}".format(args.timeout*1000)],
                    cvc5=[binaries["cvc5"], "--lang=smt2", "--tlimit={}".format(args.timeout*1000)],
                    spacer=[binaries["z3"], "-smt2", "smt.logic=HORN", "fp.engine=spacer", "timeout={}".format(args.timeout*1000)],
                    eldarica=[binaries["eldarica"], "-horn", "-hsmt", "-t:{}".format(args.timeout)])
    queues = defaultdict(deque)
    for case in sorted(cases, key=lambda c: (c["suite"], c["source_path"])):
        queues[case["suite"]].append(case)
    ordered = []
    while any(queues.values()):
        for suite in sorted(queues):
            if queues[suite]:
                ordered.append(queues[suite].popleft())
    ordered = ordered[:args.limit] if args.limit else ordered
    jobs = [(case, name) for case in ordered for name in (("z3", "cvc5") if case["suite"].startswith("smtcomp-") else ("spacer", "eldarica"))]
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    for source in (Path(__file__), CORPUS / "inputs.csv", CORPUS / "sources.json", CORPUS / "SHA256SUMS"):
        shutil.copyfile(source, out / source.name)
    metadata = dict(started_utc=utc(), pid=os.getpid(), workers=args.workers, timeout_seconds=args.timeout,
        memory_mb=args.memory_mb, log_mb=args.log_mb, inputs=len(ordered), runs=len(jobs), smoke_limit=args.limit,
        platform=platform.platform(), python=platform.python_version(), logical_cpus=os.cpu_count(),
        repository_revision=subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=CORPUS.parent, text=True).strip(),
        solvers=versions, commands=prefixes,
        snapshot_sha256={p.name: digest(p) for p in out.iterdir()},
        timing="Process wall seconds including startup; concurrent shared CPU, not dedicated CPU seconds. External process-group SIGKILL deadline plus internal solver limits.",
        cleanup="Bounded cleanup; denied group signals fall back to verified owned PIDs. Cleanup failures are infrastructure errors and stop further dispatch.",
        memory="Approximate process-group RSS sampled at most once per second; includes descendants. Exceeding limit causes error/memory_limit, never a challenge candidate.",
        labels="Raw upstream YAML and SMT status preserved only; not validated ground truth.",
        candidates="Both solvers timeout or unknown; requires an assertion/rule and query; SHA-256 deduplicated; errors excluded.")
    atomic_json(out / "metadata.json", metadata)
    (out / "runner.pid").write_text(str(os.getpid()) + "\n")
    fields = ["suite", "source_path", "solver", "status", "seconds", "returncode", "limit_reason", "sha256", "bytes", "started_utc", "ended_utc", "pid", "sampled_peak_rss_kb", "stdout", "stderr", "candidate_eligible"]
    records, pending, cursor = [], {}, 0
    started = last_report = last_memory = time.monotonic()
    last_count, state = 0, "running"
    pool = ThreadPoolExecutor(args.workers)
    try:
        with (out / "results.jsonl").open("w") as jsonl, (out / "results.csv").open("w", newline="") as csvfile:
            writer = csv.DictWriter(csvfile, fields, extrasaction="ignore")
            writer.writeheader()
            csvfile.flush()
            write_progress(out, records, len(jobs), started, state)
            while pending or (cursor < len(jobs) and not STOP.is_set()):
                while len(pending) < args.workers and cursor < len(jobs) and not STOP.is_set():
                    case, name = jobs[cursor]
                    pending[pool.submit(run_one, case, name, prefixes[name], args, out)] = cursor
                    cursor += 1
                done, _ = wait(pending, timeout=0.2, return_when=FIRST_COMPLETED)
                for future in sorted(done, key=lambda f: pending[f]):
                    pending.pop(future)
                    result = future.result()
                    records.append(result)
                    jsonl.write(json.dumps(result) + "\n")
                    jsonl.flush()
                    writer.writerow(result)
                    csvfile.flush()
                now = time.monotonic()
                if now - last_memory >= 1:
                    sample_memory(args.memory_mb)
                    last_memory = time.monotonic()
                if len(records) - last_count >= 10 or now - last_report >= 5:
                    write_progress(out, records, len(jobs), started, "stopping" if STOP.is_set() else state)
                    last_report, last_count = now, len(records)
            state = ("failed" if any(r["limit_reason"] == "cleanup_error" for r in records)
                     else "interrupted" if STOP.is_set() else "complete")
            if state == "failed":
                atomic_json(out / "failure.json", dict(utc=utc(), error="Solver cleanup failed; see result diagnostics"))
    except BaseException as exc:
        state = "failed"
        atomic_json(out / "failure.json", dict(utc=utc(), error=repr(exc)))
        raise
    finally:
        STOP.set()
        pool.shutdown(wait=True)
        write_progress(out, records, len(jobs), started, state)
    if state != "complete":
        raise SystemExit(130)


if __name__ == "__main__":
    main()
