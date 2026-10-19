#!/usr/bin/env python3
"""Finish the authorized 2026-10-19 campaign, preserving every benchmark outcome."""

import argparse
from collections import Counter
import csv
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shlex
import shutil
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
CORPUS = ROOT / "evaluation"
RESULTS = CORPUS / "results"
SOLVERS = RESULTS / "solvers-300s-2026-10-18-fresh"
REFERENCE = RESULTS / "translation-QF_UFNRA-2026-10-19" / "metadata.json"
SCHEDULE = [
    ("smtcomp-2025-QF_UFLIA.tar.gz", "QF_UFLIA", 300),
    ("smtcomp-2025-QF_AUFLIA.tar.gz", "QF_AUFLIA", 534),
    ("smtcomp-2025-QF_AUFBV.tar.gz", "QF_AUFBV", 75),
    ("smtcomp-2025-LIA.tar.gz", "LIA", 300),
    ("smtcomp-2025-QF_UFNRA.tar.gz", "QF_UFNRA", 48),
    ("smtcomp-2025-QF_DT.tar.gz", "QF_DT", 352),
    ("chccomp-2026-rust-horn.tar.gz", "rust-horn", 73),
    ("chccomp-2026-sally-chc-benchmarks.tar.gz", "sally", 179),
    ("chccomp-2026-ringen-adt-benchmarks.tar.gz", "ringen", 439),
    ("tricera-adt-arr.tar.gz", "tricera", 635),
]
PIN_KEYS = ("source_hashes", "runner_hashes", "translator_sha256", "lean_sha256",
            "cloc_sha256", "lean_version", "cloc_version", "lean_path", "python")
INFRASTRUCTURE = {"launch_error", "cleanup_error", "capture_error", "interrupted"}


def utc():
    return datetime.now(timezone.utc).isoformat()


def read_json(path):
    return json.loads(path.read_text())


def atomic_json(path, value):
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)


def digest(path):
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def output(command):
    return subprocess.check_output(command, cwd=ROOT, text=True, timeout=30).strip()


def notify(out, success, message):
    title = "SMTLib-to-Lean evaluation complete" if success else "SMTLib-to-Lean evaluation stopped"
    # Pass notification text as argv, never interpolate it into AppleScript code.
    script = ('on run argv\n display notification (item 2 of argv) with title '
              '(item 1 of argv)\nend run')
    report = dict(utc=utc(), success_notification=success, title=title, message=message)
    try:
        result = subprocess.run(["osascript", "-e", script, title, message],
                                capture_output=True, text=True, timeout=15)
        report.update(returncode=result.returncode, stdout=result.stdout, stderr=result.stderr)
    except (OSError, subprocess.SubprocessError) as exc:
        report["error"] = repr(exc)
    atomic_json(out / "notification.json", report)


class Queue:
    def __init__(self, out):
        self.out = out
        self.child = None
        self.child_run = None
        self.child_started = None
        self.identities = {}
        self.offsets = {}
        self.completed = {}
        self.progress = {}
        self.started = time.monotonic()

    def event(self, kind, **details):
        value = dict(utc=utc(), event=kind, **details)
        with (self.out / "events.jsonl").open("a") as stream:
            stream.write(json.dumps(value) + "\n")
        print(json.dumps(value), flush=True)

    def initialize(self):
        self.pin = read_json(REFERENCE)
        self.lake = shutil.which("lake")
        require(self.lake, "lake is not available")
        sources = read_json(CORPUS / "sources.json")
        self.archives = {a["archive"]: a for a in sources["archives"]}
        require(sources["file_count"] == 2935 and len(self.archives) == len(SCHEDULE),
                "Unexpected corpus size")
        self.corpus_hashes = {name: digest(CORPUS / name)
                              for name in ("sources.json", "inputs.csv", "SHA256SUMS")}
        with (CORPUS / "inputs.csv").open(newline="") as stream:
            rows = list(csv.DictReader(stream))
        self.inputs = {(r["archive"], r["archive_member"]): r["sha256"] for r in rows}
        require(len(rows) == len(self.inputs) == 2935, "Invalid input manifest")
        self.runs = []
        for archive, label, count in SCHEDULE:
            entry = self.archives["smt-queries/" + archive]
            require(entry["files"] == count, "Unexpected archive size: " + archive)
            self.runs.append(dict(archive=archive, total=count,
                out=RESULTS / ("translation-" + label + "-2026-10-19"),
                generated=CORPUS / "generated" / archive.removesuffix(".tar.gz")))
        self.verify_pins()
        solver = read_json(SOLVERS / "metadata.json")
        require(solver["runs"] == 5870 and solver["inputs"] == 2935 and
                solver["timeout_seconds"] == 300 and solver["memory_mb"] == 4096 and
                solver["smoke_limit"] is None, "Unexpected solver baseline configuration")
        atomic_json(self.out / "metadata.json", dict(started_utc=utc(), pid=os.getpid(),
            command=sys.argv, working_directory=str(ROOT), poll_seconds=10,
            translation_total=2935, solver_total=5870, reference=str(REFERENCE),
            pins={key: self.pin[key] for key in PIN_KEYS}, corpus_hashes=self.corpus_hashes,
            solver_metadata=solver, queue_sha256=digest(Path(__file__)),
            runs=[{k: str(v) if isinstance(v, Path) else v for k, v in r.items()} for r in self.runs]))
        shutil.copyfile(__file__, self.out / "evaluation_queue.py")
        (self.out / "runner.pid").write_text(str(os.getpid()) + "\n")
        for run in self.runs[:5]:
            require(run["out"].exists(), "Required existing run is missing: " + str(run["out"]))

    def verify_pins(self):
        code = [ROOT / "Main.lean", ROOT / "Smt2Lean.lean", *sorted((ROOT / "Smt2Lean").rglob("*.lean")),
                ROOT / "lean-toolchain", ROOT / "lakefile.toml", ROOT / "lake-manifest.json"]
        require({str(p.relative_to(ROOT)): digest(p) for p in code} == self.pin["source_hashes"],
                "Translator source/toolchain hashes changed")
        for name, expected in self.pin["runner_hashes"].items():
            require(digest(ROOT / "scripts" / name) == expected, "Runner changed: " + name)
        for name, expected in self.corpus_hashes.items():
            require(digest(CORPUS / name) == expected, "Corpus metadata changed: " + name)
        lean = Path(output([self.lake, "env", "lean", "--print-prefix"])) / "bin/lean"
        cloc = Path(self.pin["arguments"]["cloc"])
        for path, key in ((ROOT / ".lake/build/bin/smt2lean", "translator_sha256"),
                          (lean, "lean_sha256"), (cloc.resolve(), "cloc_sha256")):
            require(digest(path) == self.pin[key], "Binary changed: " + str(path))
        require(output([str(lean), "--version"]) == self.pin["lean_version"] and
                output([str(cloc), "--version"]) == self.pin["cloc_version"] and
                sys.version == self.pin["python"], "Tool versions changed")
        lean_path = output([self.lake, "env", sys.executable, "-c",
                            "import os; print(os.environ.get('LEAN_PATH', ''))"])
        require(lean_path == self.pin["lean_path"], "Lean dependency paths changed")

    def identity(self, directory, metadata, script):
        pid = metadata["pid"]
        result = subprocess.run(["ps", "-ww", "-p", str(pid), "-o", "uid=,lstart=,command="],
                                capture_output=True, text=True, timeout=10)
        if result.returncode == 1 and not result.stdout.strip() and not result.stderr.strip():
            return False
        require(result.returncode == 0, "Cannot inspect runner PID: " + result.stderr.strip())
        pieces = result.stdout.strip().split(None, 6)
        require(len(pieces) == 7 and int(pieces[0]) == os.getuid(), "Runner ownership mismatch")
        born, command = " ".join(pieces[1:6]), pieces[6]
        args = shlex.split(command)
        require(any(Path(arg).name == script for arg in args) and "--out" in args,
                "Runner PID belongs to another command: " + str(pid))
        destination = Path(args[args.index("--out") + 1])
        require((ROOT / destination).resolve() == directory.resolve(), "Runner output path mismatch")
        identity = (pid, born, command)
        require(directory not in self.identities or self.identities[directory] == identity,
                "Runner process identity changed: " + str(directory))
        # A reused PID born after the recorded runner cannot be adopted.
        started = datetime.fromisoformat(metadata["started_utc"]).timestamp()
        birth = datetime.strptime(born, "%a %b %d %H:%M:%S %Y").timestamp()
        require(birth <= started + 2, "Runner PID was reused: " + str(pid))
        self.identities[directory] = identity
        return True

    def inspect_records(self, directory):
        path = directory / "results.jsonl"
        if not path.exists():
            return
        offset = self.offsets.get(directory, 0)
        with path.open("rb") as stream:
            require(path.stat().st_size >= offset, "Results were truncated: " + str(path))
            stream.seek(offset)
            while True:
                line = stream.readline()
                if not line or not line.endswith(b"\n"):
                    break
                row = json.loads(line)
                stages = row.get("stages", {}).values() if "stages" in row else [row]
                require(not any(s.get("limit_reason") in INFRASTRUCTURE for s in stages),
                        "Infrastructure failure recorded in " + str(path))
                self.offsets[directory] = stream.tell()

    def snapshot(self, directory, total, run=None):
        if not directory.exists():
            require(run is not None, "Solver baseline is missing")
            require(not run["generated"].exists(), "Refusing existing generated output: " + str(run["generated"]))
            return dict(state="pending", completed=0, total=total)
        if not (directory / "progress.json").exists():
            require(directory == self.child_run and self.child.poll() is None,
                    "Partial output has no live owned runner: " + str(directory))
            return dict(state="starting", completed=0, total=total)
        metadata = read_json(directory / "metadata.json")
        if run:
            arguments = metadata["arguments"]
            require(all(metadata[key] == self.pin[key] for key in PIN_KEYS),
                    "Run does not match pinned tools: " + str(directory))
            require(metadata["archive"] == self.archives["smt-queries/" + run["archive"]] and
                    metadata["complete_archive"] and metadata["total"] == total and
                    arguments["timeout"] == 300 and arguments["memory_mb"] == 4096 and
                    arguments["max_rec_depth"] == 4096 and arguments["limit"] is None and
                    Path(arguments["generated"]).resolve() == run["generated"].resolve(),
                    "Unexpected translation configuration: " + str(directory))
        state = read_json(directory / "progress.json")
        require(state["pid"] == metadata["pid"] and state["total"] == total and
                0 <= state["completed"] <= total, "Invalid progress: " + str(directory))
        self.inspect_records(directory)
        require(not (directory / "failure.json").exists(), "Runner failed: " + str(directory))
        if state["state"] != "complete":
            require(state["state"] == "running", "Runner stopped: " + str(directory))
            if not self.identity(directory, metadata, "evaluate_translation.py" if run else "evaluate_solvers.py"):
                # Completion can be written between the first read and ps.
                state = read_json(directory / "progress.json")
                require(state["state"] == "complete", "Runner died before completion: " + str(directory))
        if state["state"] == "complete":
            require(state["completed"] == total, "Incomplete final result: " + str(directory))
            if directory not in self.completed:
                rows = [json.loads(line) for line in (directory / "results.jsonl").read_text().splitlines()]
                keys = [(r["archive"], r["archive_member"]) for r in rows]
                require(len(rows) == total and all(self.inputs.get(k) == r["sha256"] for k, r in zip(keys, rows)),
                        "Completed records do not match inputs: " + str(directory))
                if run:
                    expected = {k for k in self.inputs if k[0] == "smt-queries/" + run["archive"]}
                    require(len(set(keys)) == total and set(keys) == expected, "Incomplete archive coverage")
                else:
                    expected = {(a, member, solver) for a, member in self.inputs
                                for solver in (("z3", "cvc5") if Path(a).name.startswith("smtcomp-")
                                               else ("spacer", "eldarica"))}
                    require({(*k, r["solver"]) for k, r in zip(keys, rows)} == expected,
                            "Incomplete solver coverage")
                self.completed[directory] = rows
        return state

    def refresh(self, state="running", error=None):
        translations = [dict(archive=run["archive"], run=str(run["out"]),
                             **self.snapshot(run["out"], run["total"], run)) for run in self.runs]
        solvers = self.snapshot(SOLVERS, 5870)
        active = [r for r in translations if r["state"] in {"starting", "running"}]
        require(len(active) <= 1, "More than one translation archive is running")
        self.progress = dict(updated_utc=utc(), state=state, pid=os.getpid(),
            wall_seconds=round(time.monotonic() - self.started, 3),
            translation_completed=sum(r["completed"] for r in translations), translation_total=2935,
            solver_completed=solvers["completed"], solver_total=5870,
            current=active[0]["archive"] if active else None, translations=translations, solvers=solvers)
        if error:
            self.progress["error"] = error
        atomic_json(self.out / "progress.json", self.progress)
        return translations, solvers

    def launch(self, run):
        self.verify_pins()
        require(not run["out"].exists() and not run["generated"].exists(),
                "Refusing to overwrite a partial run: " + str(run["out"]))
        archive = self.archives["smt-queries/" + run["archive"]]
        require(digest(CORPUS / archive["archive"]) == archive["sha256"], "Archive hash changed")
        command = [self.lake, "env", sys.executable, "scripts/evaluate_translation.py",
                   "--archive", run["archive"], "--out", str(run["out"]),
                   "--generated", str(run["generated"]), "--timeout", "300", "--memory-mb", "4096",
                   "--max-rec-depth", "4096", "--cloc", self.pin["arguments"]["cloc"]]
        log = self.out / (run["out"].name + ".console.log")
        self.event("launch", archive=run["archive"], command=command, console_log=str(log))
        with log.open("x") as stream:
            self.child = subprocess.Popen(command, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT,
                                          stdin=subprocess.DEVNULL, start_new_session=True)
        self.child_run = run["out"]
        self.child_started = time.monotonic()
        self.event("started", archive=run["archive"], pid=self.child.pid)

    def combine(self):
        rows, summaries = [], {}
        for run in self.runs:
            records = self.completed[run["out"]]
            summaries[run["archive"]] = dict(completed=len(records),
                outcomes=dict(Counter(r["outcome"] for r in records)),
                metrics_outcomes=dict(Counter(r["metrics_status"] for r in records)))
            rows.extend(dict(r, translation_run=str(run["out"].relative_to(ROOT))) for r in records)
        require(len(rows) == 2935 and len(self.completed[SOLVERS]) == 5870, "Campaign is incomplete")
        temporary = self.out / "translations.jsonl.tmp"
        with temporary.open("w") as stream:
            for row in rows:
                stream.write(json.dumps(row) + "\n")
        temporary.replace(self.out / "translations.jsonl")
        temporary = self.out / "translations.csv.tmp"
        with temporary.open("w", newline="") as stream:
            fields = sorted({key for row in rows for key in row})
            writer = csv.DictWriter(stream, fields)
            writer.writeheader()
            writer.writerows({k: json.dumps(v) if isinstance(v, (dict, list)) else v for k, v in r.items()}
                             for r in rows)
        temporary.replace(self.out / "translations.csv")
        atomic_json(self.out / "summary.json", dict(completed_utc=utc(), translation_completed=len(rows),
            solver_completed=5870, translation_outcomes=dict(Counter(r["outcome"] for r in rows)),
            archives=summaries, solver_run=str(SOLVERS.relative_to(ROOT))))

    def run(self):
        self.initialize()
        while True:
            translations, solvers = self.refresh()
            if self.child and not (self.child_run / "progress.json").exists():
                require(time.monotonic() - self.child_started < 120,
                        "Translation runner did not start within 120 seconds: " + str(self.child_run))
            if self.child and self.child.poll() is not None:
                require(self.child.returncode == 0 and self.child_run in self.completed,
                        "Translation runner exited unsuccessfully: " + str(self.child_run))
                self.event("exited", run=str(self.child_run), returncode=self.child.returncode)
                self.child, self.child_run = None, None
            if all(r["state"] == "complete" for r in translations) and solvers["state"] == "complete" and not self.child:
                self.verify_pins()
                self.combine()
                self.refresh("complete")
                self.event("complete", translations=2935, solver_jobs=5870)
                notify(self.out, True, "All 2,935 translations and 5,870 solver jobs finished. Results are ready to review.")
                return
            if not self.child and not any(r["state"] in {"running", "starting"} for r in translations):
                pending = next((r for r, status in zip(self.runs, translations) if status["state"] == "pending"), None)
                if pending:
                    self.launch(pending)
                    continue
            time.sleep(10)

    def fail(self, exc):
        if self.child and self.child.poll() is None:
            # lake env may be a wrapper; signal its entire owned process group
            # so the Python runner can clean up its separately grouped stage.
            try:
                os.killpg(self.child.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            except OSError as error:
                self.event("group_signal_error", error=repr(error))
                metadata_path = self.child_run / "metadata.json"
                try:
                    if metadata_path.exists():
                        metadata = read_json(metadata_path)
                        if self.identity(self.child_run, metadata, "evaluate_translation.py"):
                            os.kill(metadata["pid"], signal.SIGTERM)
                    self.child.terminate()
                except (OSError, RuntimeError, subprocess.SubprocessError) as error:
                    self.event("stop_error", error=repr(error))
            try:
                self.child.wait(timeout=30)
            except subprocess.TimeoutExpired:
                self.event("stop_timeout", pid=self.child.pid)
        error = repr(exc)
        atomic_json(self.out / "failure.json", dict(utc=utc(), error=error))
        self.progress.update(updated_utc=utc(), state="failed", pid=os.getpid(), error=error)
        atomic_json(self.out / "progress.json", self.progress)
        self.event("failed", error=error)
        notify(self.out, False, "Evaluation queue stopped; existing results are preserved. See " + str(self.out / "failure.json"))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True, help="New queue status/log directory")
    args = parser.parse_args()
    out = args.out.resolve()
    if out.exists():
        parser.error("Queue output directory must be new; refusing to overwrite")
    out.mkdir(parents=True, exist_ok=False)
    queue = Queue(out)
    def interrupted(signum, _frame):
        raise RuntimeError("Queue interrupted by signal " + str(signum))
    for sig in (signal.SIGINT, signal.SIGTERM):
        signal.signal(sig, interrupted)
    try:
        queue.run()
    except BaseException as exc:
        queue.fail(exc)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
