#!/usr/bin/env python3
"""Start or resume a sequential, fully audited translation campaign on macOS.

Example: lake env python3 scripts/evaluate.py campaign --out evaluation/results/NEW
  --generated evaluation/generated/NEW

Both directories must be new. Fixed policy: one worker, 300 seconds per stage,
4096 MiB, maxRecDepth 4096, equivalence off. Expected benchmark failures are
retained; inspection, infrastructure, integrity and bookkeeping failures stop
the campaign. Resume with --resume --out using the original frozen environment.
There is no solver execution. Installed
Lean/dependencies are hashed, not copied; do not rebuild them during a campaign.
AC power and owned caffeinate -is assertions are checked every ten seconds.
This prevents idle/system sleep while on AC; it does not guarantee lid-close
operation. Keep the lid open. RSS limits are sampled, not hard allocation caps.
"""

import argparse
from collections import Counter
import csv
import fcntl
import hashlib
import importlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import signal
import subprocess
import sys
import time
from types import SimpleNamespace

if __package__:
    from . import solvers as processes
else:
    import solvers as processes

ROOT = Path(os.environ.get("SMT2LEAN_PROJECT_ROOT", Path(__file__).resolve().parents[2])).resolve()
SCHEDULE = [
    ("smtcomp-2025-QF_UFNRA.tar.gz", 48), ("smtcomp-2025-LIA.tar.gz", 300),
    ("chccomp-2026-rust-horn.tar.gz", 73), ("smtcomp-2025-QF_UFLIA.tar.gz", 300),
    ("smtcomp-2025-QF_AUFLIA.tar.gz", 534), ("chccomp-2026-sally-chc-benchmarks.tar.gz", 179),
    ("chccomp-2026-ringen-adt-benchmarks.tar.gz", 439), ("smtcomp-2025-QF_DT.tar.gz", 352),
    ("smtcomp-2025-QF_AUFBV.tar.gz", 75), ("tricera-adt-arr.tar.gz", 635),
]
RUNNERS = ("translation.py", "metrics.py", "solvers.py")
STAGES = ("translation", "statements", "template")
BENCHMARK_STATUSES = {"passed", "error", "unsupported", "timeout", "memory_limit", "output_limit"}
INFRASTRUCTURE = {"launch_error", "cleanup_error", "capture_error", "interrupted"}


utc = processes.utc
atomic_json = processes.atomic_json


def digest(path):
    return processes.digest(Path(path))


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def read_json(path):
    return json.loads(path.read_text())


def import_frozen(snapshot, filenames, pins):
    """Verify snapshots before importing them, without reusing live flat modules."""
    snapshot = snapshot.resolve()
    names = [Path(filename).stem for filename in filenames]
    for filename in filenames:
        path = snapshot / filename
        require(digest(path) == pins.get(str(path)), "Pinned runner changed: " + str(path))
    for name in names:
        module = sys.modules.get(name)
        if module is not None and Path(module.__file__).resolve() != snapshot / (name + ".py"):
            del sys.modules[name]
    sys.path.insert(0, str(snapshot))
    modules = {name: importlib.import_module(name) for name in reversed(names)}
    for name, module in modules.items():
        require(Path(module.__file__).resolve() == snapshot / (name + ".py"),
                "Failed to import pinned runner: " + name)
    return modules


def output(command):
    return subprocess.check_output(command, cwd=ROOT, text=True, timeout=30).strip()


def assertion_evidence(assertions, battery, pid):
    """Require both active assertion types to belong to our live guard PID."""
    require(re.search(r"Now drawing from ['\"]AC Power['\"]", battery), "AC power is required")
    for kind in ("PreventUserIdleSystemSleep", "PreventSystemSleep"):
        require(re.search(r"(?m)^\s*" + kind + r"\s+1\s*$", assertions),
                "Inactive system-wide sleep assertion: " + kind)
        require(re.search(r"(?m)^\s*pid\s+" + str(pid) +
                          r"\(caffeinate\):.*\b" + kind + r"\b", assertions),
                "Owned caffeinate assertion missing: " + kind)
    return dict(pid=pid, verified_utc=utc(), assertions=assertions, battery=battery)


def validate_record(row, expected, generated, runner, directory):
    key = (row["archive"], row["archive_member"])
    require(key in expected, "Unknown record identity: " + str(key))
    require(all(row.get(k) == v for k, v in expected[key].items()),
            "Input manifest mismatch: " + str(key))
    source = Path(row["path"])
    require(source.stat().st_size == int(row["bytes"]) and digest(source) == row["sha256"],
            "Extracted input changed: " + str(source))
    require(row["input_metrics_status"] == "passed", "Input metrics failed: " + str(key))
    require(isinstance(row["query_count"], int) and row["query_count"] >= 0,
            "Invalid query count: " + str(key))
    statuses = {name: row[name + "_status"] for name in STAGES}
    require(set(row["stages"]) == {name for name in STAGES if statuses[name] != "not_run"},
            "Missing or extra stage records: " + str(key))
    for name, stage in row["stages"].items():
        require(stage["status"] == statuses[name] and stage["status"] in BENCHMARK_STATUSES,
                "Invalid or infrastructure stage status: " + str(key))
        require(stage.get("limit_reason") not in INFRASTRUCTURE and not stage.get("failure"),
                "Stage infrastructure failure: " + str(key))
        require(stage["failure_category"] != "error", "Unclassified benchmark error needs review: " + str(key))
        require(runner.stage_status(stage, name == "translation") == stage["status"],
                "Stage classification mismatch: " + str(key))
        require(stage["seconds"] >= 0 and row[name + "_seconds"] == stage["seconds"],
                "Invalid stage timing: " + str(key))
        for channel in ("stdout", "stderr"):
            require(runner.processes.safe_path(directory, stage[channel]).is_file(),
                    "Missing stage log: " + str(key))
    if statuses["translation"] != "passed":
        require(statuses["translation"] in BENCHMARK_STATUSES - {"passed"} and
                statuses["statements"] == statuses["template"] == "not_run" and
                row["outcome"] == "translation_" + statuses["translation"] and
                "generated" not in row and row["metrics_status"] == "not_run",
                "Invalid failed-translation record: " + str(key))
    else:
        require(row["metrics_status"] == "passed", "Output metrics failed: " + str(key))
        require(row["emitted_queries"] == row["query_count"], "Query-count mismatch: " + str(key))
        destination = (ROOT / row["generated"]).resolve()
        require(destination == runner.processes.safe_path(generated, row["output_relative"]).resolve()
                and destination.is_relative_to(generated.resolve()), "Unexpected generated path")
        require(destination.is_file() and digest(destination) == row["output_sha256"] and
                destination.stat().st_size == row["output_bytes"], "Generated output hash/size mismatch")
        expected_outcome = next((name + "_" + statuses[name] for name in STAGES
                                 if statuses[name] != "passed"), "passed")
        require(all(statuses[name] in BENCHMARK_STATUSES for name in STAGES) and
                row["outcome"] == expected_outcome, "Invalid outcome: " + str(key))
    return key


class Campaign:
    def __init__(self, args):
        self.args, self.out = args, args.out
        self.guard = self.child = None
        self.stopping = False
        self.records, self.completed, self.current = [], [], None
        self.started = time.monotonic()
        self.pins = {}
        self.last_checkpoint = 0
        self.last_clock = None
        self.owned = {}

    def event(self, kind, **details):
        record = dict(utc=utc(), event=kind, **details)
        with (self.out / "events.jsonl").open("a") as stream:
            stream.write(json.dumps(record) + "\n")
        print(json.dumps(record), flush=True)

    def progress(self, state):
        atomic_json(self.out / "progress.json", dict(state=state, pid=os.getpid(), updated_utc=utc(),
            total=sum(count for _, count in SCHEDULE), completed=len(self.records),
            completed_archives=self.completed, current=self.current,
            wall_seconds=round(time.monotonic() - self.started, 3),
            outcomes=dict(Counter(row["outcome"] for row in self.records))))

    def checkpoint(self):
        clocks = (time.time(), time.monotonic())
        if self.last_clock is not None:
            require(abs((clocks[0] - self.last_clock[0]) - (clocks[1] - self.last_clock[1])) <= 5,
                    "Suspected system suspend or clock change; campaign timing may be invalid")
        self.last_clock = clocks
        require(not self.stopping, "Campaign interrupted")
        require(self.guard is not None and self.guard.poll() is None, "Sleep guard exited")
        evidence = assertion_evidence(output(["pmset", "-g", "assertions"]),
                                      output(["pmset", "-g", "batt"]), self.guard.pid)
        evidence["free_bytes"] = {str(p): shutil.disk_usage(p).free
                                  for p in (self.out, self.args.generated)}
        require(min(evidence["free_bytes"].values()) >= self.args.min_free_gib * 1024**3,
                "Free disk space fell below minimum")
        atomic_json(self.out / "guard.json", evidence)
        self.last_checkpoint = time.monotonic()

    def periodic_checkpoint(self):
        if time.monotonic() - self.last_checkpoint >= 10:
            self.checkpoint()

    def source_files(self):
        return [ROOT / "Main.lean", ROOT / "Smt2Lean.lean",
                *sorted((ROOT / "Smt2Lean").rglob("*.lean")),
                *[ROOT / name for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json",
                  "patches/cvc5-owned-arguments.patch", ".lake/packages/cvc5/ffi/ffi.cpp",
                  ".lake/packages/cvc5/cvc5.lean")]]

    def pin(self, path, copy_to=None):
        self.periodic_checkpoint()
        path = path.resolve()
        self.pins[str(path)] = digest(path)
        if copy_to is not None:
            copy_to.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(path, copy_to)
            self.pins[str(copy_to.resolve())] = digest(copy_to)
            require(self.pins[str(path)] == self.pins[str(copy_to.resolve())], "Snapshot copy mismatch")

    def verify_pins(self):
        require(self.sources == [str(p) for p in self.source_files()], "Source file set changed")
        for name, expected in self.pins.items():
            self.periodic_checkpoint()
            require(digest(name) == expected, "Pinned file changed: " + name)
        require(self.dependencies == self.dependency_files(), "Lean dependency file set changed")

    def dependency_files(self):
        paths = set()
        for directory in self.lean_paths:
            for path in directory.rglob("*"):
                self.periodic_checkpoint()
                if path.is_file():
                    paths.add(str(path.resolve()))
        return sorted(paths)

    def initialize(self):
        require(platform.system() == "Darwin", "This campaign requires macOS sleep assertions")
        self.out.mkdir(parents=True)
        self.args.generated.mkdir(parents=True)
        (self.out / "runner.pid").write_text(str(os.getpid()) + "\n")
        self.guard = subprocess.Popen(["/usr/bin/caffeinate", "-is", "-w", str(os.getpid())])
        for _ in range(20):
            try:
                self.checkpoint()
                break
            except RuntimeError:
                time.sleep(0.1)
        self.checkpoint()
        self.event("guard_verified", pid=self.guard.pid, lid_close_guaranteed=False)
        snapshot = self.out / "snapshot"
        for name in RUNNERS:
            self.pin(Path(__file__).parent / name, snapshot / name)
        self.pin(Path(__file__), snapshot / "campaign.py")
        self.pin(self.args.translator, snapshot / "smt2lean")
        self.translator = snapshot / "smt2lean"
        self.sources = [str(p) for p in self.source_files()]
        for path in self.source_files():
            self.pin(path, snapshot / "sources" / path.relative_to(ROOT))
        corpus = ROOT / "evaluation"
        for name in ("sources.json", "inputs.csv", "SHA256SUMS"):
            self.pin(corpus / name, snapshot / "corpus" / name)
        self.archives = {a["archive"]: a for a in read_json(corpus / "sources.json")["archives"]}
        sums = dict((line.split(None, 1)[1], line.split(None, 1)[0])
                    for line in (corpus / "SHA256SUMS").read_text().splitlines() if line.strip())
        with (corpus / "inputs.csv").open(newline="") as stream:
            rows = list(csv.DictReader(stream))
        self.expected = {(row["archive"], row["archive_member"]): row for row in rows}
        require(len(rows) == len(self.expected) == sum(count for _, count in SCHEDULE),
                "Duplicate identities or unexpected corpus count")
        require(set(self.archives) == set(sums) == {"smt-queries/" + name for name, _ in SCHEDULE},
                "Unexpected archive set")
        for name, count in SCHEDULE:
            key = "smt-queries/" + name
            self.pin(corpus / key)
            require(self.archives[key]["files"] == sum(r["archive"] == key for r in rows) == count
                    and digest(corpus / key) == self.archives[key]["sha256"] == sums[key],
                    "Archive count/hash mismatch: " + name)
            cases = [row for row in rows if row["archive"] == key]
            parent = Path(os.path.commonpath([str(Path(row["archive_member"]).parent) for row in cases]))
            for row in cases:
                row["output_relative"] = str(Path(row["archive_member"]).relative_to(parent).with_suffix(".lean"))
                row["path"] = str(corpus / "extracted" / name.removesuffix(".tar.gz") / row["archive_member"])
            require(len({row["output_relative"].lower() for row in cases}) == count, "Output filename collision")
        self.lean = Path(output(["lean", "--print-prefix"])) / "bin/lean"
        for path in (self.lean, Path(self.args.cloc), Path(sys.executable)):
            self.pin(path)
        self.lean_paths = [Path(p).resolve() for p in os.environ["LEAN_PATH"].split(os.pathsep) if p]
        for directory in [self.lean.parent.parent / "lib/lean", *[p.parent for p in self.lean_paths]]:
            for library in directory.glob("*.dylib"):
                self.pin(library)
        self.dependencies = self.dependency_files()
        for path in self.dependencies:
            self.pin(Path(path))
        os.environ["SMT2LEAN_PROJECT_ROOT"] = str(ROOT)
        self.runner = import_frozen(snapshot, RUNNERS, self.pins)["translation"]
        metadata = dict(started_utc=utc(), pid=os.getpid(), command=sys.argv, root=str(ROOT),
            arguments={k: str(v) if isinstance(v, Path) else v for k, v in vars(self.args).items()},
            policy=dict(workers=1, timeout=300, memory_mb=4096, max_rec_depth=4096, equivalence=False),
            schedule=SCHEDULE, source_files=self.sources, pins=self.pins, dependencies=self.dependencies,
            python=sys.version, lean_version=output([str(self.lean), "--version"]),
            cloc_version=output([self.args.cloc, "--version"]), platform=platform.platform(),
            machine=output(["sysctl", "-n", "hw.model", "hw.memsize", "hw.logicalcpu"]),
            macos=output(["sw_vers"]), git_commit=output(["git", "rev-parse", "HEAD"]),
            git_status=output(["git", "status", "--short"]), guard_pid=self.guard.pid,
            environment={k: os.environ.get(k) for k in ("PATH", "LEAN_PATH", "LEAN_SRC_PATH",
                "DYLD_LIBRARY_PATH", "LANG", "LC_ALL", "TMPDIR", "SMT2LEAN_PROJECT_ROOT")})
        atomic_json(self.out / "metadata.json", metadata)
        self.checkpoint()
        self.progress("running")
        self.report("running")

    def inspect(self, directory, generated, seen, final=False):
        path = directory / "results.jsonl"
        if not path.exists():
            require(not final, "Missing results")
            return
        data = path.read_bytes()
        if final:
            require(not data or data.endswith(b"\n"), "Truncated final record")
        lines = data.splitlines() if data.endswith(b"\n") else data.splitlines()[:-1]
        require(len(lines) >= len(seen), "Results were truncated")
        for index, line in enumerate(lines):
            if index < len(seen):
                require(digest_bytes(line) == seen[index][1], "Existing record changed")
                if final:
                    self.periodic_checkpoint()
                    validate_record(json.loads(line), self.expected, generated, self.runner, directory)
                continue
            row = json.loads(line)
            key = validate_record(row, self.expected, generated, self.runner, directory)
            require(key not in {item[0] for item in seen}, "Duplicate record")
            seen.append((key, digest_bytes(line)))
            self.records.append(row)
            with (self.out / "results.jsonl").open("a") as stream:
                stream.write(json.dumps(row) + "\n")
        atomic_json(self.out / "summary.json", self.runner.summarize(self.records))

    def run_archive(self, archive, count):
        label = archive.removesuffix(".tar.gz")
        directory, generated = self.out / "archives" / label, self.args.generated / label
        self.current = dict(archive=archive, total=count, completed=0)
        self.verify_pins()
        self.checkpoint()
        command = [sys.executable, str(self.out / "snapshot/translation.py"),
                   "--archive", archive, "--out", str(directory), "--generated", str(generated),
                   "--translator", str(self.translator), "--cloc", self.args.cloc,
                   "--timeout", "300", "--memory-mb", "4096", "--max-rec-depth", "4096"]
        seen = []
        self.event("archive_started", archive=archive, command=command)
        self.supervise_archive(directory, generated, seen, command, self.out / (label + ".log"))
        self.audit_archive(archive, count, directory, generated, seen)

    def supervise_archive(self, directory, generated, seen, command, log_path, root=ROOT,
                          resuming=False):
        with log_path.open("w") as log:
            self.child = subprocess.Popen(command, cwd=root, stdout=log, stderr=subprocess.STDOUT,
                                          start_new_session=True)
            child_started = time.monotonic()
            while self.child.poll() is None:
                self.capture_owned()
                self.checkpoint()
                require(not (directory / "failure.json").exists(), "Archive runner reported failure")
                self.inspect(directory, generated, seen)
                progress = directory / "progress.json"
                require((progress.exists() and time.time() - progress.stat().st_mtime < 60) or
                        ((resuming or not progress.exists()) and
                         time.monotonic() - child_started < 60),
                        "Archive runner heartbeat missing or stale")
                self.current.update(completed=len(seen), pid=self.child.pid)
                self.progress("running")
                try:
                    self.child.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    pass
            require(self.child.returncode == 0, "Archive runner exited with " + str(self.child.returncode))

    def audit_archive(self, archive, count, directory, generated, seen, root=ROOT, runners=RUNNERS):
        self.inspect(directory, generated, seen, final=True)
        self.capture_owned()
        require(not self.owned, "Owned benchmark processes remained after archive exit")
        self.verify_pins()
        self.checkpoint()
        expected = {key for key in self.expected if key[0] == "smt-queries/" + archive}
        require(len(seen) == count and {key for key, _ in seen} == expected, "Incomplete archive")
        state, meta = read_json(directory / "progress.json"), read_json(directory / "metadata.json")
        require(state["state"] == "complete" and state["completed"] == state["total"] == count
                and meta["complete_archive"] and meta["total"] == count and meta["workers"] == 1
                and not (directory / "failure.json").exists(), "Incomplete archive state")
        require(meta["translator_sha256"] == digest(self.translator) and
                meta["lean_sha256"] == digest(self.lean) and
                meta["cloc_sha256"] == digest(self.args.cloc), "Archive tool pins differ")
        arguments = meta["arguments"]
        require(meta["archive"] == self.archives["smt-queries/" + archive] and
                meta["lean_path"] == os.environ["LEAN_PATH"] and meta["check_equivalence"] is False
                and arguments["timeout"] == 300 and arguments["memory_mb"] == 4096
                and arguments["max_rec_depth"] == 4096 and arguments["limit"] is None
                and arguments["translator"] == str(self.translator)
                and arguments["generated"] == str(generated), "Archive configuration differs")
        for name in runners:
            require(meta["runner_hashes"][name] == digest(self.out / "snapshot" / name),
                    "Archive runner snapshot differs")
        rows = [row for row in self.records if row["archive"] == "smt-queries/" + archive]
        require({p.resolve() for p in generated.rglob("*") if p.is_file()} ==
                {(root / row["generated"]).resolve() for row in rows if row.get("generated")},
                "Unexpected or missing generated files")
        require(read_json(directory / "summary.json") == self.runner.summarize(rows), "Summary mismatch")
        atomic_json(directory / "audit.json", dict(utc=utc(), state="passed", records=count,
            identities_verified=True, input_hashes_verified=True, output_hashes_verified=True,
            statuses_verified=True, pins_verified=True, results_sha256=digest(directory / "results.jsonl"),
            **({"resume_session": self.session} if hasattr(self, "session") else {})))
        self.completed.append(archive)
        self.event("archive_audited", archive=archive, records=count)
        self.current = None
        self.report("running")

    def capture_owned(self):
        """Remember owned process identities, including stages orphaned by a dead runner."""
        table, roots = {}, set()
        for line in output(["ps", "-ww", "-axo", "pid=,ppid=,pgid=,uid=,lstart=,stat=,command="]).splitlines():
            parts = line.split(None, 10)
            require(len(parts) == 11, "Cannot inspect owned worker descendants")
            if int(parts[3]) != os.getuid() or parts[9].startswith("Z"):
                continue
            pid, command = int(parts[0]), parts[10]
            table[pid] = (int(parts[1]), tuple(parts[2:9]))
            # These executables with this fresh campaign's private paths are
            # attributable even if the runner died before the next poll.
            translation = hasattr(self, "translator") and command.startswith(str(self.translator) + " ")
            lean = hasattr(self, "lean") and command.startswith(str(self.lean) + " ")
            private_path = str(self.out / "archives") + "/" in command or str(self.args.generated) + "/" in command
            if private_path and (translation or lean):
                roots.add(pid)
        if self.child is not None and self.child.returncode is None:
            roots.add(self.child.pid)  # An unreaped owned child reserves this PID.
        owned = {pid: table[pid] for pid in roots if pid in table and pid != self.child.pid}
        while True:
            children = {pid: item for pid, item in table.items() if item[0] in roots and pid not in roots}
            if not children:
                break
            owned.update(children)
            roots.update(children)
        self.owned = {pid: item for pid, item in self.owned.items()
                      if pid in table and table[pid][1] == item[1]}
        self.owned.update(owned)

    def report(self, state):
        summary = self.runner.summarize(self.records)
        atomic_json(self.out / "summary.json", summary)
        fields = ["suite", "archive", "source_path", "sha256", "generated", "outcome", "control",
                  "failure_category", "query_count", "emitted_queries", "input_bytes", "output_bytes",
                  "input_code_loc", "output_code_loc", "input_tokens", "output_tokens", "token_ratio",
                  "code_loc_ratio", "byte_ratio", "translation_and_statements_seconds"]
        fields += [stage + suffix for stage in STAGES for suffix in ("_status", "_seconds")]
        temporary = self.out / "results.csv.tmp"
        with temporary.open("w", newline="") as stream:
            writer = csv.DictWriter(stream, fields, extrasaction="ignore")
            writer.writeheader()
            writer.writerows(self.records)
        temporary.replace(self.out / "results.csv")
        lines = ["# Translation campaign", "", f"State: **{state}**; updated {utc()}.",
            f"Coverage: {len(self.records)}/2935 inputs; {summary['passed']} passed; "
            f"{summary['controls']} controls; {len(self.completed)}/10 archives audited.", "",
            "Partial results remain provisional until every archive is audited.", "",
            "[Metadata and pins](metadata.json) · [Progress](progress.json) · [Summary](summary.json) · "
            "[Full records](results.jsonl) · [Flat records](results.csv)", "",
            "| Archive | Audited | Recorded / total | Passed |", "|---|---|---:|---:|"]
        for archive, count in SCHEDULE:
            rows = [r for r in self.records if r["archive"] == "smt-queries/" + archive]
            lines.append(f"| {archive} | {'yes' if archive in self.completed else 'no'} | "
                         f"{len(rows)} / {count} | {sum(r['outcome'] == 'passed' for r in rows)} |")
        lines += ["", "| Stage | Successful seconds median / p95 | Sampled peak RSS KiB median / p95 |",
                  "|---|---:|---:|"]
        for stage in STAGES:
            timing, memory = summary[stage + "_successful_seconds"], summary[stage + "_sampled_peak_rss_kb"]
            lines.append(f"| {stage} | {timing.get('median', 'n/a')} / {timing.get('p95', 'n/a')} | "
                         f"{memory.get('median', 'n/a')} / {memory.get('p95', 'n/a')} |")
        ratio = summary["token_ratio"]
        lines += ["", f"Token expansion median / p95: {ratio.get('median', 'n/a')} / {ratio.get('p95', 'n/a')}; "
                  f"ratio of total output/input tokens: {summary['total_token_ratio']}.", "",
            "Each stage uses a 300 s wall limit and 4096 MiB sampled process-group RSS limit; "
            "Lean also receives -M4096. One worker; maxRecDepth 4096; equivalence checking off.",
            "Times include subprocess startup, polling and cleanup; exclude build and metrics. "
            "Successful timing populations exclude failures; all-attempt times and failed-time totals remain in summary.json.",
            "RSS populations include all sampled attempts and may miss brief peaks. Shared-machine wall time is not isolated CPU time.",
            "Size ratios use fully typechecked cases only. Code LOC is cloc code lines after "
            "comment/string-aware normalization; tokens use the repository's language-specific lexical counters. "
            "Output tokens, code LOC and statement bytes count declarations/helpers before -- Proofs, "
            "excluding imports, options and namespace/section scaffolding. Raw output bytes retain the full file.",
            "Controls, duplicate contents, expected resource/unsupported failures and every input remain in records. "
            "Sleep assertions require AC power and do not guarantee lid-close operation. "
            "Wall/monotonic clock divergence above five seconds stops the campaign as suspected suspend or clock change.", ""]
        (self.out / "report.md.tmp").write_text("\n".join(lines))
        (self.out / "report.md.tmp").replace(self.out / "report.md")

    def close(self):
        if self.child is not None:
            self.capture_owned()
            if self.child.poll() is None:
                self.child.terminate()
                try:
                    self.child.wait(timeout=30)
                except subprocess.TimeoutExpired:
                    self.capture_owned()
                    self.child.kill()
                    self.child.wait(timeout=5)
            def still_owned(pid, identity):
                result = subprocess.run(["ps", "-p", str(pid), "-o", "pgid=,uid=,lstart=,stat="],
                                        capture_output=True, text=True, timeout=10)
                require(result.returncode in (0, 1) and not result.stderr, "Cannot verify worker cleanup")
                current = result.stdout.split()
                return len(current) == 8 and tuple(current[:7]) == identity and not current[-1].startswith("Z")
            for pid, (_, identity) in self.owned.items():
                if still_owned(pid, identity):
                    try:
                        os.kill(pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
            for _ in range(20):
                survivors = [pid for pid, (_, identity) in self.owned.items() if still_owned(pid, identity)]
                if not survivors:
                    break
                time.sleep(0.1)
            require(not survivors, "Owned worker descendants survived cleanup: " + str(survivors))
            self.event("owned_worker_stopped", pid=self.child.pid, inspected_descendants=list(self.owned))
        if self.guard is not None and self.guard.poll() is None:
            self.guard.terminate()
            self.guard.wait(timeout=5)


def digest_bytes(data):
    return hashlib.sha256(data).hexdigest()


def read_rows(path):
    data = path.read_bytes()
    if data and not data.endswith(b"\n"):
        raise RuntimeError("Truncated records require manual recovery: " + str(path))
    return [json.loads(line) for line in data.splitlines()]


def write_rows(path, rows):
    temporary = path.with_suffix(path.suffix + ".tmp")
    with temporary.open("w") as stream:
        for row in rows:
            stream.write(json.dumps(row) + "\n")
    temporary.replace(path)


def partition_records(rows):
    """Only an interrupted final attempt may be retried; retain benchmark failures."""
    kept, interrupted, seen = [], [], set()
    for index, row in enumerate(rows):
        key = (row["archive"], row["archive_member"])
        if key in seen:
            raise RuntimeError("Duplicate record: " + str(key))
        seen.add(key)
        if any(stage.get("limit_reason") == "interrupted"
               or stage.get("status") == "interrupted"
               for stage in row["stages"].values()):
            if index != len(rows) - 1:
                raise RuntimeError("Interrupted record is not last")
            interrupted.append(row)
        else:
            kept.append(row)
    return kept, interrupted


def resume_class(base):
    class ResumeCampaign(base.Campaign):
        def initialize(self):
            meta = base.read_json(self.out / "metadata.json")
            state = base.read_json(self.out / "progress.json")
            base.require(state["state"] in {"failed", "interrupted", "resuming"},
                         "Campaign is not stopped")
            base.require(meta["root"] == str(base.ROOT), "Project root differs")
            base.require(str(Path(sys.executable).resolve()) in meta["pins"],
                         "Launch with the original pinned Python interpreter")
            base.require(meta["policy"] == dict(workers=1, timeout=300, memory_mb=4096,
                                               max_rec_depth=4096, equivalence=False),
                         "Campaign policy differs")
            for pid in {meta["pid"], state["pid"]}:
                try:
                    os.kill(pid, 0)
                except ProcessLookupError:
                    pass
                else:
                    raise RuntimeError("Prior supervisor PID still exists: " + str(pid))
            self.started -= state["wall_seconds"]  # Accumulate active sessions, excluding downtime.
            self.session = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
            self.history = self.out / "resumptions" / self.session
            self.history.mkdir(parents=True)
            for name in ("progress.json", "report.md", "summary.json", "results.csv",
                         "results.jsonl", "failure.json", "guard.json", "runner.pid"):
                if (self.out / name).exists():
                    shutil.copy2(self.out / name, self.history / name)
            (self.out / "runner.pid").write_text(str(os.getpid()) + "\n")
            self.guard = subprocess.Popen(["/usr/bin/caffeinate", "-is", "-w", str(os.getpid())])
            for _ in range(20):
                try:
                    self.checkpoint()
                    break
                except RuntimeError:
                    time.sleep(0.1)
            self.checkpoint()
            self.event("resume_guard_verified", pid=self.guard.pid, session=self.session)
            self.sources, self.pins = meta["source_files"], dict(meta["pins"])
            self.dependencies = meta["dependencies"]
            self.lean_paths = [Path(p).resolve() for p in os.environ["LEAN_PATH"].split(os.pathsep) if p]
            self.lean = Path(base.output(["lean", "--print-prefix"])) / "bin/lean"
            self.translator = self.out / "snapshot/smt2lean"
            runner_name = base.RUNNERS[0].removesuffix(".py")
            self.runner = importlib.import_module(runner_name)
            base.require(Path(self.runner.__file__).resolve() == self.out / "snapshot" / (runner_name + ".py"),
                         "Runner is not the original snapshot")
            self.verify_pins()
            self.pin(Path(__file__), self.history / Path(__file__).name)
            worker = Path(__file__).with_name("translation.py")
            self.pin(worker, self.history / worker.name)
            self.resume_worker = self.history / worker.name
            corpus = self.out / "snapshot/corpus"
            self.archives = {a["archive"]: a for a in base.read_json(corpus / "sources.json")["archives"]}
            with (corpus / "inputs.csv").open(newline="") as stream:
                manifest = list(csv.DictReader(stream))
            self.expected = {}
            for archive, count in base.SCHEDULE:
                rows = [r for r in manifest if r["archive"] == "smt-queries/" + archive]
                base.require(len(rows) == count, "Archive count differs")
                parent = Path(os.path.commonpath([str(Path(r["archive_member"]).parent) for r in rows]))
                for row in rows:
                    row["output_relative"] = str(Path(row["archive_member"]).relative_to(parent).with_suffix(".lean"))
                    row["path"] = str(base.ROOT / "evaluation/extracted" /
                                      archive.removesuffix(".tar.gz") / row["archive_member"])
                    self.expected[(row["archive"], row["archive_member"])] = row
            plans, all_rows = [], []
            for archive, count in base.SCHEDULE:
                label = archive.removesuffix(".tar.gz")
                directory, generated = self.out / "archives" / label, self.args.generated / label
                if not directory.exists():
                    base.require(not generated.exists(), "Generated directory without records")
                    continue
                rows = read_rows(directory / "results.jsonl")
                kept, interrupted = partition_records(rows)
                for row in kept:
                    base.validate_record(row, self.expected, generated, self.runner, directory)
                    self.periodic_checkpoint()
                inputs = base.read_json(directory / "inputs.json")
                base.require(inputs == sorted([r for r in self.expected.values()
                    if r["archive"] == "smt-queries/" + archive], key=lambda r: r["archive_member"]),
                    "Archive input list differs")
                if (directory / "audit.json").exists():
                    audit = base.read_json(directory / "audit.json")
                    base.require(audit["state"] == "passed" and audit["records"] == count
                                 and audit["results_sha256"] == base.digest(directory / "results.jsonl")
                                 and len(kept) == count and not interrupted, "Completed audit differs")
                    self.completed.append(archive)
                existing = {p.resolve() for p in generated.rglob("*") if p.is_file()}
                possible = {(generated / r["output_relative"]).resolve() for r in inputs}
                base.require(existing <= possible, "Unexpected generated files")
                plans.append((label, directory, generated, kept, interrupted, existing))
                all_rows.extend(kept)
            keyed = {(r["archive"], r["archive_member"]): r for r in all_rows}
            for row in read_rows(self.out / "results.jsonl"):
                base.require(keyed.get((row["archive"], row["archive_member"])) == row,
                             "Previously aggregated result differs")
            for label, directory, generated, kept, interrupted, existing in plans:
                backup = self.history / "archives" / label
                backup.mkdir(parents=True)
                for name in ("progress.json", "summary.json", "results.csv", "results.jsonl",
                             "failure.json", "runner.pid"):
                    if (directory / name).exists():
                        shutil.copy2(directory / name, backup / name)
                outputs = {(base.ROOT / r["generated"]).resolve() for r in kept if r.get("generated")}
                for path in existing - outputs:
                    destination = backup / "interrupted-output" / path.relative_to(generated)
                    destination.parent.mkdir(parents=True, exist_ok=True)
                    path.rename(destination)
                if interrupted:
                    base.atomic_json(backup / "excluded-attempts.json", interrupted)
                    write_rows(directory / "results.jsonl", kept)
                    base.atomic_json(directory / "summary.json", self.runner.summarize(kept))
                (directory / "failure.json").unlink(missing_ok=True)
            self.records = all_rows
            write_rows(self.out / "results.jsonl", self.records)
            (self.out / "failure.json").unlink(missing_ok=True)
            base.atomic_json(self.history / "metadata.json", dict(
                started_utc=base.utc(), pid=os.getpid(), session=self.session,
                retained=len(self.records), policy=meta["policy"],
                original_metadata_sha256=base.digest(self.out / "metadata.json"),
                prior_active_seconds=state["wall_seconds"],
                timing="Per-stage timings unchanged; campaign wall_seconds excludes stopped intervals.",
                resume_scripts={name: base.digest(self.history / name)
                                for name in (Path(__file__).name, worker.name)}))
            self.event("campaign_resumed", retained=len(self.records),
                       remaining=sum(count for _, count in base.SCHEDULE) - len(self.records), session=self.session)
            self.progress("running")
            self.report("running")

        def run_archive(self, archive, count):
            if archive in self.completed:
                return
            label = archive.removesuffix(".tar.gz")
            directory, generated = self.out / "archives" / label, self.args.generated / label
            if not directory.exists():
                return super().run_archive(archive, count)
            self.verify_pins()
            self.checkpoint()
            seen = [(base.validate_record(row, self.expected, generated, self.runner, directory),
                     base.digest_bytes(line))
                    for line in (directory / "results.jsonl").read_bytes().splitlines()
                    for row in [json.loads(line)]]
            self.current = dict(archive=archive, total=count, completed=len(seen))
            command = [sys.executable, "-B", str(self.resume_worker),
                       "--resume-campaign", str(self.out), "--archive", archive, "--session", self.session]
            self.event("archive_resumed", archive=archive, retained=len(seen), command=command)
            Campaign.supervise_archive(self, directory, generated, seen, command,
                                       self.history / (label + ".log"), root=base.ROOT, resuming=True)
            Campaign.audit_archive(self, archive, count, directory, generated, seen,
                                   root=base.ROOT, runners=base.RUNNERS)

    return ResumeCampaign


def load_resume(out):
    """Use the saved environment and base implementation, including old campaigns."""
    meta = read_json(out / "metadata.json")
    require(Path(meta["arguments"]["out"]) == out, "Campaign location differs")
    for key, value in meta["environment"].items():
        if value is None:
            os.environ.pop(key, None)
        else:
            os.environ[key] = value
    os.environ["SMT2LEAN_PROJECT_ROOT"] = meta["root"]
    os.chdir(meta["root"])
    snapshot = out / "snapshot"
    if (snapshot / "campaign.py").exists():
        filenames = (*RUNNERS, "campaign.py")
        name = "campaign"
    else:
        filenames = ("evaluate_translation.py", "evaluation_metrics.py",
                     "evaluate_solvers.py", "evaluation_campaign.py")
        name = "evaluation_campaign"
    base = import_frozen(snapshot, filenames, meta["pins"])[name]
    require(str(base.ROOT) == meta["root"], "Project root differs")
    args = SimpleNamespace(**meta["arguments"])
    args.out = out
    args.generated, args.translator = Path(args.generated), Path(args.translator)
    return resume_class(base)(args), base.SCHEDULE


def run_campaign(campaign, schedule, resuming=False):
    """One lifecycle for fresh and resumed campaigns."""
    for sig in (signal.SIGINT, signal.SIGTERM):
        signal.signal(sig, lambda *_: setattr(campaign, "stopping", True))
    try:
        campaign.initialize()
        for archive, count in schedule:
            campaign.run_archive(archive, count)
        campaign.report("complete")
        campaign.progress("complete")
        campaign.event("campaign_complete", records=len(campaign.records))
        return 0
    except Exception as exc:
        # A rejected resume must not modify an active or completed campaign.
        if campaign.out.exists() and (not resuming or hasattr(campaign, "history")):
            atomic_json(campaign.out / "failure.json",
                        dict(utc=utc(), error=repr(exc), current=campaign.current))
            campaign.event("campaign_stopped", error=repr(exc))
            if not resuming or hasattr(campaign, "runner") and campaign.records:
                campaign.progress("failed")
                if hasattr(campaign, "runner"):
                    campaign.report("failed")
        else:
            print(str(exc), file=sys.stderr)
        return 1
    finally:
        campaign.close()


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--resume", action="store_true", help="Resume this campaign's frozen environment")
    parser.add_argument("--generated", type=Path)
    parser.add_argument("--translator", type=Path)
    parser.add_argument("--cloc")
    parser.add_argument("--min-free-gib", type=float)
    arguments = list(sys.argv[1:] if argv is None else argv)
    args = parser.parse_args(arguments)
    args.out = args.out.resolve()
    if args.resume:
        if any(value is not None for value in
               (args.generated, args.translator, args.cloc, args.min_free_gib)):
            parser.error("--resume uses saved settings; supply only --out")
        with (args.out / ".resume.lock").open("a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            campaign, schedule = load_resume(args.out)
            return run_campaign(campaign, schedule, resuming=True)
    if args.generated is None:
        parser.error("a fresh campaign requires --generated")
    args.generated = args.generated.resolve()
    args.translator = (args.translator or ROOT / ".lake/build/bin/smt2lean").resolve()
    args.cloc = args.cloc or shutil.which("cloc")
    args.min_free_gib = 10 if args.min_free_gib is None else args.min_free_gib
    if args.out.exists() or args.generated.exists() or args.out == args.generated:
        parser.error("Campaign and generated directories must be distinct and new")
    if not args.cloc or args.min_free_gib < 10:
        parser.error("cloc and at least 10 GiB minimum free space are required")
    args.cloc = str(Path(args.cloc).resolve())
    if not os.environ.get("LEAN_PATH"):
        lake = shutil.which("lake")
        if not lake:
            parser.error("Run with lake env or supply a valid LEAN_PATH")
        os.chdir(ROOT)
        os.execv(lake, [lake, "env", sys.executable, str(Path(__file__).resolve()), *arguments])
    del args.resume
    os.chdir(ROOT)
    return run_campaign(Campaign(args), SCHEDULE)


if __name__ == "__main__":
    sys.exit(main())

