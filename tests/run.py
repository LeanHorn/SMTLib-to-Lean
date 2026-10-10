"""Run independent regression groups concurrently, after building all targets."""

import argparse
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import shlex
import shutil
import subprocess
import sys
import tempfile
import time

from cli import GROUPS
from cli_checks.support import ROOT


def checks():
    # Start the larger groups early; split testTranslation at its existing boundaries.
    result = {
        f"translation-{group}": [".lake/build/bin/testTranslation", group]
        for group in ("arithmetic", "scopes", "bitvectors", "bindings", "horn", "core")
    }
    result.update({f"cli-{group}": [sys.executable, "tests/cli.py", group]
                   for group in GROUPS})
    result.update({target: [f".lake/build/bin/{target}"] for target in
                   ("testSource", "testParser", "testReconstruction", "testHorn", "testArrays", "testModels")})
    result["runner-policy"] = [sys.executable, "tests/cli_selection.py"]
    result["anchor"] = [sys.executable, "tests/anchor.py"]
    return result


def run_check(item, directory):
    name, command = item
    started = time.perf_counter()
    log = directory / f"{name}.log"
    with log.open("w") as output:
        try:
            code = subprocess.run(command, cwd=ROOT, stdout=output,
                                  stderr=subprocess.STDOUT).returncode
        except OSError as error:
            output.write(str(error) + "\n")
            code = 1
    status = "PASS" if code == 0 else "FAIL"
    print(f"{status} {name} ({time.perf_counter() - started:.2f}s)", flush=True)
    if code:
        print(f"Log: {log}\nRerun: cd {shlex.quote(str(ROOT))} && "
              f"lake env {shlex.join(command)}", flush=True)
    return code


def main(argv=None):
    available = checks()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("groups", nargs="*", help="selected groups; default: all")
    parser.add_argument("--jobs", type=int, default=4, help="concurrent groups (default: 4)")
    parser.add_argument("--list", action="store_true", help="list groups without running")
    args = parser.parse_args(argv)
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    if unknown := set(args.groups) - available.keys():
        parser.error("unknown groups: " + ", ".join(sorted(unknown)))
    if args.list:
        print("\n".join(available))
        return 0
    selected = {name: available[name] for name in (args.groups or available)}
    directory = Path(tempfile.mkdtemp(prefix="smt2lean suite "))
    print(f"Running {len(selected)} groups with {args.jobs} workers; logs: {directory}", flush=True)
    started = time.perf_counter()
    # Workers start subprocesses; each CLI subprocess owns its own temporary files.
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        codes = list(pool.map(lambda item: run_check(item, directory), selected.items()))
    if any(codes):
        print(f"Suite failed; logs retained: {directory}", flush=True)
        return 1
    shutil.rmtree(directory)
    print(f"All {len(selected)} groups passed ({time.perf_counter() - started:.2f}s)", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
