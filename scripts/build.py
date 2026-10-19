#!/usr/bin/env python3
"""Build with the checked-in ownership fix for the pinned cvc5 dependency."""
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
CVC5_REVISION = "7e3365990661b697ccb30e92d6912f4cc6589322"


def patch_cvc5():
    dependency = ROOT / ".lake/packages/cvc5"
    revision = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=dependency, text=True).strip()
    if revision != CVC5_REVISION:
        raise RuntimeError("cvc5 revision changed; review the ownership patch before building")
    patch = ROOT / "patches/cvc5-owned-arguments.patch"
    command = ["git", "apply", "--whitespace=nowarn"]
    applied = subprocess.run([*command, "--reverse", "--check", str(patch)],
                             cwd=dependency, capture_output=True)
    if applied.returncode == 0:
        return
    # Check every hunk before changing anything; never discard local modifications.
    subprocess.run([*command, "--check", str(patch)], cwd=dependency, check=True)
    subprocess.run([*command, str(patch)], cwd=dependency, check=True)
    print("Applied cvc5 term/sort ownership fix", flush=True)


def main():
    # Materialize the locked dependencies, including on a fresh checkout, without updating them.
    subprocess.run(["lake", "env", "true"], cwd=ROOT, check=True)
    patch_cvc5()
    return subprocess.run(["lake", "build", *sys.argv[1:]], cwd=ROOT).returncode


if __name__ == "__main__":
    raise SystemExit(main())
