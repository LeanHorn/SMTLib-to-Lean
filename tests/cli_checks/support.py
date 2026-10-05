"""Shared subprocess and generated-file checks for the CLI regressions."""

from pathlib import Path
import os
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
EXE = ROOT / ".lake/build/bin/smt2lean"
FIXTURES = ROOT / "tests/translation/bool"
INTEGERS = ROOT / "tests/translation/int"
FUNCTIONS = ROOT / "tests/translation/functions"
QUANTIFIERS = ROOT / "tests/translation/quantifiers"
BINDINGS = ROOT / "tests/translation/bindings"
CHC = ROOT / "tests/translation/chc"
SESSIONS = ROOT / "tests/translation/sessions"
SOLVER_OPTIONS = """(set-option :produce-models true)
(set-option :produce-proofs true)
(set-option :produce-unsat-cores true)
(set-option :print-success true)
(set-option :random-seed 42)
(set-option :smt.mbqi false)
(set-option :auto-config false)
(set-option :model true)
"""


def run(*args, code=0):
    args = [arg.relative_to(ROOT) if isinstance(arg, Path) and arg.is_relative_to(ROOT)
            else arg for arg in args]
    result = subprocess.run(
        [str(EXE), *map(str, args)], cwd=ROOT, capture_output=True, text=True
    )
    assert result.returncode == code, (args, result.returncode, result.stdout, result.stderr)
    if code:
        assert result.stderr and not result.stdout, result
    return result


def without_sources(text):
    """Metadata and filenames may move locations, but must not change Lean code."""
    return "".join(line for line in text.splitlines(keepends=True)
                   if not line.startswith("-- Source: "))


def check_lean(lean, source, *, complete=False):
    args = [str(lean)]
    if complete:
        args.append("-DwarningAsError=true")
    # Core-only files must remain independent of all project packages.
    search_path = str(source.parent)
    if any(line.startswith("import Mathlib.") for line in source.read_text().splitlines()):
        search_path += os.pathsep + os.environ["LEAN_PATH"]
    result = subprocess.run(
        [*args, source.name], cwd=source.parent,
        env=dict(os.environ, LEAN_PATH=search_path),
        capture_output=True, text=True,
    )
    assert result.returncode == 0, (source, result.stdout, result.stderr)
    return result.stdout


def check_generated(lean, output, *, goal="Refutation", count=1):
    assert [p.name for p in output.iterdir()] == ["Query.lean"]
    query = output / "Query.lean"
    source = query.read_text()
    statements, proofs = source.split("-- Proofs\n", 1)
    assert statements.count("-- Statements") == 1
    assert "-- Source: " in statements
    assert "sorry" not in statements and "by\n  sorry" in proofs
    assert proofs.count("theorem ") == count and "def " not in proofs
    assert statements.count(f"def {goal}") == count
    for number in range(1, count + 1):
        name = goal if count == 1 else f"{goal}_{number}"
        assert f"def {name} : Prop" in statements
        assert f"theorem {name.lower()} : {name}" in proofs
        if count > 1:
            assert re.search(rf"\(query {number}: check-sat(?:-assuming)?,", statements)
    check_lean(lean, query)
    # The statement must also compile after removing the unfinished proof entirely.
    standalone = output / "StatementsOnly.lean"
    standalone.write_text(statements)
    check_lean(lean, standalone)
    standalone.unlink()
    return source

