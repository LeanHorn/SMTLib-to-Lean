"""Run with `lake env python3 tests/cli.py` after `lake build smt2lean`."""

from pathlib import Path
import os
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / ".lake/build/bin/smt2lean"
FIXTURES = ROOT / "tests/translation/bool"
INTEGERS = ROOT / "tests/translation/int"


def run(*args, code=0):
    result = subprocess.run(
        [str(EXE), *map(str, args)], cwd=ROOT, capture_output=True, text=True
    )
    assert result.returncode == code, (args, result.returncode, result.stdout, result.stderr)
    if code:
        assert result.stderr and not result.stdout, result
    return result


def check_lean(lean, source, *, complete=False):
    args = [str(lean)]
    if complete:
        args.append("-DwarningAsError=true")
    result = subprocess.run(
        [*args, source.name], cwd=source.parent,
        env=dict(os.environ, LEAN_PATH=str(source.parent)),
        capture_output=True, text=True,
    )
    assert result.returncode == 0, (source, result.stdout, result.stderr)
    return result.stdout


def check_generated(lean, output):
    assert [p.name for p in output.iterdir()] == ["Query.lean"]
    query = output / "Query.lean"
    source = query.read_text()
    statements, proofs = source.split("-- Proofs\n", 1)
    assert "-- Statements" in statements and "def Refutation" in statements
    assert "sorry" not in statements and "by\n  sorry" in proofs
    check_lean(lean, query)
    # The statement must also compile after removing the unfinished proof entirely.
    standalone = output / "StatementsOnly.lean"
    standalone.write_text(statements)
    check_lean(lean, standalone)
    standalone.unlink()
    return source


def main():
    prefix = subprocess.check_output(["lean", "--print-prefix"], cwd=ROOT, text=True).strip()
    lean = Path(prefix) / "bin/lean"
    expected = {
        "contradiction": (FIXTURES / "expected/Query.lean").read_text(),
        "bounds": (INTEGERS / "expected/Query.lean").read_text(),
    }
    assert "Usage:" in run("--help").stdout
    for args in [(), ("--unknown",), ("input.smt2",),
                 ("input.smt2", "--out", ""), ("input.smt2", "--out", "--help")]:
        run(*args, code=2)

    with tempfile.TemporaryDirectory(prefix="smt2lean cli ") as temporary:
        tmp = Path(temporary)
        inputs = [FIXTURES / f"{name}.smt2" for name in ["contradiction", "connectives", "empty"]]
        inputs += [INTEGERS / f"{name}.smt2" for name in ["literals", "arithmetic", "bounds"]]
        inputs += [ROOT / "tests/translation/functions/applications.smt2"]
        for fixture in inputs:
            name = fixture.stem
            output = tmp / name
            result = run(fixture, "--out", output)
            assert "Proof unfinished" in result.stdout
            source = check_generated(lean, output)
            if name in expected:
                assert source == expected[name], (f"{name} output changed", source)
            if name in ["literals", "arithmetic"]:
                assert "340282366920938463463374607431768211457" in source
            query = output / "Query.lean"
            edited = source + "\n-- User proof work.\n"
            query.write_text(edited)
            result = run(fixture, "--out", output, code=1)
            assert "output already exists" in result.stderr
            assert query.read_text() == edited

        for fixture, proof in [
            (FIXTURES / "contradiction.smt2", "  intro p h\n  exact h.2 h.1\n"),
            (INTEGERS / "bounds.smt2", "  intro x h\n  exact Int.not_lt_of_ge h.1 h.2\n"),
        ]:
            name = fixture.stem
            for status in ["sat", "unsat", "unknown"]:
                source, output = tmp / f"{name}-{status}.smt2", tmp / f"{name}-{status}"
                source.write_text(f"(set-info :status {status})\n" + fixture.read_text())
                run(source, "--out", output)
                assert check_generated(lean, output) == expected[name], f"{name}: {status} changed the target"

            # Replace the Proofs section exactly as in the README.
            completed = tmp / name / "Query.lean"
            statements = completed.read_text().split("-- Proofs\n", 1)[0]
            finished = statements + "-- Proofs\n\ntheorem refutation : Refutation := by\n" + proof
            completed.write_text(finished + "\n#print axioms refutation\n")
            axioms = check_lean(lean, completed, complete=True)
            assert "sorryAx" not in axioms, axioms
            if name == "contradiction":
                assert "does not depend on any axioms" in axioms
            else:
                # This core integer-order lemma uses propositional extensionality.
                assert "depends on axioms: [propext]" in axioms
            saved = completed.read_text()
            run(fixture, "--out", completed.parent, code=1)
            assert completed.read_text() == saved

        missing_output = tmp / "missing-output"
        run(tmp / "missing.smt2", "--out", missing_output, code=1)
        assert not missing_output.exists()

        invalid = [
            "(set-logic HORN)\n(check-sat)",
            "(set-logic QF_UF)\n(check-sat)\n(check-sat)",
            "(set-logic QF_UF)\n(check-sat)\n(assert",
            "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (= (div x 0) 0))\n(check-sat)",
            "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (= (mod x 0) 0))\n(check-sat)",
            "(set-logic ALL)\n(declare-fun P (Int) Bool)\n(check-sat)",
            "(set-logic QF_UFLIA)\n(declare-fun f (Int Int) Int)\n(assert (= (f 1) 0))\n(check-sat)",
            "(set-logic QF_UFLIA)\n(declare-fun f (Int) Int)\n(assert (= (f true) 0))\n(check-sat)",
        ]
        for index, text in enumerate(invalid):
            source, output = tmp / f"invalid-{index}.smt2", tmp / f"invalid-{index}"
            source.write_text(text)
            result = run(source, "--out", output, code=1)
            assert str(source) in result.stderr and "command" in result.stderr
            assert not output.exists()

        # Existing empty directories, files, and symlinks must also be refused.
        empty_dir, occupied_file, link = tmp / "existing", tmp / "file", tmp / "link"
        empty_dir.mkdir()
        occupied_file.write_text("keep")
        link.symlink_to(tmp / "absent")
        for output in [empty_dir, occupied_file, link]:
            run(FIXTURES / "contradiction.smt2", "--out", output, code=1)
        assert not list(empty_dir.iterdir())
        assert occupied_file.read_text() == "keep" and link.is_symlink()

        output = tmp / "missing-parent" / "output"
        run(FIXTURES / "contradiction.smt2", "--out", output, code=1)
        assert not output.exists()

    print("CLI passed: generation, exit codes, diagnostics, and output protection")
    print("Demo passed: expected outputs, 13 standalone translations, metadata, and 2 completed proofs")


if __name__ == "__main__":
    main()
