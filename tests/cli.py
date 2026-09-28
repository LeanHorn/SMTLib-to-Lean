"""Run with `lake env python3 tests/cli.py` after `lake build smt2lean`."""

from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / ".lake/build/bin/smt2lean"
FIXTURES = ROOT / "tests/translation/bool"


def run(*args, code=0):
    result = subprocess.run(
        [str(EXE), *map(str, args)], cwd=ROOT, capture_output=True, text=True
    )
    assert result.returncode == code, (args, result.returncode, result.stdout, result.stderr)
    if code:
        assert result.stderr and not result.stdout, result
    return result


def main():
    assert "Usage:" in run("--help").stdout
    for args in [(), ("--unknown",), ("input.smt2",),
                 ("input.smt2", "--out", ""), ("input.smt2", "--out", "--help")]:
        run(*args, code=2)

    with tempfile.TemporaryDirectory(prefix="smt2lean cli ") as temporary:
        tmp = Path(temporary)
        for name in ["contradiction", "connectives", "empty"]:
            output = tmp / name
            result = run(FIXTURES / f"{name}.smt2", "--out", output)
            assert "Proof unfinished" in result.stdout
            assert sorted(p.name for p in output.iterdir()) == ["Proofs.lean", "Statements.lean"]
            statement = (output / "Statements.lean").read_text()
            assert "sorry" not in statement
            proof = output / "Proofs.lean"
            assert "by\n  sorry" in proof.read_text()
            edited = proof.read_text() + "\n-- User proof work.\n"
            proof.write_text(edited)
            result = run(FIXTURES / f"{name}.smt2", "--out", output, code=1)
            assert "output already exists" in result.stderr
            assert proof.read_text() == edited
            assert (output / "Statements.lean").read_text() == statement

        missing_output = tmp / "missing-output"
        run(tmp / "missing.smt2", "--out", missing_output, code=1)
        assert not missing_output.exists()

        invalid = [
            "(set-logic HORN)\n(check-sat)",
            "(set-logic QF_UF)\n(check-sat)\n(check-sat)",
            "(set-logic QF_UF)\n(check-sat)\n(assert",
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


if __name__ == "__main__":
    main()
