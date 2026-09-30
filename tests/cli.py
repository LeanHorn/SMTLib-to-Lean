"""Run with `lake env python3 tests/cli.py` after `lake build smt2lean`."""

from pathlib import Path
import os
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / ".lake/build/bin/smt2lean"
FIXTURES = ROOT / "tests/translation/bool"
INTEGERS = ROOT / "tests/translation/int"
FUNCTIONS = ROOT / "tests/translation/functions"
QUANTIFIERS = ROOT / "tests/translation/quantifiers"
BINDINGS = ROOT / "tests/translation/bindings"
CHC = ROOT / "tests/translation/chc"


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
    result = subprocess.run(
        [*args, source.name], cwd=source.parent,
        env=dict(os.environ, LEAN_PATH=str(source.parent)),
        capture_output=True, text=True,
    )
    assert result.returncode == 0, (source, result.stdout, result.stderr)
    return result.stdout


def check_generated(lean, output, *, goal="Refutation"):
    assert [p.name for p in output.iterdir()] == ["Query.lean"]
    query = output / "Query.lean"
    source = query.read_text()
    statements, proofs = source.split("-- Proofs\n", 1)
    assert "-- Statements" in statements and f"def {goal} : Prop" in statements
    assert "-- Source: " in statements
    assert f"theorem {goal.lower()} : {goal}" in proofs
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
        "congruence": (FUNCTIONS / "expected/Query.lean").read_text(),
        "quantified": (QUANTIFIERS / "expected/Query.lean").read_text(),
        "lh_sum_rec": (CHC / "expected/Query.lean").read_text(),
    }
    help_text = run("--help").stdout
    assert all(word in help_text for word in ["Usage:", "HORN", "Problem", "Refutation"])
    for args in [(), ("--unknown",), ("input.smt2",),
                 ("input.smt2", "--out", ""), ("input.smt2", "--out", "--help")]:
        run(*args, code=2)

    with tempfile.TemporaryDirectory(prefix="smt2lean cli ") as temporary:
        tmp = Path(temporary)
        inputs = [FIXTURES / f"{name}.smt2" for name in ["contradiction", "connectives", "empty"]]
        inputs += [INTEGERS / f"{name}.smt2" for name in ["literals", "arithmetic", "bounds"]]
        inputs += [FUNCTIONS / f"{name}.smt2" for name in ["applications", "congruence"]]
        inputs += [QUANTIFIERS / f"{name}.smt2" for name in ["scopes", "quantified", "hints"]]
        inputs += [BINDINGS / name for name in ["simultaneous.smt2", "definitions.smt2", "named.smt2"]]
        for fixture in inputs:
            name = fixture.stem
            output = tmp / name
            result = run(fixture, "--out", output)
            assert "Proof unfinished" in result.stdout
            source = check_generated(lean, output)
            if name == "named":
                assert '(:named "positive")' in source and '(:named "same body")' in source
                assert '(:named "line\\nname", "also")' in source
                assert "\nname" not in source
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
            (FUNCTIONS / "congruence.smt2", "  intro f x y h\n  exact h.2 (congrArg f h.1)\n"),
            (QUANTIFIERS / "quantified.smt2", "  intro P h\n  exact h.2.elim (fun x hx => hx (h.1 x))\n"),
        ]:
            name = fixture.stem
            for status in ["sat", "unsat", "unknown"]:
                source, output = tmp / f"{name}-{status}.smt2", tmp / f"{name}-{status}"
                source.write_text(f"(set-info :status {status})\n" + fixture.read_text())
                run(source, "--out", output)
                generated = check_generated(lean, output)
                assert without_sources(generated) == without_sources(expected[name]), f"{name}: {status} changed the target"

            # Replace the Proofs section exactly as in the README.
            completed = tmp / name / "Query.lean"
            statements = completed.read_text().split("-- Proofs\n", 1)[0]
            finished = statements + "-- Proofs\n\ntheorem refutation : Refutation := by\n" + proof
            completed.write_text(finished + "\n#print axioms refutation\n")
            axioms = check_lean(lean, completed, complete=True)
            assert "sorryAx" not in axioms, axioms
            if name == "bounds":
                # This core integer-order lemma uses propositional extensionality.
                assert "depends on axioms: [propext]" in axioms
            else:
                assert "does not depend on any axioms" in axioms
            saved = completed.read_text()
            run(fixture, "--out", completed.parent, code=1)
            assert completed.read_text() == saved

        # Quantifier hints must leave the entire emitted proposition unchanged.
        source, output = tmp / "quantified-hinted.smt2", tmp / "quantified-hinted"
        text = (QUANTIFIERS / "quantified.smt2").read_text()
        text = text.replace("(forall ((x Int)) (P x))",
                            "(forall ((x Int)) (! (P x) :pattern ((P x)) :qid universal))")
        text = text.replace("(exists ((x Int)) (not (P x)))",
                            "(exists ((x Int)) (! (not (P x)) :no-pattern (P x) :qid witness))")
        source.write_text(text)
        run(source, "--out", output)
        generated = check_generated(lean, output)
        assert without_sources(generated) == without_sources(expected["quantified"])

        missing_output = tmp / "missing-output"
        run(tmp / "missing.smt2", "--out", missing_output, code=1)
        assert not missing_output.exists()

        horn = ROOT / "tests/chc/lh_sum_rec.smt2"
        horn_output = tmp / "horn"
        run(horn, "--out", horn_output)
        horn_source = check_generated(lean, horn_output, goal="Problem")
        assert horn_source == expected["lh_sum_rec"], "lh_sum_rec output changed"
        assert horn_source.count("(clause ") == 3
        horn_text = horn.read_text()
        for status in [None, "unsat", "unknown"]:
            source, output = tmp / f"horn-{status}.smt2", tmp / f"horn-{status}"
            metadata = "" if status is None else f"(set-info :status {status})"
            source.write_text(horn_text.replace("(set-info :status sat)", metadata))
            run(source, "--out", output)
            generated = check_generated(lean, output, goal="Problem")
            assert without_sources(generated) == without_sources(horn_source), status

        output = tmp / "combined-chc"
        run(CHC / "clauses.smt2", "--out", output)
        combined = check_generated(lean, output, goal="Problem")
        assert combined.count("(clause ") == 16

        output = tmp / "definitions-chc"
        run(CHC / "definitions.smt2", "--out", output)
        generated = check_generated(lean, output, goal="Problem")
        assert generated.count("(clause ") == 3
        assert all(f'(:named "{name}")' in generated for name in ["entry clause", "step", "safety"])

        source, output = tmp / "hinted-chc.smt2", tmp / "hinted-chc"
        text = (CHC / "definitions.smt2").read_text()
        text = text.replace("(=> |entry clause| (rule x b))",
                            "(! (=> |entry clause| (rule x b)) :pattern ((P x) (R x b)) "
                            ":no-pattern (P (div x 2)) :qid step)")
        text = text.replace("(=> (bad x b) false)",
                            "(! (=> (bad x b) false) :pattern ((R x b)) :qid safety)")
        source.write_text(text)
        run(source, "--out", output)
        hinted = check_generated(lean, output, goal="Problem")
        assert without_sources(hinted) == without_sources(generated)

        query = horn_output / "Query.lean"
        edited = horn_source + "\n-- User CHC proof work.\n"
        query.write_text(edited)
        result = run(horn, "--out", horn_output, code=1)
        assert "output already exists" in result.stderr and query.read_text() == edited

        # Equivalent parsed logic with comments/whitespace; no clauses means True.
        source, output = tmp / "empty-horn.smt2", tmp / "empty-horn"
        source.write_text("(set-logic ; parsed as HORN\n HORN)\n(check-sat)")
        run(source, "--out", output)
        empty_horn = check_generated(lean, output, goal="Problem")
        assert "def Problem : Prop :=\n  True\n" in empty_horn

        # The same assertions follow the SMT path without an explicit HORN logic.
        smt_source = None
        for logic in ["(set-logic ALL)", ""]:
            name = "horn-as-smt" if logic else "horn-no-logic"
            source, output = tmp / f"{name}.smt2", tmp / name
            source.write_text(horn_text.replace("(set-logic HORN)", logic))
            run(source, "--out", output)
            generated = check_generated(lean, output)
            if smt_source is not None:
                assert without_sources(generated) == without_sources(smt_source)
            smt_source = generated

        # HORN text in comments, names, and metadata must never select CHC mode.
        source, output = tmp / "horn-text.smt2", tmp / "horn-text"
        source.write_text('''; (set-logic HORN)
(set-info :source "(set-logic HORN)")
(set-logic ALL)
(declare-const |(set-logic HORN)| Int)
(assert (= |(set-logic HORN)| 0))
(check-sat)
(set-info :status sat)
''')
        run(source, "--out", output)
        check_generated(lean, output)

        horn_prefix = "(set-logic HORN)\n(declare-fun P (Int) Bool)\n(assert (P 0))\n"
        for name, text, location, reason in [
            ("later-clause", horn_prefix +
             "(assert (forall ((x Int)) (=> (not (P x)) false)))\n(check-sat)",
             "4:1: query 1: command 4: clause 2:", "CHC relation inside a theory guard"),
            ("later-operator", horn_prefix +
             "(assert (forall ((x Int)) (=> (= (div x 2) 0) (P x))))\n(check-sat)",
             "4:1: query 1: command 4: clause 2:", "unsupported operator"),
            ("let-operator", horn_prefix +
             "(assert (forall ((x Int)) (let ((half (div x 2))) (=> (= half 0) (P x)))))\n(check-sat)",
             "4:1: query 1: command 4: clause 2:", "unsupported operator"),
            ("let-relation", horn_prefix +
             "(assert (forall ((x Int)) (let ((hidden (not (P x)))) (=> hidden (P x)))))\n(check-sat)",
             "4:1: query 1: command 4: clause 2:", "CHC relation inside a theory guard"),
            ("defined-negative-relation", horn_prefix +
             "(define-fun neg ((x Int)) Bool (not (P x)))\n"
             "(assert (forall ((x Int)) (=> (neg x) false)))\n(check-sat)",
             "5:1: query 1: command 5: clause 2:", "CHC relation inside a theory guard"),
            ("defined-quantifier", horn_prefix +
             "(define-fun someP () Bool (exists ((x Int)) (P x)))\n"
             "(assert (=> someP false))\n(check-sat)",
             "5:1: query 1: command 5: clause 2:", "quantifier"),
            ("unused-definition", horn_prefix +
             "(define-fun bad () Int (div 1 0))\n(check-sat)",
             "4:1: query 1: command 4:", "INTS_DIVISION"),
            ("named-clause", horn_prefix +
             '(assert (! (forall ((x Int)) (=> (not (P x)) false)) :named |bad clause|))\n(check-sat)',
             '4:1: query 1: command 4 (:named "bad clause"): clause 2:', "CHC relation inside a theory guard"),
            ("hinted-clause", horn_prefix +
             '(assert (forall ((x Int)) (! (=> (not (P x)) false) :pattern ((P x)) :qid bad)))\n(check-sat)',
             "4:1: query 1: command 4: clause 2:", "CHC relation inside a theory guard"),
            ("global-int", "(set-logic HORN)\n(declare-const x Int)\n(check-sat)",
             "2:1: query 1: command 2:", "unsupported CHC declaration"),
            ("malformed-tail", horn_prefix + "(check-sat)\n(assert",
             "5:8: query 1: command 5:", "unterminated command"),
            ("missing-check", horn_prefix, "4:1: query 1: command 4:", "expected one check-sat"),
        ]:
            source, output = tmp / f"horn-{name}.smt2", tmp / f"horn-{name}"
            source.write_text(text)
            result = run(source, "--out", output, code=1)
            # cvc5 renders its diagnostic message as an escaped string.
            escaped_location = location.replace('"', '\\"')
            assert f"{source}:{escaped_location}" in result.stderr, result.stderr
            assert reason in result.stderr, result.stderr
            assert not output.exists()

        invalid = [
            "(set-logic QF_LRA)\n(check-sat)",
            "(set-logic QF_UF)\n(check-sat)\n(check-sat)",
            "(set-logic QF_UF)\n(check-sat)\n(assert",
            "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (= (div x 0) 0))\n(check-sat)",
            "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (= (mod x 0) 0))\n(check-sat)",
            "(set-logic ALL)\n(declare-fun P (Real) Bool)\n(check-sat)",
            "(set-logic QF_UFLIA)\n(declare-fun f (Int Int) Int)\n(assert (= (f 1) 0))\n(check-sat)",
            "(set-logic QF_UFLIA)\n(declare-fun f (Int) Int)\n(assert (= (f true) 0))\n(check-sat)",
            "(set-logic ALL)\n(assert (forall ((x Real)) true))\n(check-sat)",
            "(set-logic QF_LIA)\n(assert (forall ((x Int)) (> x 0)))\n(check-sat)",
            "(set-logic ALL)\n(assert (exists ((p Bool)) (= (ite p 1 (div 1 0)) 1)))\n(check-sat)",
            "(set-logic ALL)\n(assert (ite 1 true false))\n(check-sat)",
            "(set-logic ALL)\n(assert (ite true false 1))\n(check-sat)",
            "(set-logic QF_LIA)\n(assert (let ((x 1) (y x)) (= y 1)))\n(check-sat)",
            "(set-logic QF_UF)\n(assert (let ((p true) (q p)) q))\n(check-sat)",
            "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (let ((half (div x 2))) (let ((copy half)) (= copy 0))))\n(check-sat)",
            "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (let ((next (+ x 1))) (= (mod next 2) 0)))\n(check-sat)",
            "(set-logic UFLIA)\n(declare-fun P (Int) Bool)\n(assert (forall ((x Int)) (! (P x) :weight 5)))\n(check-sat)",
        ]
        for index, text in enumerate(invalid):
            source, output = tmp / f"invalid-{index}.smt2", tmp / f"invalid-{index}"
            source.write_text(text)
            result = run(source, "--out", output, code=1)
            assert re.search(re.escape(str(source)) + r":\d+:\d+: command ", result.stderr), result.stderr
            assert not output.exists()

        # Quoted names and doubled quotes cannot move source boundaries. Keep CRLF bytes.
        source, output = tmp / "locations\n-- name.smt2", tmp / "locations"
        text = ('; λ ignored )\r\n(set-logic QF_UF)\r\n'
                '(set-info :source "(; ""quoted"")")\r\n'
                '(declare-const |p (;)| Bool)\r\n'
                '(assert\r\n  |p (;)|)\r\n(check-sat)')
        source.write_bytes(text.encode())
        run(source, "--out", output)
        generated = check_generated(lean, output)
        assert '\\n-- name.smt2":5:1-6:11 (assertion 1, command 4)' in generated
        # Move the same assertion and ensure only provenance changes.
        shifted, shifted_output = tmp / "shifted.smt2", tmp / "shifted"
        shifted.write_bytes(('\n\n' + text).encode())
        run(shifted, "--out", shifted_output)
        shifted_code = check_generated(lean, shifted_output)
        assert '":7:1-8:11 (assertion 1, command 4)' in shifted_code
        assert without_sources(shifted_code) == without_sources(generated)
        for name, text, location, reason in [
            ("multiline", "; λ\n(set-logic ALL)\n  (assert\n    (= (div 1 0) 0))\n(check-sat)",
             "3:3: command 2:", "unsupported operator"),
            ("definition-source", "; λ\n(set-logic ALL)\n  (define-fun bad ((x Int)) Int\n    (div x 2))\n(check-sat)",
             "3:3: command 2:", "INTS_DIVISION"),
            ("named-source", '(set-logic ALL)\n  (assert (! (= (div 1 0) 0) :named |bad body|))\n(check-sat)',
             '2:3: command 2 (:named "bad body"):', "INTS_DIVISION"),
            ("unused-named-source", '(set-logic ALL)\n  (assert (let ((ignored (! (div 1 0) :named |unused body|))) true))\n(check-sat)',
             '2:3: command 2 (:named "unused body"):', "INTS_DIVISION"),
            ("alias-source", "(set-logic ALL)\n  (define-sort Bad () Real)\n(check-sat)",
             "2:3: command 2:", "unsupported sort alias"),
            ("bad-string", '(set-logic QF_UF)\n(set-info :source "unfinished',
             "2:30: command 2:", "unterminated string"),
            ("extra-close", "(set-logic QF_UF)\n(check-sat)\n  )",
             "3:3: command 3:", "expected '('"),
        ]:
            source, output = tmp / f"{name}.smt2", tmp / name
            source.write_text(text)
            result = run(source, "--out", output, code=1)
            # cvc5 renders its diagnostic message as an escaped string.
            escaped_location = location.replace('"', '\\"')
            assert f"{source}:{escaped_location}" in result.stderr, result.stderr
            assert reason in result.stderr and not output.exists(), result.stderr

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
    print("Demo passed: 32 SMT and 8 CHC standalone translations, source locations, and 4 completed proofs")


if __name__ == "__main__":
    main()
