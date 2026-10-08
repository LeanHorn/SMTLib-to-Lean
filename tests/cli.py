"""Run with `lake env python3 tests/cli.py` after `lake build smt2lean`."""

from pathlib import Path
import re
import subprocess
import tempfile
from cli_checks.support import (ROOT, FIXTURES, INTEGERS, FUNCTIONS, QUANTIFIERS, BINDINGS, CHC, SESSIONS, SOLVER_OPTIONS, run, without_sources, check_lean, check_generated)

from cli_checks.sessions import (check_resets, check_uninterpreted_sorts)
from cli_checks.arithmetic import (check_integer_division, check_reals, check_conversions)
from cli_checks.bitvec import (check_bitvectors, check_bitvector_widths, check_bitvector_shifts, check_bitvector_division, check_bitvector_conversions)
from cli_checks.datatypes import check_datatypes
from cli_checks.arrays import (check_arrays_basic, check_arrays_extended, check_array_sharing)


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
    assert all(word in help_text for word in ["Usage:", "HORN", "Problem", "Refutation", "--max-rec-depth", "4096"])
    for args in [(), ("--unknown",), ("input.smt2",),
                 ("input.smt2", "--out", ""), ("input.smt2", "--out", "--help")]:
        run(*args, code=2)

    with tempfile.TemporaryDirectory(prefix="smt2lean cli ") as temporary:
        tmp = Path(temporary)
        fixture = FIXTURES / "contradiction.smt2"
        for depth in ["0", "-1", "bad", "1.5", ""]:
            output = tmp / "invalid-depth"
            run(fixture, "--out", output, "--max-rec-depth", depth, code=2)
            assert not output.exists()
        run(fixture, "--out", tmp / "missing-depth", "--max-rec-depth", code=2)
        for index, options in enumerate([
            ["--out", tmp / "depth-after", "--max-rec-depth", "8192"],
            ["--max-rec-depth", "8192", "--out", tmp / "depth-before"],
        ]):
            run(fixture, *options)
            output = tmp / ("depth-after" if index == 0 else "depth-before")
            generated = check_generated(lean, output)
            assert generated == expected["contradiction"].replace("maxRecDepth 4096", "maxRecDepth 8192")

        # A small limit must also apply inside the translator, before output exists.
        output = tmp / "depth-too-low"
        limited = run(fixture, "--out", output, "--max-rec-depth", "1", code=1)
        assert "maximum recursion depth" in limited.stderr, limited
        assert not output.exists()

        for fixture, goal, count in [("smt", "Refutation", 8), ("chc", "Problem", 6), ("assuming", "Refutation", 6), ("resets", "Refutation", 7), ("sorts", "Refutation", 8), ("compatibility", "Refutation", 7)]:
            output = tmp / f"session-{fixture}"
            run(SESSIONS / f"{fixture}.smt2", "--out", output)
            generated = check_generated(lean, output, goal=goal, count=count)
            if fixture == "smt":
                assert generated.count("def SMT.xor ") == generated.count("def SMT.distinct3.{") == 1
            query = output / "Query.lean"
            edited = generated + "\n-- User session proof work.\n"
            query.write_text(edited)
            run(SESSIONS / f"{fixture}.smt2", "--out", output, code=1)
            assert query.read_text() == edited

        check_uninterpreted_sorts(lean, tmp)
        check_integer_division(lean, tmp)
        check_reals(lean, tmp)
        check_conversions(lean, tmp)
        check_bitvectors(lean, tmp)
        check_bitvector_widths(lean, tmp)
        check_bitvector_shifts(lean, tmp)
        check_bitvector_division(lean, tmp)
        check_bitvector_conversions(lean, tmp)
        check_arrays_basic(lean, tmp)
        check_arrays_extended(lean, tmp)
        check_array_sharing(lean, tmp)
        check_datatypes(lean, tmp)

        for logic, goal in [("ALL", "Refutation"), ("HORN", "Problem")]:
            for name, body, count in [
                ("empty", "(check-sat)\n(check-sat)\n(push 1)", 2),
                ("single", "(push 1)\n(assert false)\n(pop 1)\n(check-sat)", 1),
                ("configured", "(assert false)\n(check-sat)\n"
                 "(set-option :print-success false)\n(set-info :status unknown)\n(check-sat)", 2),
            ]:
                source, output = tmp / f"session-{logic}-{name}.smt2", tmp / f"session-{logic}-{name}"
                source.write_text(f"(set-logic {logic})\n" + body)
                result = run(source, "--out", output)
                assert "success" not in result.stdout and "unsat" not in result.stdout
                generated = check_generated(lean, output, goal=goal, count=count)
                if name == "single":
                    expected_body = "True → False" if logic == "ALL" else "True"
                    assert f"def {goal} : Prop :=\n  {expected_body}\n" in generated

        # A later failure must leave no output, even after reconstructing query 1.
        for name, text, reason in [
            ("underflow", "(set-logic ALL)\n(check-sat)\n(pop 1)", "exceeds active scope depth"),
            ("operator", "(set-logic ALL)\n(check-sat)\n(assert (= (^ 1 0) 0))", "unsupported operator"),
            ("popped-name", "(set-logic ALL)\n(push 1)\n(declare-const p Bool)\n"
             "(assert p)\n(check-sat)\n(pop 1)\n(assert p)", "not declared"),
            ("clause", "(set-logic HORN)\n(declare-fun P (Int) Bool)\n(assert (P 0))\n"
             "(check-sat)\n(assert (=> (not (P 0)) false))\n(check-sat)",
             "CHC relation inside a theory guard"),
            ("declaration", "(set-logic HORN)\n(check-sat)\n(declare-const x Int)\n(check-sat)",
             "unsupported CHC declaration"),
        ]:
            source, output = tmp / f"session-bad-{name}.smt2", tmp / f"session-bad-{name}"
            source.write_text(text)
            result = run(source, "--out", output, code=1)
            assert "query 2:" in result.stderr and reason in result.stderr, result.stderr
            assert not output.exists()

        inputs = [FIXTURES / f"{name}.smt2" for name in ["contradiction", "connectives", "empty", "options"]]
        inputs += [INTEGERS / f"{name}.smt2" for name in ["literals", "arithmetic", "bounds"]]
        inputs += [FUNCTIONS / f"{name}.smt2" for name in ["applications", "congruence"]]
        inputs += [QUANTIFIERS / f"{name}.smt2" for name in ["scopes", "quantified", "hints"]]
        inputs += [BINDINGS / name for name in ["simultaneous.smt2", "definitions.smt2", "named.smt2"]]
        inputs += [ROOT / "tests/translation/sorts/uninterpreted.smt2"]
        for fixture in inputs:
            name = fixture.stem
            output = tmp / name
            result = run(fixture, "--out", output)
            assert "Proof unfinished" in result.stdout
            source = check_generated(lean, output)
            if name == "options":
                assert without_sources(source) == without_sources(expected["contradiction"])
                assert "success" not in result.stdout and "unsat" not in result.stdout
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
                source.write_text(SOLVER_OPTIONS + f"(set-info :status {status})\n" + fixture.read_text())
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
            source.write_text(SOLVER_OPTIONS + horn_text.replace("(set-info :status sat)", metadata))
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

        output = tmp / "surface-forms-chc"
        run(CHC / "surface-forms.smt2", "--out", output)
        surface = check_generated(lean, output, goal="Problem")
        # Every normalized clause retains its location in the ten original assertions.
        clause_sources = [line.split(" (clause ", 1)[0]
                          for line in surface.splitlines() if " (clause " in line]
        assert len(clause_sources) == 13 and len(set(clause_sources)) == 10
        # This combined fixture is inconsistent: P 0, P -> Q, and P -> Q -> False.
        query = output / "Query.lean"
        query.write_text(surface.split("-- Proofs\n", 1)[0] +
                         "theorem checked : ¬Problem := by\n"
                         "  intro h\n"
                         "  rcases h with ⟨p, q, done, _, _, _, hp, hpq, _, _, _, _, _, _, hbad, _⟩\n"
                         "  exact hbad 0 hp (hpq 0 hp)\n")
        check_lean(lean, query, complete=True)

        source, output = tmp / "surface-model.smt2", tmp / "surface-model"
        source.write_text("(set-logic HORN)(declare-fun P (Int) Bool)(assert (P 0))"
                          "(assert (forall ((x Int)) (or (not (P x)) (= x 0))))(check-sat)")
        run(source, "--out", output)
        surface = check_generated(lean, output, goal="Problem")
        query = output / "Query.lean"
        query.write_text(surface.split("-- Proofs\n", 1)[0] +
                         "theorem checked : Problem :=\n"
                         "  ⟨fun x => x = 0, rfl, fun _ hx notZero => notZero hx⟩\n")
        check_lean(lean, query, complete=True)

        source, output = tmp / "hinted-chc.smt2", tmp / "hinted-chc"
        text = (CHC / "definitions.smt2").read_text()
        text = text.replace("(=> |entry clause| (rule x b))",
                            "(! (=> |entry clause| (rule x b)) :pattern ((P x) (R x b)) "
                            ":no-pattern (P (^ x 2)) :qid step)")
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
             "(assert (forall ((x Int)) (=> (= (^ x 2) 0) (P x))))\n(check-sat)",
             "4:1: query 1: command 4: clause 2:", "unsupported operator"),
            ("let-operator", horn_prefix +
             "(assert (forall ((x Int)) (let ((half (^ x 2))) (=> (= half 0) (P x)))))\n(check-sat)",
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
             "(define-fun bad () Int (^ 1 0))\n(check-sat)",
             "4:1: query 1: command 4:", "POW"),
            ("named-clause", horn_prefix +
             '(assert (! (forall ((x Int)) (=> (not (P x)) false)) :named |bad clause|))\n(check-sat)',
             '4:1: query 1: command 4 (:named "bad clause"): clause 2:', "CHC relation inside a theory guard"),
            ("hinted-clause", horn_prefix +
             '(assert (forall ((x Int)) (! (=> (not (P x)) false) :pattern ((P x)) :qid bad)))\n(check-sat)',
             "4:1: query 1: command 4: clause 2:", "CHC relation inside a theory guard"),
            ("global-int", "(set-logic HORN)\n(declare-const x Int)\n(check-sat)",
             "2:1: query 1: command 2:", "unsupported CHC declaration"),
            ("malformed-tail", horn_prefix + "(check-sat)\n(assert",
             "5:8: query 2: command 5:", "unterminated command"),
            ("missing-check", horn_prefix, "4:1: query 1: command 4:", "expected at least one check-sat"),
        ]:
            source, output = tmp / f"horn-{name}.smt2", tmp / f"horn-{name}"
            source.write_text(text)
            result = run(source, "--out", output, code=1)
            # cvc5 renders its diagnostic message as an escaped string.
            escaped_location = location.replace('"', '\\"')
            assert f"{source}:{escaped_location}" in result.stderr, result.stderr
            assert reason in result.stderr, result.stderr
            assert not output.exists()

        # Bad configuration rejects the whole query, with locations, in either mode.
        for logic in ["ALL", "HORN"]:
            for number, (command, reason) in enumerate([
                ('(set-option :produce-models "true")', "invalid value for :produce-models"),
                ("(set-option :random-seed -1)", "invalid value for :random-seed"),
                ("(set-option :global-declarations true)", "must be set before"),
                ("(set-option :unknown false)", "unsupported solver option"),
                ("(set-info :unknown true)", "unsupported metadata"),
                ("(get-proof)", "requires a preceding check"),
                ("(get-model)", "requires a preceding check"),
                ("(get-unsat-core)", "requires a preceding check"),
            ]):
                source, output = tmp / f"config-{logic}-{number}.smt2", tmp / f"config-{logic}-{number}"
                source.write_text(f"(set-logic {logic})\n(assert false)\n{command}\n(check-sat)")
                result = run(source, "--out", output, code=1)
                context = "query 1: " if logic == "HORN" else ""
                assert f"{source}:3:1: {context}command 3:" in result.stderr, result.stderr
                assert reason in result.stderr and not output.exists(), result.stderr
            for suffix in ['(echo "ignored")']:
                source, output = tmp / f"config-tail-{logic}.smt2", tmp / f"config-tail-{logic}"
                source.write_text(SOLVER_OPTIONS + f"(set-logic {logic})\n(assert false)\n(check-sat)\n" + suffix)
                result = run(source, "--out", output, code=1)
                assert "unsupported command" in result.stderr and not output.exists(), result.stderr

        check_resets(lean, tmp)

        for logic, literal in [("ALL", "1"), ("ALL", "(and p 1)"), ("ALL", "missing"),
                               ("HORN", "(or p (not (not p)))")]:
            source, output = tmp / "bad-assumption.smt2", tmp / "bad-assumption"
            source.write_text(f"(set-logic {logic})(declare-const p Bool)(check-sat)(check-sat-assuming ({literal}))")
            run(source, "--out", output, code=1)
            assert not output.exists()
        source, output = tmp / "horn-assuming.smt2", tmp / "horn-assuming"
        source.write_text("(set-logic HORN)(declare-const p Bool)(check-sat-assuming (p (not p)))(check-sat)")
        run(source, "--out", output)
        text = check_generated(lean, output, goal="Problem", count=2)
        assert "check-sat-assuming," in text and "assumption 2" in text

        invalid = [
            "(set-logic QF_S)\n(check-sat)",
            "(set-logic QF_UF)\n(check-sat)\n(pop 1)",
            "(set-logic QF_UF)\n(check-sat)\n(assert",
            "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (= (^ x 0) 0))\n(check-sat)",
            "(set-logic ALL)\n(declare-fun P (String) Bool)\n(check-sat)",
            "(set-logic QF_UFLIA)\n(declare-fun f (Int Int) Int)\n(assert (= (f 1) 0))\n(check-sat)",
            "(set-logic QF_UFLIA)\n(declare-fun f (Int) Int)\n(assert (= (f true) 0))\n(check-sat)",
            "(set-logic ALL)\n(assert (forall ((x String)) true))\n(check-sat)",
            "(set-logic QF_LIA)\n(assert (forall ((x Int)) (> x 0)))\n(check-sat)",
            "(set-logic ALL)\n(assert (exists ((p Bool)) (= (ite p 1 (^ 1 0)) 1)))\n(check-sat)",
            "(set-logic ALL)\n(assert (ite 1 true false))\n(check-sat)",
            "(set-logic ALL)\n(assert (ite true false 1))\n(check-sat)",
            "(set-logic QF_LIA)\n(assert (let ((x 1) (y x)) (= y 1)))\n(check-sat)",
            "(set-logic QF_UF)\n(assert (let ((p true) (q p)) q))\n(check-sat)",
            "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (let ((half (^ x 2))) (let ((copy half)) (= copy 0))))\n(check-sat)",
            "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (let ((next (+ x 1))) (= (^ next 2) 0)))\n(check-sat)",
            "(set-logic UFLIA)\n(declare-fun P (Int) Bool)\n(assert (forall ((x Int)) (! (P x) :weight -1)))\n(check-sat)",
        ]
        for index, text in enumerate(invalid):
            source, output = tmp / f"invalid-{index}.smt2", tmp / f"invalid-{index}"
            source.write_text(text)
            result = run(source, "--out", output, code=1)
            assert re.search(re.escape(str(source)) + r":\d+:\d+: (?:query \d+: )?command ", result.stderr), result.stderr
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
            ("multiline", "; λ\n(set-logic ALL)\n  (assert\n    (= (^ 1 0) 0))\n(check-sat)",
             "3:3: command 2:", "unsupported operator"),
            ("definition-source", "; λ\n(set-logic ALL)\n  (define-fun bad ((x Int)) Int\n    (^ x 2))\n(check-sat)",
             "3:3: command 2:", "POW"),
            ("named-source", '(set-logic ALL)\n  (assert (! (= (^ 1 0) 0) :named |bad body|))\n(check-sat)',
             '2:3: command 2 (:named "bad body"):', "POW"),
            ("unused-named-source", '(set-logic ALL)\n  (assert (let ((ignored (! (^ 1 0) :named |unused body|))) true))\n(check-sat)',
             '2:3: command 2 (:named "unused body"):', "POW"),
            ("alias-source", "(set-logic ALL)\n  (define-sort Bad () String)\n(check-sat)",
             "2:3: command 2:", "unsupported sort alias"),
            ("bad-string", '(set-logic QF_UF)\n(set-info :source "unfinished',
             "2:30: command 2:", "unterminated string"),
            ("extra-close", "(set-logic QF_UF)\n(check-sat)\n  )",
             "3:3: query 2: command 3:", "expected '('"),
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
    print("Demo passed: standalone SMT/CHC translations, source locations, and completed proofs")
    print("Sessions passed: numbered SMT/CHC goals, standalone statements, later failures, and proof protection")


if __name__ == "__main__":
    main()
