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
SESSIONS = ROOT / "tests/translation/sessions"
SOLVER_OPTIONS = """(set-option :produce-models true)
(set-option :produce-proofs true)
(set-option :produce-unsat-cores true)
(set-option :print-success true)
(set-option :random-seed 42)
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
    result = subprocess.run(
        [*args, source.name], cwd=source.parent,
        env=dict(os.environ, LEAN_PATH=str(source.parent)),
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


def check_resets(lean, tmp):
    """Check resets, observation requests, and logic changes through the actual CLI."""
    for name, body, reason in [
        ("reset-scope", "(set-logic ALL)(push 1)(reset-assertions)(pop 1)", "exceeds active scope"),
        ("reset-symbol", "(set-logic ALL)(declare-const p Bool)(reset-assertions)(assert p)", "not declared"),
        ("reset-definition", "(set-logic ALL)(define-fun p () Bool true)(reset-assertions)(assert p)", "not declared"),
        ("reset-global", "(set-option :global-declarations true)(set-logic ALL)(declare-const p Bool)(reset)(set-logic ALL)(assert p)", "not declared"),
        ("late-result", "(set-logic ALL)(check-sat)(assert true)(get-model)", "requires a preceding check"),
        ("named-request", "(set-logic ALL)(check-sat)(get-value ((! true :named leak)))", "cannot introduce named terms"),
        ("bad-global", '(set-option :global-declarations "true")', "requires true or false"),
    ]:
        source, output = tmp / f"{name}.smt2", tmp / name
        source.write_text(body)
        result = run(source, "--out", output, code=1)
        assert reason in result.stderr and not output.exists(), result.stderr
    source, output = tmp / "skipped.smt2", tmp / "skipped"
    source.write_text("(set-logic ALL)(assert false)(check-sat)(get-model)(get-proof)(get-unsat-core)(get-unsat-assumptions)(get-assignment)(get-assertions)(get-info :name)(get-option :produce-models)(get-value (true))")
    result = run(source, "--out", output)
    text = check_generated(lean, output)
    assert text.count("-- Not executed:") == 9
    assert not {"sat", "unsat", "unknown"}.intersection(result.stdout.splitlines())

    source, output = tmp / "reset-logic.smt2", tmp / "reset-logic"
    source.write_text("(set-logic QF_UF)(assert false)(check-sat)(reset)(set-logic HORN)(declare-const p Bool)(check-sat-assuming (p))(reset)(set-logic QF_LIA)(declare-const x Int)(assert (< x 0))(check-sat)")
    run(source, "--out", output)
    query = output / "Query.lean"
    text = query.read_text()
    assert all(f"def {name} : Prop" in text for name in ["Refutation_1", "Problem_2", "Refutation_3"])
    check_lean(lean, query)
    query.write_text(text.split("-- Proofs\n", 1)[0])
    check_lean(lean, query)


def check_uninterpreted_sorts(lean, tmp):
    """Prove distinguishing examples, so a fixed or empty carrier cannot pass."""
    output = tmp / "sort-horn-demo"
    run(CHC / "uninterpreted.smt2", "--out", output)
    check_generated(lean, output, goal="Problem")
    cases = [
        ("nonempty", "UF", "(assert (forall ((_x S)) false))", "Refutation",
         "  intro A h allFalse\n  exact h.elim allFalse\n"),
        ("singleton", "UF", "(assert (forall ((x S) (y S)) (= x y)))", "¬ Refutation",
         "  intro h\n  exact h Unit ⟨()⟩ (fun x y => Subsingleton.elim x y)\n"),
        ("two-elements", "QF_UF", "(declare-const a S)(declare-const b S)(assert (distinct a b))",
         "¬ Refutation", "  intro h\n  exact h Bool ⟨false⟩ true false (by change true ≠ false; decide)\n"),
        ("infinite", "UF", "(declare-fun next (S) S)(declare-const zero S)"
         "(assert (forall ((x S) (y S)) (=> (= (next x) (next y)) (= x y))))"
         "(assert (forall ((x S)) (not (= (next x) zero))))", "¬ Refutation",
         "  intro h\n  exact h Nat ⟨0⟩ Nat.succ 0 ⟨fun _ _ e => Nat.succ.inj e, fun _ e => Nat.noConfusion e⟩\n"),
        ("horn-singleton", "HORN", "(declare-fun P (S) Bool)"
         "(assert (forall ((x S)) (P x)))"
         "(assert (forall ((x S) (y S)) (=> (and (P x) (P y) (distinct x y)) false)))",
         "Problem", "  refine ⟨Unit, ⟨()⟩, (fun _ => True), ?_, ?_⟩\n"
         "  · intro _; trivial\n  · intro x y _ _ different; exact different (Subsingleton.elim x y)\n"),
        ("horn-nonempty", "HORN", "(assert (forall ((_x S)) false))", "¬ Problem",
         "  rintro ⟨A, ⟨a⟩, allFalse⟩\n  exact allFalse a\n"),
    ]
    for name, logic, body, target, proof in cases:
        source, output = tmp / f"sort-{name}.smt2", tmp / f"sort-{name}"
        source.write_text(f"(set-logic {logic})(declare-sort S 0){body}(check-sat)")
        run(source, "--out", output)
        goal = "Problem" if logic == "HORN" else "Refutation"
        generated = check_generated(lean, output, goal=goal)
        statements = generated.split("-- Proofs\n", 1)[0]
        completed = output / "Query.lean"
        completed.write_text(statements + f"theorem checked : {target} := by\n" + proof)
        check_lean(lean, completed, complete=True)
    for name, prefix, suffix, reason in [
        ("arity", "(set-logic ALL)(check-sat)", "(declare-sort S 1)", "only arity 0"),
        ("popped-sort", "(set-logic ALL)(push 1)(declare-sort S 0)(check-sat)",
         "(pop 1)(declare-const x S)", "not declared"),
        ("reset-sort", "(set-option :global-declarations true)(set-logic ALL)(declare-sort S 0)(check-sat)",
         "(reset)(set-logic ALL)(declare-const x S)", "not declared"),
        ("removed-alias", "(set-logic ALL)(declare-sort S 0)(define-sort Alias () S)(check-sat)",
         "(reset-assertions)(declare-const x Alias)", "not declared"),
        ("horn-constant", "(set-logic HORN)(declare-sort S 0)(check-sat)",
         "(declare-const x S)(check-sat)", "unsupported CHC declaration"),
        ("horn-function", "(set-logic HORN)(declare-sort S 0)(check-sat)",
         "(declare-fun f (S) S)(check-sat)", "unsupported CHC declaration"),
        ("horn-negative", "(set-logic HORN)(declare-sort S 0)(declare-fun P (S) Bool)(check-sat)",
         "(assert (forall ((x S)) (=> (not (P x)) false)))(check-sat)", "CHC relation inside"),
    ]:
        source, output = tmp / f"sort-bad-{name}.smt2", tmp / f"sort-bad-{name}"
        source.write_text(prefix + suffix)
        result = run(source, "--out", output, code=1)
        assert "query 2:" in result.stderr and reason in result.stderr, result.stderr
        assert not output.exists()
    print("Sort semantics passed: nonempty, singleton, two-element, infinite, and Horn models; later failures leave no output")


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
        for fixture, goal, count in [("smt", "Refutation", 8), ("chc", "Problem", 6), ("assuming", "Refutation", 6), ("resets", "Refutation", 7), ("sorts", "Refutation", 8)]:
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
            ("operator", "(set-logic ALL)\n(check-sat)\n(assert (= (div 1 0) 0))", "unsupported operator"),
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

        for logic, literal in [("ALL", "true"), ("ALL", "(and p p)"), ("ALL", "missing"),
                               ("HORN", "true")]:
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
            "(set-logic QF_LRA)\n(check-sat)",
            "(set-logic QF_UF)\n(check-sat)\n(pop 1)",
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
