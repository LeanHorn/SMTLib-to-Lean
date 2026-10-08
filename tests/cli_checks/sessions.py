from .support import (CHC, read_generated, run, check_lean, check_generated)

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
    check_lean(lean, query, allow_sorry=True)
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
        generated = read_generated(output, goal=goal)
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


