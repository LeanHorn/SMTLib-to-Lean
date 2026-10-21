"""Checked profiles, CHC layout equivalence, manifest mappings, and dialect boundaries."""
import json
import re
import subprocess

from .support import EXE, ROOT, run, read_generated, check_lean


def check_chc_layouts(lean, tmp):
    """Both CHC layouts have the same checked meaning and keep source sharing."""
    imports, sections, equivalences = set(), [], []

    def pair(name, text, *, mode="chc", goal="Problem", count=1, expanded_check=True):
        source = tmp / f"{name}.smt2"
        source.write_text(text)
        generated = []
        for layout in ["structured", "inline"]:
            output = tmp / f"{name}-{layout}"
            run(source, "--out", output, "--mode", mode, "--layout", layout,
                *(["--check-equivalence"] if expanded_check else []))
            code = read_generated(output, goal=goal, count=count)
            wrappers = re.findall(r"^(?:noncomputable )?def \S+\.Clause(?:\d+|s)\b", code, re.M)
            assert bool(wrappers) == (layout == "structured"), code
            namespace = name.replace("-", "_") + "_" + layout
            statements = code.split("-- Proofs\n", 1)[0]
            imports.update(line for line in statements.splitlines() if line.startswith("import "))
            body = "\n".join(line for line in statements.splitlines() if not line.startswith("import "))
            sections.append(f"namespace {namespace}\n{body}\nend {namespace}\n")
            generated.append(code)
        prefix = name.replace("-", "_")
        for number in range(1, count + 1):
            target = goal if count == 1 else f"{goal}_{number}"
            equivalences.append(
                f"example : {prefix}_structured.{target} ↔ {prefix}_inline.{target} := Iff.rfl\n")
        return generated

    # Missing logic must not select refutation semantics in explicit CHC mode.
    # Both RHSs in each SMT let see the enclosing scope, including shadowed x.
    compact = """(declare-fun P (Bool Int) Bool)
(declare-fun Unused (Int) Bool)
(define-fun bump ((x Int)) Int (+ x 1))
(assert (forall ((x Int) (flag Bool))
  (let ((x (bump x)) (old x))
    (let ((copy x) (x (+ old 2)))
      (=> (or flag (< old 0))
          (P flag (+ (+ copy x) (+ (div (- 7) 3) (mod (- 7) 3)))))))))
(check-sat)
"""
    structured, inline = pair("compact", compact)
    assert structured.count("def Problem_1.Clause001") == 1
    assert "Clause002" not in structured, structured
    for code in [structured, inline]:
        assert "Definitions.bump" in code and "∨" in code, code
        assert code.count("let ") >= 4 and "Prop → Int → Prop" in code, code
        assert re.search(r"∃ \(_?r1 : Int → Prop\)", code), code
    equivalences.append("""
example : compact_inline.Problem ↔
    ∃ (p : Prop → Int → Prop) (_unused : Int → Prop),
      ∀ (x : Int) (flag : Prop), (flag ∨ x < 0) →
        p flag ((x + 1 + (x + 2)) + ((-7 : Int) / 3 + (-7 : Int) % 3)) := Iff.rfl
""")
    # The default remains structured, including its exact emitted source.
    default = tmp / "compact-default"
    run(tmp / "compact.smt2", "--out", default, "--mode", "chc")
    assert read_generated(default, goal="Problem") == structured

    array_source = """(set-logic ALL)
(declare-sort I 0)
(declare-const a (Array I Int))
(declare-fun R ((Array I Int)) Bool)
(check-sat)
(assert (R ((as const (Array I Int)) 0)))
(check-sat)
"""
    _, inline = pair("array-laws", array_source, count=2)
    assert "SMT.arrayLaws" in inline and "SMT.constArrayLaw" in inline
    assert "Nonempty" in inline
    equivalences.append("""
example : array_laws_inline.Problem_1 ↔
    ∃ (I : Type), Nonempty I ∧
      ∃ (A : Type) (read : A → I → Int) (write : A → I → Int → A)
        (_a : A) (_r : A → Prop), array_laws_inline.SMT.arrayLaws I Int A read write := Iff.rfl
""")
    pair("empty-clauses", "(check-sat)")
    equivalences.append("example : empty_clauses_inline.Problem ↔ True := Iff.rfl\n")
    pair("fixedpoint-layout", "(declare-rel R (Int))(rule (R 0))(query R)",
         mode="fixedpoint", goal="Safe")
    equivalences.append("""
example : fixedpoint_layout_inline.Reachable := by
  rintro ⟨r, seed, excluded⟩
  exact excluded 0 seed
""")

    sizes = []
    for depth in [5, 18]:
        body = f"(P x{depth})"
        for i in range(depth, 0, -1):
            body = f"(let ((x{i} (+ x{i-1} x{i-1}))) {body})"
        _, inline = pair(f"shared-{depth}",
                         "(declare-fun P (Int) Bool)"
                         f"(assert (forall ((x0 Int)) {body}))(check-sat)",
                         expanded_check=False)
        assert inline.count("let ") >= depth, inline
        sizes.append(len(inline.encode()))
    assert sizes[1] < 25000 and sizes[1] < 4 * sizes[0], sizes

    checked = tmp / "ChcLayouts.lean"
    checked.write_text("\n".join(sorted(imports)) + "\n\n" +
                       "set_option linter.unusedVariables false\n\n" +
                       "\n".join(sections + equivalences))
    check_lean(lean, checked, complete=True)


def check_chc_rejections(tmp):
    # Explicit CHC validates clauses regardless of set-logic; every failed
    # single-file translation leaves its destination absent.
    for i, logic in enumerate(["", "(set-logic ALL)", "(set-logic HORN)"]):
        source, output = tmp / f"nonhorn-{i}.smt2", tmp / f"nonhorn-{i}"
        source.write_text(logic + "(declare-fun P (Int) Bool)(declare-fun Q (Int) Bool)"
                          "(assert (forall ((x Int)) (or (P x) (Q x))))(check-sat)")
        result = run(source, "--out", output, "--mode", "chc", "--layout", "inline", code=1)
        assert "CHC" in result.stderr and not output.exists(), result.stderr
    source = tmp / "non-chc-layout.smt2"
    source.write_text("(set-logic ALL)(assert false)(check-sat)")
    for mode in ["auto", "model"]:
        output = tmp / f"non-chc-layout-{mode}"
        run(source, "--out", output, "--mode", mode, "--layout", "inline", code=1)
        assert not output.exists()
    for layout in ["unknown", "", "INLINE"]:
        output = tmp / "invalid-layout"
        run(source, "--out", output, "--layout", layout, code=2)
        assert not output.exists()
    run(source, "--out", tmp / "missing-layout", "--layout", code=2)


def check_chc_manifest(tmp):
    source = tmp / "chc-manifest"
    source.mkdir()
    good = source / "good.smt2"
    good.write_text("""(declare-const c Int)
(declare-fun f (Int) Int)
(declare-fun |P source| (Bool Int) Bool)
(declare-fun Unused (Int) Bool)
(define-fun inc ((x Int)) Int (+ (f x) c))
(check-sat)
(assert (forall ((x Int) (b Bool))
  (and (|P source| b (inc x)) (|P source| b x))))
(check-sat)
""")
    (source / "bad.smt2").write_text(
        "(declare-fun P (Int) Bool)(declare-fun Q (Int) Bool)"
        "(assert (or (P 0) (Q 0)))(check-sat)")
    previous = None
    for layout in ["structured", "inline"]:
        output = tmp / f"chc-manifest-{layout}"
        result = subprocess.run(
            [str(EXE), str(source), "--out", str(output), "--mode", "chc",
             "--layout", layout, "--check-equivalence"],
            cwd=ROOT, capture_output=True, text=True)
        assert result.returncode == 1 and "CHC" in result.stderr, result
        report = json.loads((output / "manifest.json").read_text())
        assert (report["total"], report["translated"], report["failed"]) == (2, 1, 1), report
        assert report["mode"] == "chc" and report["layout"] == layout
        assert report["check_equivalence"] is True
        entries = {entry["input"]: entry for entry in report["files"]}
        assert entries["bad.smt2"]["queries"] == []
        assert not (output / entries["bad.smt2"]["output"]).exists()
        entry = entries["good.smt2"]
        code = (output / entry["output"]).read_text()
        queries = entry["queries"]
        assert [query["query_number"] for query in queries] == [1, 2], queries
        for number, query in enumerate(queries, 1):
            assert query["goal_name"] == entry["namespace"] + f".Problem_{number}", query
            assert query["target_kind"] == "model_existence" and query["horn"] is True
            assert query["layout"] == layout
            assert query["wrappers_emitted"] == (layout == "structured")
            assert set(query["required_theories"]) == {"Core", "Int", "UninterpretedFunctions"}
            symbols = query["symbols"]
            assert [symbol["source_name"] for symbol in symbols] == ["c", "f", "P source", "Unused"]
            assert [symbol["lean_binder"] for symbol in symbols] == ["c0", "f0", "r0", "r1"]
            assert [symbol["parameter_index"] for symbol in symbols] == list(range(4))
            assert [symbol["role"] for symbol in symbols] == [
                "background_constant", "background_function", "predicate", "predicate"]
            assert [symbol["argument_sorts"] for symbol in symbols] == [[], ["Int"], ["Bool", "Int"], ["Int"]]
            assert [symbol["result_sort"] for symbol in symbols] == ["Int", "Int", "Bool", "Bool"]
            body = code.split(f"def Problem_{number} : Prop :=", 1)[1].split("\n\n", 1)[0]
            for symbol in symbols:
                assert f"({symbol['emitted_binder']} :" in body, (symbol, body)
                ref = symbol["source"]
                assert ref["file"] == str(good.resolve()) and ref["command_number"] == symbol["parameter_index"] + 1
                assert ref["start"]["line"] == symbol["parameter_index"] + 1
            clauses, wrappers = query["clauses"], query["wrapper_names"]
            assert len(clauses) == (0 if number == 1 else 2)
            assert len(wrappers) == len(clauses) + 1 and wrappers[-1].endswith(".Clauses")
            assert [clause["wrapper_name"] for clause in clauses] == wrappers[:-1]
            for index, clause in enumerate(clauses, 1):
                assert clause["assertion_number"] == 1
                assert clause["wrapper_name"].endswith(f".Clause{index:03}")
                ref = clause["source"]
                assert ref["file"] == str(good.resolve()) and ref["command_number"] == 7
                assert ref["start"]["line"] == 7 and ref["end"]["offset"] > ref["start"]["offset"]
        if previous is not None:
            for before, after in zip(previous, queries):
                for key in ["goal_name", "clauses", "wrapper_names", "required_theories"]:
                    assert before[key] == after[key], (key, before, after)
        previous = queries


def check_profiles(lean, tmp):
    fixtures = ROOT / "tests/translation"
    model_input = fixtures / "chc/general-model.smt2"
    output = tmp / "general-model"
    run(model_input, "--out", output, "--mode", "model")
    generated = read_generated(output, goal="Model", count=3)
    assert "Outside the Flex Horn adapter" in generated
    check_lean(lean, output / "Query.lean", allow_sorry=True)
    proof = output / "Checked.lean"
    proof.write_text(generated.split("-- Proofs\n", 1)[0] + """
example : Model_1 ↔ ∃ (_c : Int) (p q : Int → Prop),
    (∃ x, p x) ∧ (∀ x, p x ∨ q x) ∧ (∀ x, ¬(p x ∧ q x)) := Iff.rfl

theorem model_sat : Model_1 :=
  ⟨0, fun _ => True, fun _ => False, ⟨0, True.intro⟩,
    fun _ => Or.inl True.intro, fun _ h => h.2⟩

theorem model_unsat : ¬Model_2 := by
  rintro ⟨c, p, q, ⟨x, hx⟩, _, _, absent⟩
  exact absent x hx

theorem after_pop : Model_3 := model_sat
""")
    check_lean(lean, proof, complete=True)
    rejected = tmp / "strict-horn"
    assert "CHC" in run(model_input, "--out", rejected, code=1).stderr
    assert not rejected.exists()

    output = tmp / "fixedpoint"
    fixture = fixtures / "fixedpoint/reachability.smt2"
    run(fixture, "--mode", "fixedpoint", "--out", output)
    generated = read_generated(output, goal="Safe", count=3)
    assert "Z3 query verdict: unsat" in generated and "Z3 query verdict: sat" in generated
    assert "unexecuted request" in generated
    assert ':10:1-10:12 (query 1: query, command 9)' in generated
    assert '(rule "seed")' in generated
    for i in range(1, 4):
        assert f"def Reachable_{i} : Prop := ¬Safe_{i}" in generated
    check_lean(lean, output / "Query.lean", allow_sorry=True)
    proof = output / "Checked.lean"
    proof.write_text(generated.split("-- Proofs\n", 1)[0].replace("import Init", "import Lean", 1) + """
example : Safe_1 ↔ ∃ (r : Int → Prop) (bad : Prop),
    (∀ _x : Int, r 0) ∧ (∀ x, r x → r (x + 1)) ∧
    (∀ x, r x → x < 0 → bad) ∧ (bad → False) := Iff.rfl

theorem first_safe : Safe_1 := by
  refine ⟨fun x => 0 ≤ x, False, ?_, ?_, ?_, ?_⟩
  · intro; omega
  · intro x hx; omega
  · intro x hx hn; omega
  · exact id

theorem second_reachable : Reachable_2 := by
  rintro ⟨r, bad, seed, _, _, excluded⟩
  exact excluded 0 (seed 0)

theorem third_reachable : Reachable_3 := by
  rintro ⟨r, bad, _, _, _, fact, excluded⟩
  exact excluded (fact 0)
""")
    check_lean(lean, proof, complete=True)

    source, output = tmp / "typed-rules.smt2", tmp / "typed-rules"
    source.write_text("""
(declare-rel |mixed; relation| (Bool (_ BitVec 2) Real))
(declare-var x Int)
(declare-var |smt2lean.query.0| (_ BitVec 2))
(rule (forall ((x Real))
  (=> (= x 1.0) (|mixed; relation| true |smt2lean.query.0| x))))
(query |mixed; relation|)
""")
    run(source, "--out", output, "--mode", "fixedpoint")
    generated = read_generated(output, goal="Safe")
    proof = output / "Checked.lean"
    proof.write_text(generated.split("-- Proofs\n", 1)[0] + """
theorem typed_reachable : Reachable := by
  rintro ⟨r, seed, excluded⟩
  exact excluded True 0 1 (seed 0 0 1 rfl)
""")
    check_lean(lean, proof, complete=True)

    # Early and late failures must leave no partial output. Small generated cases
    # avoid storing one fixture per rejection or paying for additional Lean runs.
    prefix = "(declare-rel P (Int))(declare-var x Int)(rule (P 0))(query P)"
    for i, (tail, reason) in enumerate([
        ("(push 1)", "unsupported fixedpoint command"),
        ("(query (P 0))", "expected one symbol"),
        ("(query Missing)", "declared relation"),
        ("(query P :print-answer true)", "without query options"),
        ("(declare-var |x| Int)", "duplicate fixedpoint symbol"),
        ("(declare-rel A ((Array Int Int)))", "supports Bool, Int, Real"),
        ("(rule (=> (not (P x)) (P (+ x 1))))(query P)", "theory guard"),
        ("(rule false)(query P)", "positive relation head"),
        ("(rule (exists ((y Int)) (P y)))(query P)", "quantifier"),
        ("(rule (=> (= (div x 0) 1) (P x)))(query P)", "nonzero literal divisor"),
        ("(exit)(rule (P 1))", "after exit"),
    ]):
        source, target = tmp / f"bad-profile-{i}.smt2", tmp / f"bad-profile-{i}"
        source.write_text(prefix + tail)
        result = run(source, "--out", target, "--mode", "fixedpoint", code=1)
        assert reason in result.stderr, result.stderr
        assert not target.exists()
    for mode in ["unknown", "", "HORN"]:
        run(model_input, "--out", tmp / "bad-mode", "--mode", mode, code=2)
    check_chc_layouts(lean, tmp)
    check_chc_rejections(tmp)
    check_chc_manifest(tmp)
    print("Profiles passed: model/fixedpoint proofs, explicit CHC, equivalent layouts, source sharing and rejections")
