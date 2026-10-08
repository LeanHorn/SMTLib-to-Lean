from .support import (ROOT, CHC, run, check_lean, check_generated, unfold_statement)

def check_bitvectors(lean, tmp):
    """Standalone core output and completed proofs distinguishing widths and signedness."""
    for fixture, goal in [(ROOT / "tests/translation/bitvec/arithmetic.smt2", "Refutation"),
                          (CHC / "bitvec.smt2", "Problem")]:
        output = tmp / f"bv-{goal}"
        run(fixture, "--out", output)
        generated = check_generated(lean, output, goal=goal)
        assert generated.startswith("import Init\n")
        for helper in (["bvnand", "bvnor", "bvxnor", "bvcomp"] if goal == "Refutation" else ["bvcomp"]):
            assert generated.count(f"def SMT.{helper} ") == 1
    exact = [
        "(= (bvadd #xe #x1 #x2) #x1)", "(= (bvmul #x3 #x5 #x3) #xd)",
        "(= (bvand #xf #x7 #x3) #x3)", "(= (bvor #x1 #x2 #x4) #x7)",
        "(= (bvxor #x1 #x2 #x4) #x7)",
        "(= (bvnand #b1010 #b1100) #b0111)", "(= (bvnor #b1010 #b1100) #b0001)",
        "(= (bvxnor #b1010 #b1100) #b1001)",
        "(= (bvcomp #x0 #x0) #b1)", "(= (bvcomp #x0 #x1) #b0)",
        "(= (bvcomp #b1 #b1) #b1)", "(= #x0001 (_ bv1 16))",
    ]
    for width in [32, 64, 129]:
        modulus = 2 ** width
        exact.extend([
            f"(= (bvadd (_ bv{modulus - 1} {width}) (_ bv1 {width})) (_ bv0 {width}))",
            f"(= (bvneg (_ bv{modulus // 2} {width})) (_ bv{modulus // 2} {width}))",
            f"(= (bvmul (_ bv{modulus // 2} {width}) (_ bv2 {width})) (_ bv0 {width}))",
        ])
    cases = [
        ("exact", "QF_BV", "(assert (not (and " + " ".join(exact) + ")))", "Refutation",
         "  intro h\n  apply h\n  decide\n"),
        ("signedness", "QF_BV", "(declare-const x (_ BitVec 8))"
         "(assert (bvugt x #x00))(assert (bvslt x #x00))", "¬ Refutation",
         "  intro h\n  apply h (255 : BitVec 8)\n  decide\n"),
        ("congruence", "QF_UFBV", "(declare-fun f ((_ BitVec 8)) (_ BitVec 4))"
         "(declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))"
         "(assert (= x y))(assert (distinct (f x) (f y)))", "Refutation",
         "  intro f x y h\n  exact h.2 (congrArg f h.1)\n"),
        ("horn-model", "HORN", "(declare-fun P ((_ BitVec 4)) Bool)(assert (P #x0))"
         "(assert (forall ((x (_ BitVec 4))) (=> (P x) (P (bvadd x #x1)))))"
         "(assert (forall ((x (_ BitVec 4))) (=> (and (P x) (bvult x #x0)) false)))", "Problem",
         "  refine ⟨(fun _ => True), True.intro, (fun _ _ => True.intro), ?_⟩\n"
         "  intro x _ less\n  exact Nat.not_lt_zero x.toNat less\n"),
        ("horn-wrap", "HORN", "(declare-fun P ((_ BitVec 4)) Bool)(assert (P #xf))"
         "(assert (forall ((x (_ BitVec 4))) (=> (P x) (P (bvadd x #x1)))))"
         "(assert (=> (P #x0) false))", "¬ Problem",
         "  rintro ⟨p, fact, step, safety⟩\n  exact safety (step 15 fact)\n"),
    ]
    for name, logic, body, target, proof in cases:
        source, output = tmp / f"bv-{name}.smt2", tmp / f"bv-{name}"
        source.write_text(f"(set-logic {logic}){body}(check-sat)")
        run(source, "--out", output)
        generated = check_generated(lean, output, goal="Problem" if logic == "HORN" else "Refutation")
        assert generated.startswith("import Init\n")
        completed = output / "Query.lean"
        completed.write_text(generated.split("-- Proofs\n", 1)[0]
                             + f"theorem checked : {target} := by\n" + unfold_statement(generated, target) + proof)
        check_lean(lean, completed, complete=True)
    # Reject the entire session on a later unsupported operator or stale width alias.
    for name, tail, reason in [
        ("operator", "(assert (= ((_ int_to_bv 4) (^ 2 3)) #x0))", "POW"),
        ("width", "(assert (= (bvadd #x1 #b1) #x2))", "comparable bit-vector"),
        ("scope", "(push 1)(define-sort Byte () (_ BitVec 8))(pop 1)(declare-const x Byte)", "declared"),
        ("reset", "(define-sort Byte () (_ BitVec 8))(reset)(set-logic ALL)(declare-const x Byte)", "declared"),
        ("hidden", "(define-fun ignore ((x (_ BitVec 4))) Bool true)"
         "(assert (ignore ((_ int_to_bv 4) (^ 2 3))))", "POW"),
    ]:
        source, output = tmp / f"bv-invalid-{name}.smt2", tmp / f"bv-invalid-{name}"
        source.write_text("(set-logic ALL)(assert (= #x1 #x1))(check-sat)" + tail)
        assert reason in run(source, "--out", output, code=1).stderr
        assert not output.exists()
    print("Bitvector CLI passed: core-only SMT/CHC output, five completed proofs, and scope/error protection")


def check_bitvector_widths(lean, tmp):
    """Exact widths, standalone output, and completed refutations/Horn models."""
    for fixture, goal in [(ROOT / "tests/translation/bitvec/widths.smt2", "Refutation"),
                          (CHC / "widths.smt2", "Problem")]:
        output = tmp / f"widths-{goal}"
        run(fixture, "--out", output)
        assert check_generated(lean, output, goal=goal).startswith("import Init\n")
    exact = [
        "(= (concat #b1 #b00 #b101) #b100101)",
        "(= ((_ extract 7 4) #xa5) #xa)", "(= ((_ extract 3 0) #xa5) #x5)",
        "(= ((_ extract 7 7) #xa5) #b1)", "(= ((_ extract 0 0) #xa5) #b1)",
        "(= ((_ extract 7 0) #xa5) #xa5)",
        "(= ((_ zero_extend 0) #x8) #x8)", "(= ((_ sign_extend 0) #x8) #x8)",
        "(= ((_ zero_extend 4) #x8) #x08)", "(= ((_ sign_extend 4) #x8) #xf8)",
        "(= ((_ sign_extend 4) #x7) #x07)",
        "(= ((_ sign_extend 7) #b1) #xff)", "(= ((_ zero_extend 7) #b1) #x01)",
        "(= ((_ repeat 1) #xa) #xa)", "(= ((_ repeat 3) #xa) #xaaa)",
        "(= ((_ extract 8 4) ((_ repeat 3) #xa)) #b01010)",
    ]
    for width in [32, 64, 129]:
        half = 2 ** (width - 1)
        exact.extend([
            f"(= ((_ sign_extend 1) (_ bv{half} {width})) (_ bv{3 * half} {width + 1}))",
            f"(= ((_ extract {width} 1) (concat (_ bv{half + 1} {width}) #b0)) (_ bv{half + 1} {width}))",
        ])
    cases = [
        ("exact", "QF_BV", "(assert (not (and " + " ".join(exact) + ")))", "Refutation",
         "  intro h\n  apply h\n  decide\n"),
        ("roundtrip", "QF_BV", "(declare-const hi (_ BitVec 4))(declare-const lo (_ BitVec 3))"
         "(assert (distinct ((_ extract 6 3) (concat hi lo)) hi))", "Refutation",
         "  intro hi lo h\n  exact h BitVec.extractLsb'_append_eq_left\n"),
        ("extension", "QF_BV", "(assert (= ((_ sign_extend 4) #x8) ((_ zero_extend 4) #x8)))", "Refutation",
         "  intro h\n  exact (by decide : (248 : BitVec 8) ≠ 8) h\n"),
        ("horn-model", "HORN", "(declare-fun P ((_ BitVec 8)) Bool)"
         "(assert (P ((_ sign_extend 4) #x8)))(assert (=> (P ((_ zero_extend 4) #x8)) false))", "Problem",
         "  refine ⟨(fun x => x = 248), rfl, ?_⟩\n"
         "  intro h\n  exact (by decide : (8 : BitVec 8) ≠ 248) h\n"),
        ("horn-repeat", "HORN", "(declare-fun P ((_ BitVec 8)) Bool)"
         "(assert (P ((_ repeat 2) #xa)))(assert (=> (P (concat #xa #xa)) false))", "¬ Problem",
         "  rintro ⟨p, fact, safety⟩\n  exact safety fact\n"),
    ]
    for name, logic, body, target, proof in cases:
        source, output = tmp / f"widths-{name}.smt2", tmp / f"widths-{name}"
        source.write_text(f"(set-logic {logic}){body}(check-sat)")
        run(source, "--out", output)
        generated = check_generated(lean, output, goal="Problem" if logic == "HORN" else "Refutation")
        assert generated.startswith("import Init\n")
        completed = output / "Query.lean"
        completed.write_text(generated.split("-- Proofs\n", 1)[0]
                             + f"theorem checked : {target} := by\n" + unfold_statement(generated, target) + proof)
        check_lean(lean, completed, complete=True)
    for name, tail, reason in [
        ("slice", "(assert (= ((_ extract 4 0) #xf) #b01111))", "high extract index"),
        ("repeat", "(assert (= ((_ repeat 0) #xf) #xf))", "number of repeats > 0"),
        ("width", "(assert (= ((_ zero_extend 4) #xf) #xf))", "same type"),
        ("hidden", "(define-fun ignore ((x (_ BitVec 8))) Bool true)"
         "(assert (ignore ((_ zero_extend 4) ((_ int_to_bv 4) (^ 2 3)))))", "POW"),
        ("unused", "(define-fun bad () (_ BitVec 8) ((_ zero_extend 4) ((_ int_to_bv 4) (^ 2 3))))", "POW"),
    ]:
        source, output = tmp / f"widths-invalid-{name}.smt2", tmp / f"widths-invalid-{name}"
        source.write_text("(set-logic ALL)(assert (= ((_ repeat 2) #xa) #xaa))(check-sat)" + tail)
        assert reason in run(source, "--out", output, code=1).stderr
        assert not output.exists()
    print("Bitvector widths CLI passed: standalone SMT/CHC output, five completed proofs, and later-error protection")


def check_bitvector_shifts(lean, tmp):
    """Variable shifts, indexed rotations, and huge amounts in standalone output."""
    for fixture, goal in [(ROOT / "tests/translation/bitvec/shifts.smt2", "Refutation"),
                          (CHC / "shifts.smt2", "Problem")]:
        output = tmp / f"shifts-{goal}"
        run(fixture, "--out", output)
        generated = check_generated(lean, output, goal=goal)
        assert generated.startswith("import Init\n")
        for helper in ["bvshl", "bvlshr", "bvashr"]:
            assert generated.count(f"def SMT.{helper} ") == 1
        if goal == "Refutation":
            # Prove the bounded helpers agree with the unbounded core operations
            # for arbitrary widths and operands, not only the numeric samples.
            proofs = ""
            for name, op, zero in [("bvshl", "<<<", "shiftLeft_eq_zero"),
                                   ("bvlshr", ">>>", "ushiftRight_eq_zero")]:
                proofs += f"""
theorem checked_{name} {{w : Nat}} (x y : BitVec w) : SMT.{name} x y = x {op} y.toNat := by
  change x {op} min y.toNat w = x {op} y.toNat
  by_cases h : y.toNat ≤ w
  · simp [Nat.min_eq_left h]
  · have hn : w ≤ y.toNat := by omega
    rw [Nat.min_eq_right hn, BitVec.{zero} (Nat.le_refl w), BitVec.{zero} hn]
"""
            proofs += """
theorem checked_bvashr {w : Nat} (x y : BitVec w) : SMT.bvashr x y = x.sshiftRight y.toNat := by
  change x.sshiftRight (min y.toNat w) = x.sshiftRight y.toNat
  by_cases h : y.toNat ≤ w
  · simp [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega : w ≤ y.toNat)]
    ext i hi
    simp only [BitVec.getElem_sshiftRight]
    simp [show ¬ w + i < w by omega, show ¬ y.toNat + i < w by omega]
"""
            laws = output / "ShiftLaws.lean"
            laws.write_text(generated.split("-- Proofs\n", 1)[0] + proofs)
            check_lean(lean, laws, complete=True)
    exact = [
        "(= (bvshl #x9 #x1) #x2)", "(= (bvlshr #x8 #x1) #x4)",
        "(= (bvashr #x8 #x1) #xc)", "(= (bvashr #x7 #x1) #x3)",
        "(= (bvshl #x1 #x4) #x0)", "(= (bvshl #x1 #x5) #x0)",
        "(= (bvlshr #xf #x4) #x0)", "(= (bvashr #x8 #x4) #xf)",
        "(= ((_ rotate_left 1) #x9) #x3)", "(= ((_ rotate_right 1) #x9) #xc)",
        "(= ((_ rotate_left 4) #x9) #x9)", "(= ((_ rotate_right 5) #x9) #xc)",
        "(= ((_ rotate_left 4294967295) #b1) #b1)",
        "(= (bvshl #b1 #b1) #b0)", "(= (bvashr #b1 #b1) #b1)",
    ]
    for width in [32, 64, 129]:
        maximum, half = 2 ** width - 1, 2 ** (width - 1)
        exact.extend([
            f"(= (bvshl (_ bv1 {width}) (_ bv{maximum} {width})) (_ bv0 {width}))",
            f"(= (bvlshr (_ bv{maximum} {width}) (_ bv{maximum} {width})) (_ bv0 {width}))",
            f"(= (bvashr (_ bv{half} {width}) (_ bv{maximum} {width})) (_ bv{maximum} {width}))",
        ])
    cases = [
        ("exact", "QF_BV", "(assert (not (and " + " ".join(exact) + ")))", "Refutation",
         "  intro h\n  apply h\n  decide\n"),
        ("variable", "QF_BV", "(declare-const x (_ BitVec 4))(declare-const n (_ BitVec 4))"
         "(assert (= n #x0))(assert (distinct (bvshl x n) x))", "Refutation",
         "  intro x n h\n  rcases h with ⟨rfl, h⟩\n  apply h\n  simp [SMT.bvshl]\n"),
        ("signedness", "QF_BV", "(assert (= (bvashr #x8 #x1) (bvlshr #x8 #x1)))", "Refutation",
         "  intro h\n  exact (by decide : (12 : BitVec 4) ≠ 4) h\n"),
        ("horn-model", "HORN", "(declare-fun P ((_ BitVec 4)) Bool)(assert (P #x8))"
         "(assert (forall ((x (_ BitVec 4))) (=> (P x) (P ((_ rotate_left 4) x)))))"
         "(assert (forall ((x (_ BitVec 4))) (=> (and (P x) (distinct (bvshl x #xf) #x0)) false)))", "Problem",
         "  refine ⟨(fun _ => True), True.intro, (fun _ _ => True.intro), ?_⟩\n"
         "  intro x _ h\n  apply h\n  exact BitVec.shiftLeft_eq_zero (by decide)\n"),
        ("horn-rotate", "HORN", "(declare-fun P ((_ BitVec 4)) Bool)(assert (P #x8))"
         "(assert (forall ((x (_ BitVec 4))) (=> (P x) (P ((_ rotate_left 1) x)))))"
         "(assert (=> (P #x1) false))", "¬ Problem",
         "  rintro ⟨p, fact, step, safety⟩\n  exact safety (step 8 fact)\n"),
    ]
    for name, logic, body, target, proof in cases:
        source, output = tmp / f"shifts-{name}.smt2", tmp / f"shifts-{name}"
        source.write_text(f"(set-logic {logic}){body}(check-sat)")
        run(source, "--out", output)
        generated = check_generated(lean, output, goal="Problem" if logic == "HORN" else "Refutation")
        assert generated.startswith("import Init\n")
        completed = output / "Query.lean"
        completed.write_text(generated.split("-- Proofs\n", 1)[0]
                             + f"theorem checked : {target} := by\n" + unfold_statement(generated, target) + proof)
        check_lean(lean, completed, complete=True)
    for name, tail, reason in [
        ("width", "(assert (= (bvshl #x1 #b1) #x2))", "comparable bit-vector"),
        ("index", "(assert (= ((_ rotate_left -1) #x8) #x1))", "Negative numerals"),
        ("overflow", "(assert (= ((_ rotate_left 4294967296) #x8) #x8))", "rotation index exceeds"),
        ("unused", "(define-fun bad () (_ BitVec 4) ((_ |rotate_right| 4294967296) #x8))", "rotation index exceeds"),
        ("erased", "(assert (let ((unused ((_ rotate_left 4294967296) #x8))) true))", "rotation index exceeds"),
        ("hidden", "(define-fun ignore ((x (_ BitVec 4))) Bool true)"
         "(assert (ignore (bvshl ((_ int_to_bv 4) (^ 2 3)) #x1)))", "POW"),
    ]:
        source, output = tmp / f"shifts-invalid-{name}.smt2", tmp / f"shifts-invalid-{name}"
        source.write_text("(set-logic ALL)(assert (= (bvshl #x1 #x1) #x2))(check-sat)" + tail)
        assert reason in run(source, "--out", output, code=1).stderr
        assert not output.exists()
    print("Shift CLI passed: three general helper proofs, five completed query proofs, standalone output, and error protection")


def check_bitvector_division(lean, tmp):
    """Standalone output preserves SMT's zero-divisor and signed remainder rules."""
    for fixture, goal in [(ROOT / "tests/translation/bitvec/division.smt2", "Refutation"),
                          (CHC / "bv-division.smt2", "Problem")]:
        output = tmp / f"bv-division-{goal}"
        run(fixture, "--out", output)
        generated = check_generated(lean, output, goal=goal)
        assert generated.startswith("import Init\n")
        for operation in ["smtUDiv", "smtSDiv", "srem", "smod"]:
            assert f".{operation}" in generated
    exact = [
        "(= (bvudiv #xfd #x02) #x7e)", "(= (bvurem #xfd #x02) #x01)",
        "(= (bvsdiv #xfd #x02) #xff)", "(= (bvsrem #xfd #x02) #xff)",
        "(= (bvsmod #xfd #x02) #x01)", "(= (bvsdiv #x03 #xfe) #xff)",
        "(= (bvsrem #x03 #xfe) #x01)", "(= (bvsmod #x03 #xfe) #xff)",
        "(= (bvsdiv #xfd #xfe) #x01)", "(= (bvsrem #xfd #xfe) #xff)",
        "(= (bvsmod #xfd #xfe) #xff)", "(= (bvudiv #x00 #x00) #xff)",
        "(= (bvudiv #xfd #x00) #xff)", "(= (bvurem #xfd #x00) #xfd)",
        "(= (bvsdiv #x00 #x00) #xff)", "(= (bvsdiv #x03 #x00) #xff)",
        "(= (bvsdiv #xfd #x00) #x01)", "(= (bvsrem #xfd #x00) #xfd)",
        "(= (bvsmod #xfd #x00) #xfd)", "(= (bvsdiv #x80 #xff) #x80)",
        "(= (bvsrem #x80 #xff) #x00)", "(= (bvsmod #x80 #xff) #x00)",
    ]
    cases = [
        ("exact", "QF_BV", "(assert (not (and " + " ".join(exact) + ")))", "Refutation",
         "  intro h\n  apply h\n  decide\n"),
        ("remainder-sign", "QF_BV", "(declare-const x (_ BitVec 8))"
         "(assert (= (bvsrem x #x02) #xff))(assert (= (bvsmod x #x02) #x01))", "¬ Refutation",
         "  intro h\n  apply h (253 : BitVec 8)\n  decide\n"),
        ("zero-sign", "QF_BV", "(declare-const x (_ BitVec 8))"
         "(assert (= (bvsdiv x #x00) #x01))(assert (= (bvudiv x #x00) #xff))", "¬ Refutation",
         "  intro h\n  apply h (128 : BitVec 8)\n  decide\n"),
        ("horn-overflow", "HORN", "(declare-fun P ((_ BitVec 4)) Bool)(assert (P #x8))"
         "(assert (forall ((x (_ BitVec 4))) (=> (P x) (P (bvsdiv x #xf)))))"
         "(assert (forall ((x (_ BitVec 4))) (=> (and (P x) (distinct (bvsrem x #xf) #x0)) false)))",
         "Problem", "  refine ⟨(fun x => x = 8), rfl, ?_, ?_⟩\n"
         "  · intro x hx\n    change x = 8 at hx\n    subst x\n    rfl\n"
         "  · intro x hx bad\n    change x = 8 at hx\n    subst x\n    exact bad (by decide)\n"),
        ("horn-modulo", "HORN", "(declare-fun P ((_ BitVec 8)) Bool)"
         "(assert (P (bvsmod #xfd #x02)))(assert (=> (P #x01) false))", "¬ Problem",
         "  rintro ⟨p, fact, safety⟩\n  exact safety fact\n"),
    ]
    for name, logic, body, target, proof in cases:
        source, output = tmp / f"bv-div-{name}.smt2", tmp / f"bv-div-{name}"
        source.write_text(f"(set-logic {logic}){body}(check-sat)")
        run(source, "--out", output)
        generated = check_generated(lean, output, goal="Problem" if logic == "HORN" else "Refutation")
        assert generated.startswith("import Init\n")
        completed = output / "Query.lean"
        completed.write_text(generated.split("-- Proofs\n", 1)[0]
                             + f"theorem checked : {target} := by\n" + unfold_statement(generated, target) + proof)
        check_lean(lean, completed, complete=True)
    for name, tail, reason in [
        ("width", "(assert (= (bvsdiv #x1 #b1) #x1))", "comparable bit-vector"),
        ("arity", "(assert (= (bvsmod #x1 #x1 #x1) #x0))", "invalid kind"),
        ("unused", "(define-fun bad () (_ BitVec 4) (bvudiv ((_ int_to_bv 4) (^ 2 3)) #x1))", "POW"),
        ("hidden", "(define-fun ignore ((x (_ BitVec 4))) Bool true)"
         "(assert (ignore (bvsrem ((_ int_to_bv 4) (^ 2 3)) #x1)))", "POW"),
    ]:
        source, output = tmp / f"bv-div-invalid-{name}.smt2", tmp / f"bv-div-invalid-{name}"
        source.write_text("(set-logic ALL)(assert (= (bvudiv #x1 #x0) #xf))(check-sat)" + tail)
        assert reason in run(source, "--out", output, code=1).stderr
        assert not output.exists()
    print("BV division CLI passed: five completed proofs, standalone SMT/CHC output, and later-error protection")


def check_bitvector_conversions(lean, tmp):
    """Wrapping, signedness, and overflow flags through standalone generated code."""
    for fixture, goal in [(ROOT / "tests/translation/bitvec/conversions.smt2", "Refutation"),
                          (CHC / "bv-conversions.smt2", "Problem")]:
        output = tmp / f"bv-conversions-{goal}"
        run(fixture, "--out", output)
        generated = check_generated(lean, output, goal=goal)
        assert generated.startswith("import Init\n")
        for operation in ["ofInt", "toNat", "toInt", "negOverflow", "uaddOverflow",
                          "saddOverflow", "umulOverflow", "smulOverflow"]:
            assert operation in generated
    exact = [
        "(= ((_ int_to_bv 8) (- 1)) #xff)", "(= ((_ int2bv 8) 257) #x01)",
        "(= ((_ int_to_bv 8) (- 257)) #xff)", "(= (ubv_to_int #xff) 255)",
        "(= (bv2nat #x80) 128)", "(= (sbv_to_int #xff) (- 1))",
        "(= (sbv_to_int #x80) (- 128))", "(= (sbv_to_int #x7f) 127)",
        "(= ((_ int_to_bv 1) (- 1)) #b1)", "(= (sbv_to_int #b1) (- 1))",
        "(bvnego #x80)", "(not (bvnego #x7f))",
        "(bvuaddo #xff #x01)", "(not (bvsaddo #xff #x01))",
        "(bvsaddo #x7f #x01)", "(not (bvuaddo #x7f #x01))",
        "(bvumulo #x80 #x02)", "(bvsmulo #x80 #xff)",
        "(not (bvumulo #x0f #x02))", "(not (bvsmulo #x0f #x02))",
        "(= ((_ int_to_bv 129) 680564733841876926926749214863536422913) (_ bv1 129))",
        "(= ((_ int_to_bv 129) (- 680564733841876926926749214863536422913))"
        " (_ bv680564733841876926926749214863536422911 129))",
    ]
    cases = [
        ("exact", "ALL", "(assert (not (and " + " ".join(exact) + ")))", "Refutation",
         "  intro h\n  apply h\n  decide\n"),
        ("round-trip", "ALL", "(declare-const x (_ BitVec 8))"
         "(assert (distinct ((_ int_to_bv 8) (sbv_to_int x)) x))", "Refutation",
         "  intro x bad\n  exact bad BitVec.ofInt_toInt\n"),
        ("signedness", "ALL", "(declare-const x (_ BitVec 8))"
         "(assert (= (ubv_to_int x) 255))(assert (= (sbv_to_int x) (- 1)))", "¬ Refutation",
         "  intro h\n  apply h (255 : BitVec 8)\n  decide\n"),
        ("overflow", "QF_BV", "(declare-const x (_ BitVec 8))"
         "(assert (bvsaddo x #x01))(assert (not (bvuaddo x #x01)))", "¬ Refutation",
         "  intro h\n  apply h (127 : BitVec 8)\n  decide\n"),
        ("horn-model", "HORN", "(declare-fun P ((_ BitVec 8)) Bool)(assert (P #xff))"
         "(assert (forall ((x (_ BitVec 8))) (=> (P x) (P ((_ int_to_bv 8) (ubv_to_int x))))))"
         "(assert (forall ((x (_ BitVec 8))) (=> (and (P x) (< (ubv_to_int x) 0)) false)))",
         "Problem", "  refine ⟨(fun _ => True), True.intro, (fun _ _ => True.intro), ?_⟩\n"
         "  intro x _ bad\n  exact Int.not_lt.mpr (Int.natCast_nonneg x.toNat) bad\n"),
        ("horn-overflow", "HORN", "(declare-fun P ((_ BitVec 8)) Bool)(assert (P #x7f))"
         "(assert (forall ((x (_ BitVec 8))) (=> (and (P x) (bvsaddo x #x01)) false)))",
         "¬ Problem", "  rintro ⟨p, fact, safety⟩\n  exact safety 127 fact (by decide)\n"),
    ]
    for name, logic, body, target, proof in cases:
        source, output = tmp / f"bv-conv-{name}.smt2", tmp / f"bv-conv-{name}"
        source.write_text(f"(set-logic {logic}){body}(check-sat)")
        run(source, "--out", output)
        generated = check_generated(lean, output, goal="Problem" if logic == "HORN" else "Refutation")
        assert generated.startswith("import Init\n")
        completed = output / "Query.lean"
        completed.write_text(generated.split("-- Proofs\n", 1)[0]
                             + f"theorem checked : {target} := by\n" + unfold_statement(generated, target) + proof)
        check_lean(lean, completed, complete=True)
    for name, tail, reason in [
        ("width", "(assert (= ((_ int_to_bv 0) 1) #b1))", "expecting bit-width > 0"),
        ("sort", "(assert (= (ubv_to_int 1) 1))", "expecting bit-vector term"),
        ("overflow", "(assert (bvuaddo #x1 #b1))", "comparable bit-vector"),
        ("unused", "(define-fun bad () (_ BitVec 4) ((_ int_to_bv 4) (^ 2 3)))", "POW"),
        ("hidden", "(define-fun ignore ((x (_ BitVec 4))) Bool true)"
         "(assert (ignore ((_ int_to_bv 4) (^ 2 3))))", "POW"),
        ("wide", "(assert (= ((_ int_to_bv 4294967296) 1) #b1))", "conversion width exceeds"),
        ("wide-alias", "(define-fun bad () (_ BitVec 8) ((_ |int2bv| 4294967296) 1))", "conversion width exceeds"),
        ("erased", "(assert (let ((unused ((_ int_to_bv 4294967296) 1))) true))", "conversion width exceeds"),
        ("observation", "(get-value (((_ int2bv 4294967296) 1)))", "conversion width exceeds"),
    ]:
        source, output = tmp / f"bv-conv-invalid-{name}.smt2", tmp / f"bv-conv-invalid-{name}"
        source.write_text("(set-logic ALL)(assert (= ((_ int_to_bv 8) (- 1)) #xff))(check-sat)" + tail)
        assert reason in run(source, "--out", output, code=1).stderr
        assert not output.exists()
    print("BV conversion CLI passed: six completed proofs, standalone SMT/CHC output, and later-error protection")


