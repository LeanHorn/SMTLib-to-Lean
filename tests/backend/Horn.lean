import Smt2Lean.Chc

open Smt2Lean.Backend Smt2Lean.Chc

private def require (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def headName : ClauseHead → String
  | .relation atom => atom.relation.name
  | .falsity => "false"

private def checkRejected (name input : String) (ordinal : Nat) (reason : String)
    (mode : ParseMode := .chc) : IO Unit := do
  let inspected ← IO.mkRef false
  let result ← (parseAndInspectQuery input (fun _ => inspected.set true)
    (name := name) (mode := mode)).run
  require (!(← inspected.get)) s!"{name}: invalid input reached inspect"
  match result with
  | .ok _ => throw (IO.userError s!"{name}: unexpectedly accepted")
  | .error error =>
    let message := toString error
    let context := if mode == .chc then "query 1: " else ""
    require (message.contains s!"{name}:" && message.contains s!": {context}command {ordinal}:" && message.contains reason)
      s!"{name}: wrong diagnostic: {message}"

private def checkParser : IO Unit := do
  let path := "tests/chc/lh_sum_rec.smt2"
  let input ← IO.FS.readFile path
  let calls ← IO.mkRef 0
  (parseAndInspectQuery input (name := path) (mode := .chc) fun query => do
    calls.modify (· + 1)
    let #[relation] := query.declarations
      | throw (.error "expected one declaration")
    require (relation.name == "k_1") "expected k_1"
    let signature ← ofExcept relation.term.getSort
    require (signature.isFunction) "expected a function declaration"
    let domains ← ofExcept signature.getFunctionDomainSorts
    require (domains.size == 1 && domains.all (·.isInteger) &&
      (← ofExcept signature.getFunctionCodomainSort).isBoolean)
      "expected k_1 : Int → Bool"
    require (query.assertionTerms.size == 3) "expected three assertions"
    let relations ← collectRelations query.declarations
    require (relations.size == 1) "expected one CHC relation"
    let clauses ← query.assertionTerms.mapIdxM fun i assertion => extractClause relations (i + 1) assertion
    require (clauses.map (·.assertionNumber) == #[1, 2, 3]) "wrong assertion numbers"
    require (clauses.map (·.binders.size) == #[3, 5, 3]) "lh_sum_rec lost universal variables"
    require (clauses.map (headName ∘ (·.head)) == #["k_1", "k_1", "false"])
      "wrong lh_sum_rec heads"
    for clause in clauses, count in #[3, 5, 5] do
      require (clause.premises.size == 1) "expected one unflattened premise per clause"
      let premise := clause.premises[0]!
      require ((← ofExcept premise.getKind) == .AND && premise.getNumChildren == count)
        "lh_sum_rec premise changed"
    for assertion in query.assertionTerms do
      require ((← ofExcept assertion.getSort).isBoolean &&
        (← ofExcept assertion.getKind) == .FORALL)
        "expected a universally quantified Bool assertion"
    require (query.invoked == #["set-logic", "declare-fun", "assert", "assert", "assert"])
      s!"unexpected invocation trace: {query.invoked}"
  ).runIO
  require ((← calls.get) == 1) "expected exactly one inspection"
  checkRejected path input 1 "unsupported logic" (mode := .smt)
  -- CHC mode uses the same sort, operator, and command checks as ordinary SMT.
  for (name, suffix, ordinal, reason) in #[
    ("bound-string", "(assert (forall ((x String)) true))\n(check-sat)",
      2, "unsupported bound variable sort"),
    ("power", "(assert (forall ((x Int)) (= (^ x 2) 0)))\n(check-sat)",
      2, "unsupported operator: POW"),
    ("missing-check", "(assert true)", 3, "expected one check-sat"),
    ("repeated-check", "(check-sat)\n(check-sat)", 3, "after check-sat"),
    ("trailing-command", "(check-sat)\n(push 1)", 3, "after check-sat")
  ] do
    checkRejected s!"horn-{name}" ("(set-logic HORN)\n" ++ suffix) ordinal reason

private def checkClauses : IO Unit := do
  let path := "tests/translation/chc/clauses.smt2"
  let input ← IO.FS.readFile path
  (parseAndInspectQuery input (name := path) (mode := .chc) fun query => do
    let relations ← collectRelations query.declarations
    require (relations.map (·.name) == #["P", "R", "done", "True", "a b", "unused"])
      "wrong relations or missing unused declaration"
    require (relations.map (fun r => r.argumentSorts.map toString) ==
      #[#["Int"], #["Int", "Bool", "Int"], #[], #[], #["Bool", "Int"], #["Int", "Bool"]])
      "wrong relation signatures"
    for relation in relations, declaration in query.declarations do
      require (relation.term == declaration.term) "relation identity changed"
    let clauses ← query.assertionTerms.mapIdxM fun i assertion => extractClause relations (i + 1) assertion
    require (clauses.map (·.assertionNumber) == (List.range 16).toArray.map (· + 1))
      "wrong clause count or source assertion numbers"
    require (clauses.map (·.binders.size) == #[0, 0, 0, 0, 0, 3, 3, 1, 5, 0, 0, 3, 4, 4, 2, 4])
      "wrong binder counts"
    require (clauses.map (·.premises.size) == #[0, 0, 0, 0, 0, 0, 2, 2, 1, 1, 0, 1, 1, 1, 1, 1])
      "wrong premise counts"
    require (clauses.map (headName ∘ (·.head)) ==
      #["P", "R", "done", "True", "a b", "P", "R", "done", "R", "false", "false", "false", "R", "R", "R", "R"])
      "wrong clause heads"
    let facts ← (query.assertionTerms.extract 0 5).mapM (recognizeFact relations)
    require (facts.map (·.relation.term) == (query.declarations.extract 0 5).map (·.term))
      "facts refer to the wrong declarations"
    require (facts.map (fun f => f.arguments.map toString) ==
      #[#["0"], #["7", "(and true (not false))", "(- 9 4)"], #[], #[], #["(= 1 2)", "(+ 10 2)"]])
      "fact arguments changed or were reordered"
    -- Distinct antecedents catch accidental reversal or loss of chained implications.
    let some chained := clauses[6]? | throw (.error "missing chained implication")
    require (chained.premises.map toString == #["(P x)", "(and (> y x) b)"])
      "nested implication premises changed"
    let .relation head := chained.head | throw (.error "expected a relation head")
    require (head.arguments.map toString == #["(+ x 1)", "b", "x"])
      "head arguments were normalized or reordered"
    let some multi := clauses[7]? | throw (.error "missing multi-operand implication")
    require (multi.premises.map toString == #["(> x 0)", "(P x)"])
      "multi-operand implication premises changed"
    let some shadowed := clauses[8]? | throw (.error "missing shadowing clause")
    let #[outer, inner, flag, onlyBody, unused] := shadowed.binders
      | throw (.error "missing shadowed, premise-only, or unused variables")
    require (shadowed.binders.map (fun b => toString b.sort) == #["Int", "Int", "Bool", "Int", "Bool"])
      "binder sorts changed"
    require (outer.term != inner.term &&
      (← ofExcept outer.term.getSymbol) == "x" && (← ofExcept inner.term.getSymbol) == "x")
      "shadowed binders lost their native identity"
    let .relation head := shadowed.head | throw (.error "expected a relation head")
    require (head.arguments == #[outer.term, flag.term, inner.term]) "shadowed head captured a variable"
    require (shadowed.premises[0]![2]![0]! == onlyBody.term &&
      (← ofExcept unused.term.getSymbol) == "unused")
      "premise-only or unused binder changed"
    let some nested := clauses[15]? | throw (.error "missing let/quantifier clause")
    let #[outerX, outerB, innerX, innerB] := nested.binders
      | throw (.error "let expansion lost leading binders")
    require (outerX.term != innerX.term && outerB.term != innerB.term)
      "let aliases collapsed shadowed Bool/Int binders"
    let .relation head := nested.head | throw (.error "expected a relation head")
    require (head.arguments[0]![0]! == innerX.term &&
      head.arguments[1]! == outerB.term && head.arguments[2]! == outerX.term)
      "let expansion captured a head argument"
    require (nested.premises[0]![2]!.getChildren == #[innerB.term, outerB.term])
      "let expansion captured a guard variable"
  ).runIO

private def expectError (name reason : String) (action : cvc5.Env Unit) : IO Unit := do
  match ← action.run with
  | .ok _ => throw (IO.userError s!"{name}: unexpectedly accepted")
  | .error error =>
    require ((toString error).contains reason) s!"{name}: wrong diagnostic: {error}"

private def checkRejectedFacts : IO Unit := do
  for (name, body, reason) in #[
    ("integer-constant", "(declare-const x Int)", "unsupported CHC declaration 'x'"),
    ("integer-function", "(declare-fun f (Int) Int)", "unsupported CHC declaration 'f'"),
    ("string-domain", "(declare-fun P (String) Bool)", "unsupported declaration sort"),
    ("nested-relation", "(declare-fun P (Int) Bool)\n(declare-fun R (Bool) Bool)\n(assert (R (P 0)))",
      "relation inside a relation argument"),
    ("hidden-relation", "(declare-fun P (Int) Bool)\n(declare-fun R (Bool) Bool)\n(assert (R (not (P 0))))",
      "relation inside a relation argument"),
    ("nullary-argument", "(declare-const p Bool)\n(declare-fun R (Bool) Bool)\n(assert (R p))",
      "relation inside a relation argument"),
    ("literal", "(assert true)", "expected a relation fact"),
    ("negative-fact", "(declare-const p Bool)\n(assert (not p))", "expected a relation fact")
  ] do
    expectError name reason <| parseAndInspectQuery
      ("(set-logic HORN)\n" ++ body ++ "\n(check-sat)") (name := name) (mode := .chc)
      fun query => do
        let relations ← collectRelations query.declarations
        for assertion in query.assertionTerms do discard <| recognizeFact relations assertion

private def checkBoundData : IO Unit := do
  let input := "(set-logic HORN)\n(declare-const p Bool)\n(declare-fun R (Bool) Bool)\n" ++
    "(assert (forall ((p Bool)) (R p)))\n" ++
    "(assert (forall ((p Bool)) (=> (not p) (R p))))\n(check-sat)"
  (parseAndInspectQuery input (mode := .chc) fun query => do
    let relations ← collectRelations query.declarations
    let quantified := query.assertionTerms[0]!
    let bound := quantified[0]![0]!
    let some atom ← relationAtom? relations quantified[1]!
      | throw (.error "expected R applied to a bound Bool variable")
    require (atom.relation.name == "R" && atom.arguments == #[bound])
      "bound Bool argument lost its identity"
    require ((← relationAtom? relations bound).isNone)
      "bound Bool variable was mistaken for the nullary relation named p"
    let problem ← validateQuery query
    let some clause := problem.clauses[1]? | throw (.error "missing bound Bool guard")
    let #[.guard guard] := clause.premises | throw (.error "not p should be a theory guard")
    let #[binder] := clause.binders | throw (.error "missing bound p")
    let some global := relations[0]? | throw (.error "missing global p")
    require (guard[0]! == binder.term && binder.term != global.term)
      "bound Bool guard was confused with a global relation"
  ).runIO

private def checkRejectedClauses : IO Unit := do
  for (name, assertion, reason) in #[
    ("existential", "(exists ((x Int)) (P x))", "leading forall"),
    ("forall-exists", "(forall ((x Int)) (exists ((y Int)) (P y)))", "leading forall"),
    ("quantified-premise", "(=> (forall ((x Int)) (P x)) false)", "leading forall"),
    ("quantified-head", "(=> done (forall ((x Int)) (P x)))", "leading forall"),
    ("quantified-argument", "(R 0 (exists ((p Bool)) p) 1)", "leading forall"),
    ("disjunctive-head", "(forall ((x Int)) (=> (P x) (or (P x) done)))", "as CHC head"),
    ("theory-head", "(forall ((x Int)) (=> (P x) (> x 0)))", "as CHC head"),
    ("true-head", "(=> done true)", "as CHC head")
  ] do
    let input := "(set-logic HORN)\n(declare-fun P (Int) Bool)\n" ++
      "(declare-fun R (Int Bool Int) Bool)\n(declare-const done Bool)\n" ++
      s!"(assert {assertion})\n(check-sat)"
    expectError name reason <| parseAndInspectQuery input (name := name) (mode := .chc)
      fun query => do
        let relations ← collectRelations query.declarations
        for h : i in [:query.assertionTerms.size] do
          discard <| extractClause relations (i + 1) query.assertionTerms[i]

private def checkNativeIdentity : IO Unit :=
  expectError "native identity" "undeclared CHC relation" do
    let tm ← cvc5.TermManager.new
    let bool ← tm.getBooleanSort
    let declared ← tm.mkConst bool "P"
    let other ← tm.mkConst bool "P"
    let relations ← collectRelations #[{ name := "P", term := declared }]
    require (declared != other) "expected distinct native symbols"
    discard <| recognizeFact relations other

private def relationCount (clause : Clause Premise) : Nat :=
  clause.premises.foldl (fun n premise => match premise with
    | .relation _ => n + 1
    | .guard _ => n) 0

private def premiseText : Premise → String
  | .relation atom => s!"relation {atom.relation.name} {atom.arguments.map toString}"
  | .guard term => s!"guard {term}"

/-- Compare structure across metadata variants without retaining native terms. -/
private def snapshot (problem : Problem) : String :=
  toString (problem.relations.map (fun r => (r.name, r.argumentSorts.map toString)),
    problem.clauses.map fun c => (c.assertionNumber,
      c.binders.map (fun b => (toString b.term, toString b.sort)),
      c.premises.map premiseText, match c.head with
        | .relation a => (a.relation.name, a.arguments.map toString)
        | .falsity => ("false", #[])))

private def checkProblems : IO Unit := do
  let path := "tests/chc/lh_sum_rec.smt2"
  let input ← IO.FS.readFile path
  let reference ← IO.mkRef (none : Option String)
  for metadata in #["(set-info :status sat)", "(set-info :status unsat)",
      "(set-info :status unknown)", ""] do
    let calls ← IO.mkRef 0
    (parseAndInspectProblem (input.replace "(set-info :status sat)" metadata) (name := path)
      fun problem => do
        calls.modify (· + 1)
        require (problem.relations.map (·.name) == #["k_1"] &&
          problem.clauses.map (·.binders.size) == #[3, 5, 3] &&
          problem.clauses.map (headName ∘ (·.head)) == #["k_1", "k_1", "false"])
          "validated lh_sum_rec lost relations, binders, or heads"
        require (problem.clauses.map relationCount == #[0, 1, 1] &&
          problem.clauses.map (·.premises.size) == #[3, 5, 5])
          "expected a guarded fact, recursive rule, and false-head rule"
        match ← reference.get with
        | none => reference.set (some (snapshot problem))
        | some expected => require (snapshot problem == expected) "metadata changed the CHC problem"
    ).runIO
    require ((← calls.get) == 1) "expected one validated problem"
  let path := "tests/translation/chc/clauses.smt2"
  (parseAndInspectProblem (← IO.FS.readFile path) (name := path) fun problem => do
    require (problem.relations.size == 6 && problem.clauses.size == 16)
      "validated fixture lost declarations or clauses"
    require (problem.clauses.map relationCount == #[0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 3, 1, 1, 1, 1])
      "wrong relation-premise counts"
    require (problem.clauses.map (·.premises.size) == #[0, 0, 0, 0, 0, 0, 3, 2, 3, 1, 0, 7, 4, 2, 3, 3])
      "wrong flattened premise counts"
    let some clause := problem.clauses[11]? | throw (.error "missing nonlinear rule")
    require (clause.premises.map premiseText == #[
      "relation P #[x]", "guard (> x 0)", "relation P #[y]",
      "guard (or (and (< x 0) (> y 0)) (not cond))", "relation done #[]",
      "guard (= cond (> (+ (* x y) (- x)) (abs y)))", "guard (not cond)"])
      "premises were reordered, dropped, or flattened inside a theory guard"
  ).runIO

private def checkRejectedProblems : IO Unit := do
  for (name, assertion, reason) in #[
    ("negated-relation", "(=> (not (P x)) done)", "inside a theory guard"),
    ("negated-nullary", "(=> (not done) (P x))", "inside a theory guard"),
    ("relation-equality", "(=> (= (P x) cond) done)", "inside a theory guard"),
    ("relation-xor", "(=> (xor cond (P x)) done)", "inside a theory guard"),
    ("relation-distinct", "(=> (distinct cond (P x)) done)", "inside a theory guard"),
    ("relation-ite-condition", "(=> (ite (P x) cond true) done)", "inside a theory guard"),
    ("relation-ite-branch", "(=> (ite cond (P x) true) done)", "inside a theory guard"),
    ("relation-int-ite", "(P (ite (P x) x 0))", "inside a relation argument"),
    ("quantified-ite", "(P (ite (exists ((y Int)) (= x y)) x 0))", "leading forall"),
    ("relation-disjunction", "(=> (or (> x 0) (P x)) done)", "inside a theory guard"),
    ("relation-implication", "(=> (=> cond (P x)) done)", "inside a theory guard"),
    ("relation-under-negations", "(=> (not (not (P x))) done)", "inside a theory guard"),
    ("relation-argument", "(=> (R x (P x) x) done)", "inside a relation argument"),
    ("relation-xor-argument", "(R x (xor cond (P x)) x)", "inside a relation argument"),
    ("relation-distinct-argument", "(R x (distinct cond (P x)) x)", "inside a relation argument"),
    ("unsupported-guard", "(=> (> (^ x 2) 0) done)", "unsupported operator"),
    ("unsupported-head-argument", "(P (^ x 2))", "unsupported operator"),
    ("let-unsupported-guard", "(let ((half (^ x 2))) (=> (> half 0) done))", "unsupported operator"),
    ("let-unsupported-head", "(let ((rest (^ x 2))) (P rest))", "unsupported operator"),
    ("let-hidden-relation", "(let ((guard (not (P x)))) (=> guard done))", "inside a theory guard"),
    ("let-hidden-argument", "(let ((arg (P x))) (R x arg x))", "inside a relation argument"),
    ("let-hidden-quantifier", "(let ((guard (exists ((y Int)) (= x y)))) (=> guard (P x)))", "leading forall"),
    ("hinted-negative", "(! (=> (not (P x)) done) :pattern ((P x)) :qid bad)", "inside a theory guard"),
    ("hinted-existential", "(! (exists ((y Int)) (! (P y) :pattern ((P y)))) :qid bad)", "leading forall"),
    ("hinted-unsupported", "(! (P (^ x 2)) :pattern ((P x)))", "unsupported operator"),
    ("existential", "(exists ((y Int)) (P y))", "leading forall"),
    ("disjunctive-head", "(=> (P x) (or (P x) done))", "as CHC head")
  ] do
    let path := s!"tests/{name}.smt2"
    -- A later bad assertion must reject the entire problem before its callback.
    let input := "(set-logic HORN)\n(declare-fun P (Int) Bool)\n" ++
      "(declare-fun R (Int Bool Int) Bool)\n(declare-const done Bool)\n" ++
      s!"(assert (P 0))\n(assert done)\n(assert (forall ((x Int) (cond Bool)) {assertion}))\n(check-sat)"
    let inspected ← IO.mkRef false
    match ← (parseAndInspectProblem input (fun _ => inspected.set true) (name := path)).run with
    | .ok _ => throw (IO.userError s!"{name}: unexpectedly accepted")
    | .error error =>
      let message := toString error
      require (message.contains s!"{path}:7:1: query 1: command 7:" && message.contains "clause 3:" &&
        message.contains reason) s!"{name}: wrong diagnostic: {message}"
    require (!(← inspected.get)) s!"{name}: returned a partial problem"

private def checkLocalCorpus : IO Unit := do
  let mut total := 0
  for (file, count) in #[
    ("lh_sum_rec", 3), ("lh_abs_neg", 5), ("flux_sum_off_by_one", 5), ("flux_bsearch", 15)
  ] do
    let path := s!"tests/chc/{file}.smt2"
    (parseAndInspectProblem (← IO.FS.readFile path) (name := path) fun problem => do
      require (problem.clauses.size == count) s!"{file}: lost a clause"
      require (problem.clauses.map (·.assertionNumber) == (Array.range count).map (· + 1))
        s!"{file}: clause order changed"
    ).runIO
    total := total + count
  require (total == 28) "wrong local corpus size"
  IO.println "Local CHC corpus passed: all four files retain their 28 clauses"

def main : IO Unit := do
  checkParser
  checkClauses
  checkRejectedFacts
  checkBoundData
  checkRejectedClauses
  checkNativeIdentity
  checkProblems
  checkLocalCorpus
  checkRejectedProblems
  IO.println "Horn validation passed: lh_sum_rec (3 clauses) and combined fixture (16 clauses)"
  IO.println "Metadata, clause diagnostics, and whole-problem rejection passed; no solver query invoked."
