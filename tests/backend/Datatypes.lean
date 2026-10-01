import tests.backend.Support

namespace Smt2Lean.Tests

open Lean Meta Qq Backend Translate

def checkDatatypes (env : Environment) : IO Unit := do
  runQuery env "datatype-constructor-order" "
    (set-logic ALL)
    (declare-datatype Pair ((pair (left Int) (right Int))))
    (assert (= (pair 1 2) (pair 3 4)))
    (check-sat)" fun query => do
      unless query.datatypes.size == 1 && query.sorts.isEmpty do
        throwError "datatype declaration was lost or treated as an arbitrary carrier"
      let fields := query.datatypes[0]!.types[0]!.constructors[0]!.fields
      unless fields.map (·.name) == #["left", "right"] && fields[0]!.selector != fields[1]!.selector do
        throwError "selector metadata lost its field order or identity"
      let value ← defineRefutation query
      let type : Q(Type) ← pure (mkConst `SMT.Datatypes.g0.T0_Pair)
      let pair : Q(Int → Int → $type) ←
        pure (mkConst `SMT.Datatypes.g0.T0_Pair.c0_pair)
      checkEqual value q($pair 1 2 = $pair 3 4 → False)
      checkEmission value
  runQuery env "record-projections" "
    (set-logic ALL)
    (declare-datatype Pair ((pair (left Int) (right Int))))
    (assert (and (= (left (pair 1 2)) 1) (= (right (pair 1 2)) 2)))
    (check-sat)" fun query =>
      checkRefutation query q((1 : Int) = 1 ∧ (2 : Int) = 2 → False)
  let selectorDeclarations := "
    (declare-datatype D ((has (field Int)) (other (tag Int))))"
  runQuery env "selector-interpretation" ("(set-logic ALL)" ++ selectorDeclarations ++ "
    (assert (= (field (has 7)) 7))
    (assert (distinct (field (other 1)) (field (other 2))))
    (assert (forall ((d D)) (= (field d) (field d))))
    (check-sat)") fun query => do
      let value ← defineRefutation query
      let d : Q(Type) ← pure (mkConst `SMT.Datatypes.g0.T0_D)
      let other : Q(Int → $d) ← pure (mkConst `SMT.Datatypes.g0.T0_D.c1_other)
      let field : Q(($d → Int) → $d → Int) ← pure (mkConst `SMT.Selectors.g0.T0_D.s0_0_field)
      -- One function for the entire query, outside the source quantifier.
      checkEqual value q(∀ choice : $d → Int,
        (7 : Int) = 7 ∧ choice ($other 1) ≠ choice ($other 2) ∧
          (∀ x : $d, $field choice x = $field choice x) → False)
      checkEmission value
  runProblem env "selector-chc-interpretation" ("(set-logic HORN)" ++ selectorDeclarations ++ "
    (declare-fun R (Int) Bool)
    (assert (R (field (has 7))))
    (assert (=> (= (field (other 1)) (field (other 2))) false))
    (check-sat)") fun problem => do
      let value ← defineProblem problem
      let d : Q(Type) ← pure (mkConst `SMT.Datatypes.g0.T0_D)
      let other : Q(Int → $d) ← pure (mkConst `SMT.Datatypes.g0.T0_D.c1_other)
      checkEqual value q(∃ choice : $d → Int, ∃ r : Int → Prop,
        r 7 ∧ (choice ($other 1) = choice ($other 2) → False))
      checkEmission value .problem
  for file in ["constructors", "chc", "selectors", "selectors-chc"] do
    let input ← IO.FS.readFile s!"tests/translation/datatypes/{file}.smt2"
    if file == "chc" || file == "selectors-chc" then
      runProblem env file input fun problem => do
        unless file != "chc" || (problem.datatypes.size == 2 && problem.relations.size == 3 && problem.clauses.size == 5) do
          throwError "datatype CHC lost declarations, relations, or clauses"
        let value ← defineProblem problem
        checkStatementAxioms `Problem
        checkEmission value .problem
    else
      runQuery env file input fun query => do
        unless file != "constructors" || (query.datatypes.size == 8 && query.assertions.size == 13) do
          throwError "datatype fixture lost declarations or assertions"
        let value ← defineRefutation query
        checkStatementAxioms `Refutation
        checkEmission value

end Smt2Lean.Tests
