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
  for file in ["constructors", "chc"] do
    let input ← IO.FS.readFile s!"tests/translation/datatypes/{file}.smt2"
    if file == "chc" then
      runProblem env file input fun problem => do
        unless problem.datatypes.size == 2 && problem.relations.size == 3 && problem.clauses.size == 5 do
          throwError "datatype CHC lost declarations, relations, or clauses"
        let value ← defineProblem problem
        checkStatementAxioms `Problem
        checkEmission value .problem
    else
      runQuery env file input fun query => do
        unless query.datatypes.size == 8 && query.assertions.size == 13 do
          throwError "datatype fixture lost declarations or assertions"
        let value ← defineRefutation query
        checkStatementAxioms `Refutation
        checkEmission value

end Smt2Lean.Tests
