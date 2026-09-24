import Smt2Lean

def main (args : List String) : IO UInt32 := do
  IO.println s!"smt2lean: {args}"
  return 0
