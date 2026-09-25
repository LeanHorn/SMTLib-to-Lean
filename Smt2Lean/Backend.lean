import cvc5
import Smt.Reconstruct.Prop
import Smt.Reconstruct.Builtin

/-!
Parser and Boolean term-reconstruction dependencies for the translator.

Import the registered Prop and builtin reconstructors so the backend can map SMT
Booleans to Lean propositions, including declared constants and equality.
The parser driver and executable reconstruction smoke test follow in tasks 2.2
and 2.3; this module establishes the dependency build and native linking first.
-/
