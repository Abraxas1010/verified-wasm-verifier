import HeytingLean.Compiler.TensorLogic.ParseFacts

/-!
Sanity checks for the lightweight decimal float parser used by TensorLogic CLIs.

We don't test exact IEEE equality; we only assert correct sign handling for negatives.
-/

namespace HeytingLean.Tests.TensorLogic.FloatParseSanity

open HeytingLean.Compiler.TensorLogic

private def val (s : String) : Float :=
  match parseFloatLit s with
  | .ok f => f
  | .error _ => 0.0

example : val "-1.2" < -1.0 := by native_decide
example : val "-0.2" < 0.0 := by native_decide
example : val "0.2" > 0.0 := by native_decide

end HeytingLean.Tests.TensorLogic.FloatParseSanity

