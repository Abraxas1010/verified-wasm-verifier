import HeytingLean.LoF.Combinators.AIGOracle

/-!
Sanity checks for `HeytingLean.LoF.Combinators.AIGOracle`.

This is compile-only + tiny proof checks.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.LoF
open HeytingLean.LoF.Combinators
open HeytingLean.LoF.LoFPrimary

namespace AIGOracleSanity

def A : LoFPrimary.Expr 1 := LoFPrimary.Expr.var ⟨0, by decide⟩

def r0 : AIGOracle.Ref 1 :=
  { expr := A
    inputs := fun _ => false
  }

def r1 : AIGOracle.Ref 1 :=
  { expr := A
    inputs := fun _ => true
  }

example : AIGOracle.eval r0 = LoFPrimary.eval (n := 1) A (fun _ => false) := by
  simpa [r0] using (AIGOracle.eval_eq_lof_eval (n := 1) r0)

example : AIGOracle.eval r1 = LoFPrimary.eval (n := 1) A (fun _ => true) := by
  simpa [r1] using (AIGOracle.eval_eq_lof_eval (n := 1) r1)

end AIGOracleSanity

end LoF
end Tests
end HeytingLean

