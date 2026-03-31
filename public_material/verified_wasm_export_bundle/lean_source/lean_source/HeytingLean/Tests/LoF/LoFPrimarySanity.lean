import HeytingLean.LoF.LoFPrimary.Normalization

/-!
Compile-only sanity checks for the LoF primary syntax + rewrite + canonicalization layer.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.LoF.LoFPrimary

#check Expr
#check Step
#check Steps
#check eval
#check trueSet
#check Eqv
#check eqv_iff_trueSet_eq
#check step_sound
#check steps_sound

example : trueSet (n := 0) (Expr.void) = (∅ : Finset (Fin 0 → Bool)) := by
  ext ρ
  simp [trueSet, eval]

example : trueSet (n := 0) (Expr.marked (n := 0)) = (Finset.univ : Finset (Fin 0 → Bool)) := by
  ext ρ
  simp [Expr.marked, trueSet, eval]

example (A : Expr 1) : Eqv (n := 1) (Expr.juxt A A) A := by
  exact step_sound (n := 1) (Step.calling A)

end LoF
end Tests
end HeytingLean

