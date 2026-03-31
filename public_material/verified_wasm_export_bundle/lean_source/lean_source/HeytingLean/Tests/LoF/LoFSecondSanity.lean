import HeytingLean.LoF.LoFSecond.BridgePrimary

/-!
Compile-only sanity checks for the LoF second-degree (re-entry) layer.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.LoF.LoFSecond

#check Expr
#check Step
#check Steps
#check Tri
#check eval
#check valueSet
#check Eqv
#check eqv_iff_valueSet_eq
#check step_sound
#check steps_sound
#check Expr.ofPrimary
#check eval_ofPrimary

example : Eqv (n := 0) (Expr.mark (Expr.reentry (n := 0))) (Expr.reentry (n := 0)) := by
  intro ρ
  simp [eval]

example : valueSet (n := 0) (Expr.reentry (n := 0)) Tri.u =
    (Finset.univ : Finset (Fin 0 → Tri)) := by
  ext ρ
  simp [valueSet, eval]

example : valueSet (n := 0) (Expr.reentry (n := 0)) Tri.f =
    (∅ : Finset (Fin 0 → Tri)) := by
  ext ρ
  simp [valueSet, eval]

end LoF
end Tests
end HeytingLean
