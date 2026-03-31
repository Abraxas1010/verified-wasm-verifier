import HeytingLean.Genesis

/-!
# Genesis Virtual Untying Sanity
-/

namespace HeytingLean.Tests.Genesis

open HeytingLean.Genesis
open CoGame

#check virtualUnroll
#check virtualInterpretUnroll
#check lifeVirtualApproxExpr
#check virtual_unroll_zero
#check virtual_unroll_zero_life
#check virtual_interpret_unroll_life_anchor
#check virtual_unroll_nucleus_layer2

example : virtualUnroll 0 CoGame.Life = (0 : SetTheory.PGame) := by
  exact virtual_unroll_zero_life

example (G : CoGame) : virtualUnroll 0 G = (0 : SetTheory.PGame) := by
  exact virtual_unroll_zero G

example (n : Nat) :
    virtualInterpretUnroll n (virtualUnroll n CoGame.Life) = nesting n := by
  exact virtual_interpret_unroll_life_anchor n

example (n : Nat) :
    collapseNucleus (exprSupport (lifeVirtualApproxExpr n))
      =
      collapseNucleus (collapseNucleus (exprSupport (lifeVirtualApproxExpr n))) := by
  exact virtual_unroll_nucleus_layer2 n

end HeytingLean.Tests.Genesis
