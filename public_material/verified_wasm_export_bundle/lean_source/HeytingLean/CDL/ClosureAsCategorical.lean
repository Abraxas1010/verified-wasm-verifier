import HeytingLean.CDL.Coalgebra.MealyBridge
import HeytingLean.ClosingTheLoop

/-!
# CDL: Closure loop as a (trivial-parameter) Mealy dynamics

The ClosingTheLoop layer already provides an (autonomous) Mealy machine
`HeytingLean.ClosingTheLoop.Semantics.MRBridge.closeMachine` whose state is an admissible selector
and whose single input symbol `⋆` advances the selector by the loop-closing operator.

This file repackages that construction in the CDL layer:
- we view the closure loop as a `ParaMealy` coalgebra (with trivial parameter space `PUnit`),
- we record the key “semantic closure” facts as rewrite lemmas.

This is the precise point where the CDL coalgebra language meets the (M,R) closure operator.
-/

namespace HeytingLean
namespace CDL

open HeytingLean.ClosingTheLoop
open HeytingLean.ClosingTheLoop.Semantics
open HeytingLean.ClosingTheLoop.Semantics.MRBridge

namespace Closure

universe u v

variable {S : MR.MRSystem.{u, v}} {b : S.B} (RI : MR.RightInverseAt S b)

/-- The closure loop as a `ParaMealy` machine (parameters are trivial: the chosen `RI` is fixed). -/
def closeMachinePara : Coalgebra.ParaMealy PUnit (MR.AdmissibleMap S) (MR.Selector S) :=
  Coalgebra.ParaMealy.ofClosingMealy (I := PUnit) (O := MR.AdmissibleMap S) (S := MR.Selector S)
    (closeMachine (S := S) (b := b) RI)

@[simp] theorem closeMachinePara_step (Φ : MR.Selector S) :
    (closeMachinePara (S := S) (b := b) RI).transition (PUnit.unit, PUnit.unit, Φ) =
      (MR.closeSelector S b RI Φ, MR.closeSelector S b RI Φ b) := by
  -- Unfold and use the ClosingTheLoop definition of `closeMachine`.
  simp [closeMachinePara, Coalgebra.ParaMealy.ofClosingMealy, closeMachine, MR.closeSelector]

/-- The closure loop stabilizes after one additional step (idempotence). -/
theorem closeMachinePara_idem (Φ : MR.Selector S) :
    let m := closeMachinePara (S := S) (b := b) RI
    (m.transition (PUnit.unit, PUnit.unit, (m.transition (PUnit.unit, PUnit.unit, Φ)).1)).1 =
      (m.transition (PUnit.unit, PUnit.unit, Φ)).1 := by
  intro m
  -- Compute the first component after one step.
  have h₁ :
      (m.transition (PUnit.unit, PUnit.unit, Φ)).1 = MR.closeSelector S b RI Φ := by
    simp [m]
  -- Compute the first component after stepping from the already-closed selector.
  have h₂ :
      (m.transition (PUnit.unit, PUnit.unit, MR.closeSelector S b RI Φ)).1 =
        MR.closeSelector S b RI (MR.closeSelector S b RI Φ) := by
    simp [m]
  -- Reduce the goal to `closeSelector` idempotence.
  rw [h₁]
  rw [h₂]
  exact MR.closeSelector.idem (S := S) (b := b) (RI := RI) Φ

end Closure

end CDL
end HeytingLean
