import Mathlib.Tactic
import HeytingLean.LoF.MRSystems.YBridge

/-!
Sanity checks for `LoF/MRSystems/YBridge.lean`.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.LoF
open HeytingLean.LoF.MRSystems
open OmegaCompletePartialOrder

noncomputable section

/-! ## SKY: `Y` yields rewrite fixed points -/

example (f : Comb) : Comb.IsStepFixedPt f (Comb.app .Y f) :=
  Comb.isStepFixedPt_Y f

example (f : Comb) : Comb.IsStepsFixedPt f (Comb.app .Y f) :=
  Comb.isStepsFixedPt_Y f

/-! ## LawfulFix: `Fix.fix` yields equality fixed points for continuous maps -/

example : Function.IsFixedPt (id : Part Nat → Part Nat) (Fix.fix (id : Part Nat → Part Nat)) := by
  simpa using
    (fix_isFixedPt_of_ωScottContinuous (α := Part Nat) (f := (id : Part Nat → Part Nat))
      (ωScottContinuous.id))

/-! ## Derived (M,R) closure from lawful fixpoints (scoped) -/

abbrev toyCore : MRCore :=
  { A := Bool
    B := Part Nat
    M := fun _ => (⊥ : Part Nat)
    R := fun b => fun _a => b }

example : (MRCore.withFixM (m := toyCore)).ClosedDiag := by
  have hR : ∀ a : toyCore.A, ωScottContinuous (fun b : toyCore.B => toyCore.R b a) := by
    intro a
    simpa [toyCore] using (ωScottContinuous.id : ωScottContinuous (id : toyCore.B → toyCore.B))
  exact MRCore.withFixM_closedDiag (m := toyCore) hR

-- Closure is equivalently a fixed-point equation for the higher-order `closureOp`.
example :
    (toyCore.ClosedDiag ↔ Function.IsFixedPt (MRCore.closureOp toyCore) toyCore.M) :=
  MRCore.closedDiag_iff_isFixedPt_closureOp (m := toyCore)

-- If the higher-order closure operator is ωScottContinuous, we can take a lawful fixpoint.
example : (MRCore.withFixMetabolism (m := toyCore)).ClosedDiag := by
  have h : ωScottContinuous (MRCore.closureOp toyCore) := by
    -- Here `closureOp` is definitionally `id` on metabolism maps.
    simpa [MRCore.closureOp, toyCore] using
      (ωScottContinuous.id :
        ωScottContinuous (id : (toyCore.A → toyCore.B) → (toyCore.A → toyCore.B)))
  exact MRCore.withFixMetabolism_closedDiag (m := toyCore) h

end

end LoF
end Tests
end HeytingLean
