import Mathlib.Order.Nucleus
import HeytingLean.InqBQ.Classical
import HeytingLean.InqBQ.InquisitiveHeyting

namespace HeytingLean
namespace InqBQ

open Set
open InfoProp

variable {sig : Signature} {M : InfoModel sig}

/-- Singleton-based truth-conditional closure on downward-closed information propositions. -/
def truthClosure (P : InfoProp M) : InfoProp M :=
  { carrier := {s | ∀ w, w ∈ s → ({w} : Set M.W) ∈ P}
    downward := by
      intro s t hts hs w hw
      exact hs w (hts hw) }

theorem le_truthClosure (P : InfoProp M) : P ≤ truthClosure P := by
  intro s hs w hw
  exact P.downward (by
    intro u hu
    have huEq : u = w := by simpa using hu
    simpa [huEq] using hw) hs

theorem truthClosure_idempotent_le (P : InfoProp M) :
    truthClosure (truthClosure P) ≤ truthClosure P := by
  intro s hs w hw
  have hSingleton : ({w} : Set M.W) ∈ truthClosure P := hs w hw
  exact hSingleton w (by
    change w = w
    rfl)

theorem truthClosure_inf (P Q : InfoProp M) :
    truthClosure (P ⊓ Q) = truthClosure P ⊓ truthClosure Q := by
  ext s
  constructor
  · intro hs
    exact ⟨fun w hw => (hs w hw).1, fun w hw => (hs w hw).2⟩
  · intro hs w hw
    exact ⟨hs.1 w hw, hs.2 w hw⟩

/-- The singleton truth-closure packaged as a nucleus on persistent information propositions. -/
def truthClosure_is_nucleus : Nucleus (InfoProp M) where
  toFun := truthClosure
  map_inf' := by
    intro P Q
    exact truthClosure_inf P Q
  idempotent' := truthClosure_idempotent_le
  le_apply' := le_truthClosure

/-- Classical formulas are fixed points of the singleton truth-closure. -/
theorem truthClosure_supportProp_eq_of_classical
    (g : Assignment M.D) {φ : Formula sig} (hClass : Formula.isClassical φ) :
    truthClosure (supportProp M g φ) = supportProp M g φ := by
  ext s
  constructor
  · intro hs
    apply (classical_support_iff_worldwise M g (φ := φ) hClass).2
    intro w hw
    have hSingleton : ({w} : Set M.W) ∈ supportProp M g φ := hs w hw
    exact (classical_truth M w g hClass).1 hSingleton
  · intro hs
    exact le_truthClosure (supportProp M g φ) hs

end InqBQ
end HeytingLean
