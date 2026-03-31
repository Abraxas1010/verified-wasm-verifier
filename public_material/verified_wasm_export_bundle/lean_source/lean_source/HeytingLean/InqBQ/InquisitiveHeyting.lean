import Mathlib.Data.SetLike.Basic
import HeytingLean.InqBQ.Support

namespace HeytingLean
namespace InqBQ

open Set

variable {sig : Signature}

/-- Downward-closed propositions over information states. -/
structure InfoProp (M : InfoModel sig) where
  carrier : Set (Set M.W)
  downward :
    ∀ ⦃s t : Set M.W⦄, t ⊆ s → s ∈ carrier → t ∈ carrier

namespace InfoProp

variable {M : InfoModel sig}

instance : SetLike (InfoProp M) (Set M.W) where
  coe P := P.carrier
  coe_injective' := by
    intro P Q h
    cases P
    cases Q
    cases h
    rfl

@[ext] theorem ext {P Q : InfoProp M} (h : ∀ s : Set M.W, s ∈ P ↔ s ∈ Q) : P = Q := by
  apply SetLike.ext'
  ext s
  exact h s

instance : PartialOrder (InfoProp M) where
  le P Q := (P : Set (Set M.W)) ⊆ (Q : Set (Set M.W))
  le_refl _ := by intro _ hs; exact hs
  le_trans _ _ _ hPQ hQR := by intro _ hs; exact hQR (hPQ hs)
  le_antisymm P Q hPQ hQP := by
    ext s
    exact ⟨fun hs => hPQ hs, fun hs => hQP hs⟩

instance : SemilatticeInf (InfoProp M) where
  __ := inferInstanceAs (PartialOrder (InfoProp M))
  inf P Q :=
    { carrier := {s | s ∈ P ∧ s ∈ Q}
      downward := by
        intro s t hts hs
        exact ⟨P.downward hts hs.1, Q.downward hts hs.2⟩ }
  inf_le_left _ _ := by
    intro s hs
    exact hs.1
  inf_le_right _ _ := by
    intro s hs
    exact hs.2
  le_inf := by
    intro P Q R hPQ hPR s hs
    exact ⟨hPQ hs, hPR hs⟩

/-- The information proposition supported by a formula under a fixed assignment. -/
def supportProp (M : InfoModel sig) (g : Assignment M.D) (φ : Formula sig) : InfoProp M :=
  { carrier := {s | supports M s g φ}
    downward := by
      intro s t hts hs
      exact supports_mono M hs hts }

@[simp] theorem mem_supportProp (M : InfoModel sig) (g : Assignment M.D) (φ : Formula sig)
    (s : Set M.W) :
    s ∈ supportProp M g φ ↔ supports M s g φ := Iff.rfl

end InfoProp

end InqBQ
end HeytingLean
