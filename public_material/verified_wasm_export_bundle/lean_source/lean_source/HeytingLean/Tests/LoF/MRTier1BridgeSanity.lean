import Mathlib.Tactic
import HeytingLean.LoF.MRSystems.Tier1Bridge

/-!
Sanity checks for `LoF/MRSystems/Tier1Bridge.lean`.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.ClosingTheLoop.MR
open HeytingLean.LoF.MRSystems

namespace MRTier1Toy

def toyH : Set (Unit → Bool) := Set.univ

def toySystem : MRSystem where
  A := Unit
  B := Bool
  H := toyH
  f := fun _ => true
  hf := by simp [toyH]
  Sel := Set.univ
  Φf := fun _ => ⟨fun _ => true, by simp [toyH]⟩
  hΦf := by simp

def mapTrue : AdmissibleMap toySystem :=
  ⟨fun _ => true, by simp [toySystem, toyH]⟩

def mapFalse : AdmissibleMap toySystem :=
  ⟨fun _ => false, by simp [toySystem, toyH]⟩

def toySelector : Selector toySystem :=
  ⟨fun b =>
      match b with
      | true => mapFalse
      | false => mapTrue,
    by simp [toySystem]⟩

def toyRI (b : toySystem.B) : RightInverseAt toySystem b where
  β := fun g => ⟨fun _ => g, by simp [toySystem]⟩
  right_inv := by
    intro g
    rfl

end MRTier1Toy

open MRTier1Toy

-- A Tier-1 selector determines an MR core and its transition maps are admissible.
example : (MRCore.ofTier1Selector toySystem toySelector).R true ∈ toySystem.H := by
  exact MRCore.ofTier1Selector_R_mem_H (S := toySystem) (Φ := toySelector) true

-- Closing a selector at `b` preserves the induced transition function at `b`.
example :
    (MRCore.ofTier1Selector toySystem (closeSelector toySystem true (toyRI true) toySelector)).R true =
      (MRCore.ofTier1Selector toySystem toySelector).R true := by
  exact Tier1.R_at_closeSelector_eq (S := toySystem) (b := true) (RI := toyRI true) toySelector

-- Hence one-step Moore semantics from `b` is preserved.
example :
    (MRCore.ofTier1Selector toySystem (closeSelector toySystem true (toyRI true) toySelector)).semFrom true [()] =
      (MRCore.ofTier1Selector toySystem toySelector).semFrom true [()] := by
  exact Tier1.sem_singleton_closeSelector_eq (S := toySystem) (b := true) (RI := toyRI true) toySelector ()

end LoF
end Tests
end HeytingLean
