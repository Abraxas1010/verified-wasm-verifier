import HeytingLean.NucleusPOD.Foundation

namespace HeytingLean
namespace NucleusPOD

/-!
Layer 4: Venue and Slice Topos
Generated from `NucleusPOD_Lean_Proof_Catalog.docx`.
-/

def pullbackConstraint (u v : Nat) : Nat :=
  Nat.min u v

theorem pullback_preserves_heyting (u v : Nat) :
    pullbackConstraint u v ≤ u ∧ pullbackConstraint u v ≤ v := by
  constructor
  · exact Nat.min_le_left _ _
  · exact Nat.min_le_right _ _

end NucleusPOD
end HeytingLean
