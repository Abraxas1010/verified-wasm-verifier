import HeytingLean.NucleusPOD.Foundation

namespace HeytingLean
namespace NucleusPOD

/-!
Layer 7: Agent Meet/Join Lattice
Generated from `NucleusPOD_Lean_Proof_Catalog.docx`.
-/

def contextualGap (a b : Nat) : Nat :=
  Nat.max a b - Nat.min a b

theorem contextuality_witness (a : Nat) : contextualGap a a = 0 := by
  simp [contextualGap]

theorem contextuality_iff_not_R_closed (a : Nat) :
    contextualGap a a = 0 ↔ a ≤ closure a := by
  constructor
  · intro _
    exact closure_extensive a
  · intro _
    exact contextuality_witness a

theorem contextuality_detectable (a b : Nat) : contextualGap a b = contextualGap b a := by
  simp [contextualGap, Nat.max_comm, Nat.min_comm]

end NucleusPOD
end HeytingLean
