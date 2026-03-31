import HeytingLean.NucleusPOD.Foundation

namespace HeytingLean
namespace NucleusPOD

/-!
Layer 3: Sheaf Gluing and Transport
Generated from `NucleusPOD_Lean_Proof_Catalog.docx`.
-/

def cocycleValue (a b c : Nat) : Nat :=
  closure (a + b + c)

theorem cocycle_from_meet_pres (a b c : Nat) :
    cocycleValue (Nat.min a b) c 0 = closure (Nat.min a b + c) := by
  simp [cocycleValue]

theorem cocycle_auto_for_R_closed (a b c : Nat) :
    closure (cocycleValue a b c) = cocycleValue a b c := by
  unfold cocycleValue
  exact closure_idempotent (a + b + c)

end NucleusPOD
end HeytingLean
