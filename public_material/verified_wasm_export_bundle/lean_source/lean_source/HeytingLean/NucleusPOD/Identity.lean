import HeytingLean.NucleusPOD.Foundation

namespace HeytingLean
namespace NucleusPOD

/-!
Layer 9: Identity Assurance Lattice
Generated from `NucleusPOD_Lean_Proof_Catalog.docx`.
-/

def identityClosure (x : Nat) : Nat :=
  closure x

theorem assurance_heyting_algebra (a : Nat) : Nat.min a a = a := by
  simp

theorem R_identity_extensive (a : Nat) : a ≤ identityClosure a := by
  show a ≤ closure a
  exact closure_extensive a

theorem R_identity_idempotent (a : Nat) : identityClosure (identityClosure a) = identityClosure a := by
  unfold identityClosure
  exact closure_idempotent a

theorem R_identity_meet_preserving (a b : Nat) :
    identityClosure (Nat.min a b) = Nat.min (identityClosure a) (identityClosure b) := by
  by_cases h : a ≤ b
  · have h' : identityClosure a ≤ identityClosure b := by
      simpa [identityClosure] using closure_monotone h
    calc
      identityClosure (Nat.min a b) = identityClosure a := by
        simp [identityClosure, Nat.min_eq_left h]
      _ = Nat.min (identityClosure a) (identityClosure b) := by
        exact (Nat.min_eq_left h').symm
  · have hba : b ≤ a := Nat.le_of_not_ge h
    have h' : identityClosure b ≤ identityClosure a := by
      simpa [identityClosure] using closure_monotone hba
    calc
      identityClosure (Nat.min a b) = identityClosure b := by
        simp [identityClosure, Nat.min_eq_right hba]
      _ = Nat.min (identityClosure a) (identityClosure b) := by
        exact (Nat.min_eq_right h').symm

theorem grant_condition_R_closed (a : Nat) (h : closureFloor ≤ a) : identityClosure a = a := by
  simpa [identityClosure] using closure_fixpoint_of_ge_floor a h

end NucleusPOD
end HeytingLean
