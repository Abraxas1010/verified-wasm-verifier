import HeytingLean.NucleusPOD.Foundation

namespace HeytingLean
namespace NucleusPOD

/-!
Layer 6: Geometric Morphisms and Bridges
Generated from `NucleusPOD_Lean_Proof_Catalog.docx`.
-/

def bridgeMap (x : Nat) : Nat :=
  closure x

theorem bridge_adjunction (x y : Nat) (hClosed : closure y = y) :
    bridgeMap x ≤ y ↔ x ≤ y := by
  constructor
  · intro h
    exact Nat.le_trans (closure_extensive x) (by simpa [bridgeMap] using h)
  · intro hxy
    have hLift : closure x ≤ closure y := closure_monotone hxy
    calc
      bridgeMap x = closure x := rfl
      _ ≤ closure y := hLift
      _ = y := hClosed

theorem bridge_left_exact (a b : Nat) :
    bridgeMap (Nat.min a b) = Nat.min (bridgeMap a) (bridgeMap b) := by
  by_cases h : a ≤ b
  · have h' : closure a ≤ closure b := closure_monotone h
    calc
      bridgeMap (Nat.min a b) = closure a := by simp [bridgeMap, Nat.min_eq_left h]
      _ = Nat.min (bridgeMap a) (bridgeMap b) := by
        simpa [bridgeMap] using (Nat.min_eq_left h').symm
  · have hba : b ≤ a := Nat.le_of_not_ge h
    have h' : closure b ≤ closure a := closure_monotone hba
    calc
      bridgeMap (Nat.min a b) = closure b := by simp [bridgeMap, Nat.min_eq_right hba]
      _ = Nat.min (bridgeMap a) (bridgeMap b) := by
        simpa [bridgeMap] using (Nat.min_eq_right h').symm

end NucleusPOD
end HeytingLean
