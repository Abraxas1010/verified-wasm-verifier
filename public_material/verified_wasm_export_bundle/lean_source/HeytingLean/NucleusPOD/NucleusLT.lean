import HeytingLean.NucleusPOD.Foundation

namespace HeytingLean
namespace NucleusPOD

/-!
Layer 2: Nucleus as Lawvere-Tierney Topology
Generated from `NucleusPOD_Lean_Proof_Catalog.docx`.
-/

/-- Truth-value nucleus action modeled on the same carrier as `closure`. -/
def j (x : Nat) : Nat := closure x

/-- `j` preserves truth/top. -/
theorem lt_top : j closureFloor = closureFloor := by
  simp [j, closure, closureFloor]

/-- `j` is idempotent. -/
theorem lt_idempotent (x : Nat) : j (j x) = j x := by
  unfold j
  exact closure_idempotent x

/-- `j` preserves finite meets (`Nat.min`) on the `Nat`-ordered truth model. -/
theorem lt_meet (a b : Nat) : j (Nat.min a b) = Nat.min (j a) (j b) := by
  by_cases h : a ≤ b
  · have h' : closure a ≤ closure b := closure_monotone h
    calc
      j (Nat.min a b) = closure a := by simp [j, Nat.min_eq_left h]
      _ = Nat.min (j a) (j b) := by
        simpa [j] using (Nat.min_eq_left h').symm
  · have hba : b ≤ a := Nat.le_of_not_ge h
    have h' : closure b ≤ closure a := closure_monotone hba
    calc
      j (Nat.min a b) = closure b := by simp [j, Nat.min_eq_right hba]
      _ = Nat.min (j a) (j b) := by
        simpa [j] using (Nat.min_eq_right h').symm

end NucleusPOD
end HeytingLean
