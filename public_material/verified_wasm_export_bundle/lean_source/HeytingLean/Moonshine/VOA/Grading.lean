import HeytingLean.Moonshine.VOA.Jacobi

set_option autoImplicit false

noncomputable section

namespace HeytingLean.Moonshine.VOA

/-- Minimal grading data needed for downstream trace bookkeeping. -/
structure WeightGrading (A : VOAData) where
  wt : A.V → ℤ
  vacuum_wt : wt A.vacuum = 0
  translation_wt_le : ∀ v : A.V, wt (A.T v) ≤ wt v + 1

/-- Trivial grading on the toy scalar VOA. -/
def scalarWeightGrading : WeightGrading scalarVOA where
  wt := fun _ => 0
  vacuum_wt := rfl
  translation_wt_le := by
    intro v
    simp

end HeytingLean.Moonshine.VOA
