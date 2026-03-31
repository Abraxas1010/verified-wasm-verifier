import HeytingLean.Moonshine.Modular.DeltaLevelOne

set_option autoImplicit false

noncomputable section

namespace HeytingLean.Moonshine.Modular

open UpperHalfPlane

/-- Unconditional weight-12 transform for the closeout discriminant `DeltaLevelOne`. -/
theorem hDeltaSmul :
    ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℤ, ∀ τ : ℍ,
      DeltaLevelOne (g • τ) = (UpperHalfPlane.denom g τ) ^ (12 : Nat) * DeltaLevelOne τ := by
  intro g τ
  simpa using hDeltaLevelOneSmul g τ

/-- Unconditional global ratio identity for the closeout discriminant `DeltaLevelOne`. -/
theorem hDiv_of_Delta_smul :
    ∀ τ : ℍ, kleinDenom τ / DeltaLevelOne τ = (1728 : ℂ) := by
  intro τ
  simpa using kleinDenom_div_DeltaLevelOne_eq_1728 τ

end HeytingLean.Moonshine.Modular
