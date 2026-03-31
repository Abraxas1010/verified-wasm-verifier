import HeytingLean.Moonshine.Modular.KleinRatioModularForm

set_option autoImplicit false

noncomputable section

namespace HeytingLean.Moonshine.Modular

open UpperHalfPlane

theorem gate_hDeltaSmul (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : ℍ) :
    DeltaLevelOne (g • τ) = (UpperHalfPlane.denom g τ) ^ (12 : Nat) * DeltaLevelOne τ := by
  simpa using hDeltaSmul g τ

theorem gate_hDiv (τ : ℍ) :
    kleinDenom τ / DeltaLevelOne τ = (1728 : ℂ) := by
  simpa using hDiv_of_Delta_smul τ

end HeytingLean.Moonshine.Modular
