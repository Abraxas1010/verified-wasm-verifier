import HeytingLean.Moonshine.Modular.Eta

set_option autoImplicit false

namespace HeytingLean.Moonshine.Modular

open UpperHalfPlane

/-- The modular discriminant `Δ(τ) := η(τ)^24` as a function on `ℍ`. -/
noncomputable def Delta (τ : ℍ) : ℂ :=
  (eta τ) ^ (24 : Nat)

lemma Delta_ne_zero (τ : ℍ) : Delta τ ≠ 0 := by
  simp [Delta, eta_ne_zero]

end HeytingLean.Moonshine.Modular

