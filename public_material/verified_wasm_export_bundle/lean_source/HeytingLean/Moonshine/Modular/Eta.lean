import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

set_option autoImplicit false

namespace HeytingLean.Moonshine.Modular

open UpperHalfPlane

/-- Dedekind eta as a function on `ℍ` (wrapper around `Mathlib.NumberTheory.ModularForms.DedekindEta`). -/
noncomputable def eta (τ : ℍ) : ℂ :=
  ModularForm.eta (τ : ℂ)

lemma eta_ne_zero (τ : ℍ) : eta τ ≠ 0 := by
  have hz : (τ : ℂ) ∈ UpperHalfPlane.upperHalfPlaneSet := τ.property
  simpa [eta] using ModularForm.eta_ne_zero (z := (τ : ℂ)) hz

lemma differentiableAt_eta (τ : ℍ) : DifferentiableAt ℂ (fun z : ℂ ↦ ModularForm.eta z) (τ : ℂ) := by
  have hz : (τ : ℂ) ∈ UpperHalfPlane.upperHalfPlaneSet := τ.property
  simpa using ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet (z := (τ : ℂ)) hz

end HeytingLean.Moonshine.Modular

