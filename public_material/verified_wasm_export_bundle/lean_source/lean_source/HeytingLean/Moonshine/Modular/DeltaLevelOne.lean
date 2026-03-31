import HeytingLean.Moonshine.Modular.KleinDenominatorGlobalReduction
import HeytingLean.Moonshine.Modular.KleinDenominatorTailMajorant

set_option autoImplicit false

noncomputable section

namespace HeytingLean.Moonshine.Modular

open UpperHalfPlane

/--
Level-one discriminant used for closeout:
`Δ₁(τ) := (1/1728) * (E4(τ)^3 - E6(τ)^2) = (1/1728) * kleinDenom(τ)`.
-/
noncomputable def DeltaLevelOne (τ : ℍ) : ℂ :=
  (1 / (1728 : ℂ)) * kleinDenom τ

lemma hDeltaLevelOneSmul (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : ℍ) :
    DeltaLevelOne (g • τ) = (UpperHalfPlane.denom g τ) ^ (12 : Nat) * DeltaLevelOne τ := by
  calc
    DeltaLevelOne (g • τ)
        = (1 / (1728 : ℂ)) * kleinDenom (g • τ) := rfl
    _ = (1 / (1728 : ℂ)) * ((UpperHalfPlane.denom g τ) ^ (12 : Nat) * kleinDenom τ) := by
          rw [kleinDenom_smul]
    _ = (UpperHalfPlane.denom g τ) ^ (12 : Nat) * DeltaLevelOne τ := by
          simp [DeltaLevelOne, mul_assoc, mul_comm]

lemma DeltaLevelOne_ne_zero (τ : ℍ) : DeltaLevelOne τ ≠ 0 := by
  have h1728 : (1 / (1728 : ℂ)) ≠ 0 := by norm_num
  exact mul_ne_zero h1728 (kleinDenom_ne_zero_global τ)

lemma kleinDenom_eq_1728_mul_DeltaLevelOne (τ : ℍ) :
    kleinDenom τ = (1728 : ℂ) * DeltaLevelOne τ := by
  have h1728 : (1728 : ℂ) ≠ 0 := by norm_num
  calc
    kleinDenom τ = (1728 : ℂ) * ((1 / (1728 : ℂ)) * kleinDenom τ) := by
      field_simp [h1728]
    _ = (1728 : ℂ) * DeltaLevelOne τ := by simp [DeltaLevelOne]

lemma kleinDenom_div_DeltaLevelOne_eq_1728 (τ : ℍ) :
    kleinDenom τ / DeltaLevelOne τ = (1728 : ℂ) := by
  exact (div_eq_iff (DeltaLevelOne_ne_zero τ)).2 (kleinDenom_eq_1728_mul_DeltaLevelOne τ)

end HeytingLean.Moonshine.Modular
