import HeytingLean.Moonshine.Modular.JInvariant
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

set_option autoImplicit false

noncomputable section

namespace HeytingLean.Moonshine.Modular

open UpperHalfPlane

open scoped CongruenceSubgroup
open scoped MatrixGroups

local notation "GL2R" => GL (Fin 2) ℝ

private def sl2zToGL2R (γ : SL(2, ℤ)) : GL2R :=
  -- This matches the coercion used by the `SL(2, ℤ)` action on `ℍ`.
  Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)

private lemma sl2zToGL2R_mem_Gamma1 (γ : SL(2, ℤ)) :
    sl2zToGL2R γ ∈ (Γ(1) : Subgroup GL2R) := by
  -- `Γ(1)` (as a subgroup of `GL(2, ℝ)`) is the image of the subgroup `Γ(1) ⊆ SL(2, ℤ)`.
  refine ⟨γ, CongruenceSubgroup.mem_Gamma_one γ, ?_⟩
  -- `mapGL` is defined as `toGL ∘ map`.
  simp [sl2zToGL2R, Matrix.SpecialLinearGroup.mapGL]

lemma E4_Gamma1_smul (γ : GL2R) (hγ : γ ∈ (Γ(1) : Subgroup GL2R)) (τ : ℍ) :
    E4 (γ • τ) = (denom γ τ) ^ (4 : ℤ) * E4 τ := by
  simpa using (SlashInvariantForm.slash_action_eqn'' (f := E4) (hγ := hγ) (z := τ))

lemma E6_Gamma1_smul (γ : GL2R) (hγ : γ ∈ (Γ(1) : Subgroup GL2R)) (τ : ℍ) :
    E6 (γ • τ) = (denom γ τ) ^ (6 : ℤ) * E6 τ := by
  simpa using (SlashInvariantForm.slash_action_eqn'' (f := E6) (hγ := hγ) (z := τ))

theorem kleinJ_Gamma1_invariant (γ : GL2R) (hγ : γ ∈ (Γ(1) : Subgroup GL2R)) (τ : ℍ) :
    kleinJ (γ • τ) = kleinJ τ := by
  set d : ℂ := denom γ τ
  have hd : d ≠ 0 := by simpa [d] using denom_ne_zero γ τ
  have hd12 : d ^ 12 ≠ 0 := pow_ne_zero 12 hd

  have hE4 : E4 (γ • τ) = d ^ 4 * E4 τ := by
    simpa [d, zpow_ofNat] using E4_Gamma1_smul (γ := γ) (hγ := hγ) (τ := τ)
  have hE6 : E6 (γ • τ) = d ^ 6 * E6 τ := by
    simpa [d, zpow_ofNat] using E6_Gamma1_smul (γ := γ) (hγ := hγ) (τ := τ)

  have hE4pow : (E4 (γ • τ)) ^ 3 = d ^ 12 * (E4 τ) ^ 3 := by
    calc
      (E4 (γ • τ)) ^ 3 = (d ^ 4 * E4 τ) ^ 3 := by simp [hE4]
      _ = (d ^ 4) ^ 3 * (E4 τ) ^ 3 := by simp [mul_pow]
      _ = d ^ 12 * (E4 τ) ^ 3 := by
            have : (d ^ 4) ^ 3 = d ^ 12 := by
              simpa using (pow_mul d 4 3).symm
            simp [this]

  have hE6pow : (E6 (γ • τ)) ^ 2 = d ^ 12 * (E6 τ) ^ 2 := by
    calc
      (E6 (γ • τ)) ^ 2 = (d ^ 6 * E6 τ) ^ 2 := by simp [hE6]
      _ = (d ^ 6) ^ 2 * (E6 τ) ^ 2 := by simp [mul_pow]
      _ = d ^ 12 * (E6 τ) ^ 2 := by
            have : (d ^ 6) ^ 2 = d ^ 12 := by
              simpa using (pow_mul d 6 2).symm
            simp [this]

  have hden :
      (E4 (γ • τ)) ^ 3 - (E6 (γ • τ)) ^ 2 = d ^ 12 * ((E4 τ) ^ 3 - (E6 τ) ^ 2) := by
    simp [hE4pow, hE6pow, mul_sub]

  -- Cancel the common `d^12` scaling factor from the numerator and denominator.
  have hj :
      kleinJ (γ • τ) =
        (d ^ 12 * ((1728 : ℂ) * (E4 τ) ^ 3)) / (d ^ 12 * ((E4 τ) ^ 3 - (E6 τ) ^ 2)) := by
    unfold kleinJ
    rw [hE4pow, hE6pow]
    -- Fold the common factor in the denominator and commute the numerator into `c * a`.
    rw [← mul_sub (d ^ 12) ((E4 τ) ^ 3) ((E6 τ) ^ 2)]
    simp [mul_left_comm]

  calc
    kleinJ (γ • τ)
        = (d ^ 12 * ((1728 : ℂ) * (E4 τ) ^ 3)) / (d ^ 12 * ((E4 τ) ^ 3 - (E6 τ) ^ 2)) := hj
    _ = ((1728 : ℂ) * (E4 τ) ^ 3) / ((E4 τ) ^ 3 - (E6 τ) ^ 2) := by
          simpa [mul_assoc] using
            mul_div_mul_left ((1728 : ℂ) * (E4 τ) ^ 3) ((E4 τ) ^ 3 - (E6 τ) ^ 2) hd12
    _ = kleinJ τ := by
          simp [kleinJ]

theorem kleinJ_sl2_invariant (γ : SL(2, ℤ)) (τ : ℍ) : kleinJ (γ • τ) = kleinJ τ := by
  -- The `SL(2, ℤ)` action on `ℍ` is via the inclusion into `GL(2, ℝ)`.
  -- We rewrite the action explicitly to match the `GL(2,ℝ)`-form of the invariance lemma.
  simpa [sl2zToGL2R] using
    (kleinJ_Gamma1_invariant (γ := sl2zToGL2R γ) (hγ := sl2zToGL2R_mem_Gamma1 γ) (τ := τ))

theorem kleinJ₀_sl2_invariant (γ : SL(2, ℤ)) (τ : ℍ) : kleinJ₀ (γ • τ) = kleinJ₀ τ := by
  -- Avoid relying on simp unfolding the `SL(2,ℤ)` action.
  simpa [kleinJ₀] using congrArg (fun z : ℂ ↦ z - 744) (kleinJ_sl2_invariant (γ := γ) (τ := τ))

end HeytingLean.Moonshine.Modular
