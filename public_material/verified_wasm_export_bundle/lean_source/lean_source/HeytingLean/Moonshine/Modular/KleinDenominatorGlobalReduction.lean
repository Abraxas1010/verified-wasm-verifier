import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.SlashInvariantForms

import HeytingLean.Moonshine.Modular.Eisenstein
import HeytingLean.Moonshine.Modular.KleinDenominatorNonvanishing

set_option autoImplicit false

noncomputable section

namespace HeytingLean.Moonshine.Modular

open UpperHalfPlane ModularGroup SlashInvariantForm Complex CongruenceSubgroup

open scoped Modular MatrixGroups

/-- The Klein denominator `E4(τ)^3 - E6(τ)^2` as a function on `ℍ`. -/
noncomputable def kleinDenom (τ : ℍ) : ℂ :=
  (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat)

lemma kleinDenom_eq (τ : ℍ) : kleinDenom τ = (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) := rfl

/-!
## SL(2,ℤ) transformation

The key point: even without a global nonvanishing proof, we can reduce any global claim about
zeros of `kleinDenom` to the standard fundamental domain `𝒟` (mathlib: `ModularGroup.fd`).
-/

lemma kleinDenom_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    kleinDenom (γ • τ) = (denom γ τ) ^ (12 : Nat) * kleinDenom τ := by
  have hE4 : E4 (γ • τ) = (denom γ τ) ^ (4 : ℤ) * E4 τ := by
    simpa using (SlashInvariantForm.slash_action_eqn_SL'' (f := E4) (hγ := mem_Gamma_one γ) τ)
  have hE6 : E6 (γ • τ) = (denom γ τ) ^ (6 : ℤ) * E6 τ := by
    simpa using (SlashInvariantForm.slash_action_eqn_SL'' (f := E6) (hγ := mem_Gamma_one γ) τ)
  -- Rewrite `zpow` with positive exponent to `pow` so we can use `pow_mul`.
  have hE4' : E4 (γ • τ) = (denom γ τ) ^ (4 : Nat) * E4 τ := by
    simpa [zpow_ofNat] using hE4
  have hE6' : E6 (γ • τ) = (denom γ τ) ^ (6 : Nat) * E6 τ := by
    simpa [zpow_ofNat] using hE6
  -- Expand and factor out `denom^12` explicitly (avoids simp getting stuck on the coerced action).
  -- Name the underlying `GL(2,ℝ)` element used in the `SL(2,ℤ)` action.
  let γR : GL (Fin 2) ℝ :=
    Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ)
  have hact : (γ • τ) = (γR • τ) := by rfl
  set d : ℂ := denom γR (τ : ℂ)
  have hdenom : denom γ τ = d := by rfl
  have hE4d : E4 (γR • τ) = d ^ (4 : Nat) * E4 τ := by
    have h := hE4'
    simp [d, hact] at h
    exact h
  have hE6d : E6 (γR • τ) = d ^ (6 : Nat) * E6 τ := by
    have h := hE6'
    simp [d, hact] at h
    exact h
  have hd43 : (d ^ (4 : Nat)) ^ (3 : Nat) = d ^ (12 : Nat) := by
    simpa using (pow_mul d 4 3).symm
  have hd62 : (d ^ (6 : Nat)) ^ (2 : Nat) = d ^ (12 : Nat) := by
    simpa using (pow_mul d 6 2).symm
  calc
    kleinDenom (γ • τ) = kleinDenom (γR • τ) := by simp [hact]
    _ = (d ^ (4 : Nat) * E4 τ) ^ (3 : Nat) - (d ^ (6 : Nat) * E6 τ) ^ (2 : Nat) := by
          simp [kleinDenom, hE4d, hE6d]
    _ = ((E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat)) * d ^ (12 : Nat) := by
          -- Put all `d`-powers on the right, then factor with `sub_mul`.
          -- We pin the two arithmetic rewrites to keep `simp` deterministic.
          simp [mul_pow, sub_mul, mul_comm, hd43, hd62]
    _ = (denom γ τ) ^ (12 : Nat) * kleinDenom τ := by
          -- `denom γ τ` unfolds to `denom γR (τ : ℂ)`.
          simp [kleinDenom, d, hdenom, mul_comm]

theorem exists_mem_fd_of_kleinDenom_eq_zero {τ : ℍ} (hτ : kleinDenom τ = 0) :
    ∃ ξ : ℍ, ξ ∈ ModularGroup.fd ∧ kleinDenom ξ = 0 := by
  rcases ModularGroup.exists_smul_mem_fd τ with ⟨γ, hγ⟩
  refine ⟨γ • τ, hγ, ?_⟩
  -- Avoid `simp` rewriting the group action into coercions; use `kleinDenom_smul` explicitly.
  calc
    kleinDenom (γ • τ) = (denom γ τ) ^ (12 : Nat) * kleinDenom τ := kleinDenom_smul (γ := γ) (τ := τ)
    _ = 0 := by simp [hτ]

theorem kleinDenom_ne_zero_of_nonzero_on_fd
    (hfd : ∀ τ : ℍ, τ ∈ ModularGroup.fd → kleinDenom τ ≠ 0) :
    ∀ τ : ℍ, kleinDenom τ ≠ 0 := by
  intro τ
  rcases ModularGroup.exists_smul_mem_fd τ with ⟨γ, hγ⟩
  have h := hfd (γ • τ) hγ
  intro h0
  -- If `kleinDenom τ = 0` then also `kleinDenom (γ • τ) = 0`, contradicting `h`.
  have : kleinDenom (γ • τ) = 0 := by
    calc
      kleinDenom (γ • τ) = (denom γ τ) ^ (12 : Nat) * kleinDenom τ := kleinDenom_smul (γ := γ) (τ := τ)
      _ = 0 := by simp [h0]
  exact h this

/--
If `kleinDenom` vanishes anywhere on `ℍ`, then it vanishes in the standard fundamental domain,
at imaginary part bounded by any `A` which certifies nonvanishing for `Im(τ) > A`.

This packages the current *partial* nonvanishing result into a clean global reduction lemma.
-/
theorem exists_mem_fd_and_im_le_of_kleinDenom_eq_zero
    {A : ℝ} (hA : ∀ τ : ℍ, A < τ.im → kleinDenom τ ≠ 0) {τ : ℍ} (hτ : kleinDenom τ = 0) :
    ∃ ξ : ℍ, ξ ∈ ModularGroup.fd ∧ kleinDenom ξ = 0 ∧ ξ.im ≤ A := by
  rcases exists_mem_fd_of_kleinDenom_eq_zero (τ := τ) hτ with ⟨ξ, hξfd, hξ0⟩
  refine ⟨ξ, hξfd, hξ0, ?_⟩
  -- Contrapose: if `A < ξ.im` then `kleinDenom ξ ≠ 0`, contradicting `hξ0`.
  refine le_of_not_gt ?_
  intro hlt
  exact (hA ξ hlt) hξ0

theorem exists_mem_fd_and_im_le_of_kleinDenom_eq_zero' {τ : ℍ} (hτ : kleinDenom τ = 0) :
    ∃ ξ : ℍ, ξ ∈ ModularGroup.fd ∧ kleinDenom ξ = 0 ∧
      ξ.im ≤ Classical.choose exists_im_bound_kleinDenom_ne_zero := by
  classical
  -- Use the canonical witness from `Classical.choose`.
  let A : ℝ := Classical.choose exists_im_bound_kleinDenom_ne_zero
  have hA : ∀ τ : ℍ, A < τ.im → kleinDenom τ ≠ 0 :=
    Classical.choose_spec exists_im_bound_kleinDenom_ne_zero
  simpa [A] using
    (exists_mem_fd_and_im_le_of_kleinDenom_eq_zero (A := A) (hA := hA) (τ := τ) hτ)

end HeytingLean.Moonshine.Modular
