import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

import HeytingLean.Quantum.TWA.Core

/-!
# TWA Dissipation (Phase 1.5)

This module is an "algebraic only" companion to `HeytingLean.Quantum.TWA.Core`.

It provides:
- a simple **complex-valued effective Hamiltonian** constructor (real Hamiltonian + real loss),
- a small **noise/covariance** API around the Lindblad rate matrix `Γ`,
- proof-level facts we can already justify (nonnegativity of rates for PSD `Γ`, etc.).

No stochastic calculus is formalized here; those come later at the IR/SDE level.
-/

noncomputable section

namespace HeytingLean
namespace Quantum
namespace TWA

open scoped ComplexConjugate

/-! ## Effective Hamiltonian (scalar, complex-valued) -/

/-- Effective Hamiltonian used as a typed stand-in for later derivations:

`H_eff(s) = H(s) - i · loss(s)`.

Here `H : SpinConfig N → ℝ` and `loss : SpinConfig N → ℝ` are both purely classical functions.
-/
def effectiveHamiltonian {N : ℕ} (H loss : SpinConfig N → ℝ) : SpinConfig N → ℂ :=
  fun s => (H s : ℂ) - Complex.I * (loss s : ℂ)

@[simp] lemma effectiveHamiltonian_apply {N : ℕ} (H loss : SpinConfig N → ℝ) (s : SpinConfig N) :
    effectiveHamiltonian (N := N) H loss s = (H s : ℂ) - Complex.I * (loss s : ℂ) := rfl

@[simp] lemma effectiveHamiltonian_re {N : ℕ} (H loss : SpinConfig N → ℝ) (s : SpinConfig N) :
    (effectiveHamiltonian (N := N) H loss s).re = H s := by
  simp [effectiveHamiltonian]

@[simp] lemma effectiveHamiltonian_im {N : ℕ} (H loss : SpinConfig N → ℝ) (s : SpinConfig N) :
    (effectiveHamiltonian (N := N) H loss s).im = -loss s := by
  simp [effectiveHamiltonian]

@[simp] lemma effectiveHamiltonian_loss_zero {N : ℕ} (H : SpinConfig N → ℝ) :
    effectiveHamiltonian (N := N) H (fun _ => 0) = fun s => (H s : ℂ) := by
  funext s
  simp [effectiveHamiltonian]

@[simp] lemma effectiveHamiltonian_add {N : ℕ}
    (H₁ H₂ loss₁ loss₂ : SpinConfig N → ℝ) :
    effectiveHamiltonian (N := N) (H₁ + H₂) (loss₁ + loss₂)
      = fun s => effectiveHamiltonian (N := N) H₁ loss₁ s + effectiveHamiltonian (N := N) H₂ loss₂ s := by
  funext s
  simp [effectiveHamiltonian, sub_eq_add_neg, mul_add]
  ring

@[simp] lemma effectiveHamiltonian_conj {N : ℕ} (H loss : SpinConfig N → ℝ) (s : SpinConfig N) :
    conj (effectiveHamiltonian (N := N) H loss s)
      = (H s : ℂ) + Complex.I * (loss s : ℂ) := by
  -- `simp` knows `conj I = -I` and `conj (ofReal r) = ofReal r`.
  simp [effectiveHamiltonian, sub_eq_add_neg]

/-! ## Noise / covariance facts from `Γ` -/

namespace LindbladSpec

/-- The Lindblad/TWA covariance matrix (as provided). -/
def covariance (S : LindbladSpec) : Matrix (Fin S.nJumps) (Fin S.nJumps) ℂ := S.Γ

@[simp] lemma covariance_psd (S : LindbladSpec) :
    HeytingLean.Quantum.PosSemidef S.covariance := S.Γ_psd

/-- Real-valued per-jump rate extracted from the diagonal of `Γ`. -/
def rate (S : LindbladSpec) (i : Fin S.nJumps) : ℝ := (S.Γ i i).re

lemma rate_nonneg (S : LindbladSpec) (i : Fin S.nJumps) : 0 ≤ S.rate i := by
  simpa [LindbladSpec.rate] using
    (HeytingLean.Quantum.PosSemidef.diagonal_entry_nonneg (ι := Fin S.nJumps) (A := S.Γ) S.Γ_psd i)

/-- Total real rate (trace of `Γ`, real part). -/
def totalRate (S : LindbladSpec) : ℝ := (Matrix.trace S.Γ).re

lemma totalRate_eq_sum_rate (S : LindbladSpec) :
    S.totalRate = (Finset.univ : Finset (Fin S.nJumps)).sum (fun i => S.rate i) := by
  classical
  simp [LindbladSpec.totalRate, LindbladSpec.rate, Matrix.trace]

lemma totalRate_nonneg (S : LindbladSpec) : 0 ≤ S.totalRate := by
  simpa [LindbladSpec.totalRate] using
    (HeytingLean.Quantum.PosSemidef.trace_real_nonneg (ι := Fin S.nJumps) (A := S.Γ) S.Γ_psd)

end LindbladSpec

end TWA
end Quantum
end HeytingLean
