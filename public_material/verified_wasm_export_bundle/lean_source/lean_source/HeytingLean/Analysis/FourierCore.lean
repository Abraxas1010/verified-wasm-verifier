import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.Complex.Exponential

namespace HeytingLean
namespace Analysis

open Complex

/-!
# Fourier Core (discrete, safe)

Lightweight core pieces for discrete Fourier on `Fin N` with `ℂ`:

- Characters/kernels (`twiddle`)
- Discrete DFT/IDFT over functions `Fin N → ℂ`
- A simple band projector (nucleus) on spectra

This module depends only on basic mathlib components (Complex exp and
big-operators) and avoids heavy measure-theoretic imports. It is
intended to be library-only (no CLI) to keep executables fast.
-/

/-- Discrete Fourier kernel (a.k.a. twiddle factor).
    `N` is the length, `k` is the frequency index, `n` the time index. -/
noncomputable def twiddle (N : ℕ) (k n : Fin N) : ℂ :=
  let t : ℝ := ((k.val : ℝ) * (n.val : ℝ)) / (N : ℝ)
  let twoPi : ℂ := (6.2831853071795864769 : ℝ)
  Complex.exp (-twoPi * Complex.I * (t : ℂ))

/-- Discrete Fourier transform on `Fin N` with complex values. -/
noncomputable def dft {N : ℕ} (x : Fin N → ℂ) : Fin N → ℂ :=
  fun k => (Finset.univ : Finset (Fin N)).sum (fun n => twiddle N k n * x n)

/-- Inverse discrete Fourier transform on `Fin N`. -/
noncomputable def idft {N : ℕ} (X : Fin N → ℂ) : Fin N → ℂ :=
  fun n =>
    let twoPi : ℂ := (6.2831853071795864769 : ℝ)
    (1 / (N : ℂ)) *
      (Finset.univ : Finset (Fin N)).sum (fun k =>
        -- conj(exp(-i θ)) = exp(i θ) since θ is real here.
        Complex.exp (twoPi * Complex.I * (((k.val : ℝ) * (n.val : ℝ) / (N : ℝ)) : ℂ)) * X k)

/-- Simple band projector (nucleus) in the spectral domain: keeps bins
    satisfying `Ω`, zeros the rest. -/
def bandProjector {N : ℕ} (Ω : Fin N → Prop) [DecidablePred Ω]
    (X : Fin N → ℂ) : Fin N → ℂ :=
  fun k => if Ω k then X k else 0

@[simp]
lemma bandProjector_keep {N : ℕ} {Ω : Fin N → Prop} [DecidablePred Ω]
    (X : Fin N → ℂ) {k : Fin N} (hk : Ω k) :
    bandProjector Ω X k = X k := by
  simp [bandProjector, hk]

@[simp]
lemma bandProjector_kill {N : ℕ} {Ω : Fin N → Prop} [DecidablePred Ω]
    (X : Fin N → ℂ) {k : Fin N} (hk : ¬ Ω k) :
    bandProjector Ω X k = 0 := by
  simp [bandProjector, hk]

/-- Idempotence: projecting twice equals projecting once. -/
lemma bandProjector_idem {N : ℕ} (Ω : Fin N → Prop) [DecidablePred Ω]
    (X : Fin N → ℂ) :
    bandProjector Ω (bandProjector Ω X) = bandProjector Ω X := by
  funext k; by_cases hk : Ω k <;> simp [bandProjector, hk]

/- Optional monotonicity lemmas can be added later if needed. -/

end Analysis
end HeytingLean
