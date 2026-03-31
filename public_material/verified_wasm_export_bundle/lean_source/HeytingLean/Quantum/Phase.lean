import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import HeytingLean.Quantum.VacuumOmegaR

/-
# Phase algebra around the minimal form `e^{iθ}`

This module provides a lightweight phase layer that:
- Encodes the minimal oscillatory form `ψ(θ) = exp (i θ)`.
- Connects back to the Ωᴿ vacuum via a simple “phase coherence” view.

It deliberately avoids introducing any physical constants or collapse
assumptions; those live in physics-facing modules.
-/

open scoped Real
open MeasureTheory intervalIntegral

namespace HeytingLean
namespace Quantum
namespace Phase

/-- Minimal phase form `ψ(θ) = e^{iθ}`. -/
noncomputable def minimalPhaseForm (θ : ℝ) : ℂ :=
  Complex.exp (Complex.I * θ)

/-- Expansion of the minimal phase form into real sine and cosine components. -/
lemma minimalPhase_expansion (θ : ℝ) :
    minimalPhaseForm θ = Real.cos θ + Complex.I * Real.sin θ := by
  unfold minimalPhaseForm
  -- `Complex.exp_mul_I` is stated for a real argument, via coercion to ℂ.
  -- We rewrite `Complex.I * θ` as `θ * Complex.I` to match its form.
  simpa [mul_comm, Complex.exp_mul_I, Complex.ofReal_mul, Complex.ofReal_cos,
    Complex.ofReal_sin, mul_comm, mul_left_comm, mul_assoc] using
    (Complex.exp_mul_I (x := (θ : ℝ)))

/-- “Global neutrality” of the minimal phase form:
integral of `e^{iθ}` over a full period vanishes. -/
lemma minimalPhase_globally_neutral :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), minimalPhaseForm θ = 0 := by
  -- First compute the integral over the symmetric interval `[-π, π]`
  have h_symm :
      ∫ θ in (-Real.pi)..Real.pi, minimalPhaseForm θ = 0 := by
    -- Use the standard lemma for `∫ exp (t * I)` over `[-r, r]`.
    have h :=
      (integral_exp_mul_I_eq_sin (r := Real.pi))
    -- Rewrite the integrand and simplify `sin π = 0`.
    -- `integral_exp_mul_I_eq_sin` has type
    --   ∫ t in -π..π, Complex.exp (t * Complex.I) = 2 * Real.sin π
    -- and we rewrite the integrand to `minimalPhaseForm`.
    have h0 : (2 * Real.sin Real.pi : ℂ) = 0 := by
      simp [Real.sin_pi]
    -- The integrand agrees with `minimalPhaseForm` pointwise on ℝ.
    -- We can rewrite using the definition and commutativity of multiplication.
    -- Note that `Complex.exp (t * Complex.I)` and `Complex.exp (Complex.I * t)`
    -- coincide for real `t`.
    -- We let `simp` handle this rewriting.
    simpa [minimalPhaseForm, mul_comm, h0] using h

  -- Relate the `0..2π` integral to the `[-π, π]` one via a shift by `π`.
  have h_shift :
      ∫ θ in (0 : ℝ)..(2 * Real.pi), minimalPhaseForm (θ - Real.pi) =
        ∫ θ in (-Real.pi)..Real.pi, minimalPhaseForm θ := by
    -- Change variables `u = θ - π` using `integral_comp_add_right` with `d = -π`.
    -- This sends `[0, 2π]` to `[-π, π]`.
    simp [sub_eq_add_neg, two_mul]

  -- On the other hand, shifting by `π` multiplies the phase by `-1`.
  have h_shifted_integrand :
      ∀ θ : ℝ, minimalPhaseForm (θ - Real.pi) = -minimalPhaseForm θ := by
    intro θ
    unfold minimalPhaseForm
    -- Use the complex identity `exp (z - π I) = -exp z` with `z = I * θ`.
    simpa [mul_sub, mul_comm, mul_left_comm, mul_assoc] using
      (Complex.exp_sub_pi_mul_I (z := Complex.I * (θ : ℝ)))

  -- Rewrite the shifted integral using the above pointwise identity.
  have h_neg :
      ∫ θ in (0 : ℝ)..(2 * Real.pi), -minimalPhaseForm θ =
        ∫ θ in (-Real.pi)..Real.pi, minimalPhaseForm θ := by
    -- `simp` rewrites `minimalPhaseForm (θ - π)` using `h_shifted_integrand`.
    have := h_shift
    -- Replace the left integrand `minimalPhaseForm (θ - π)` by `-minimalPhaseForm θ`.
    have h_left :
        ∫ θ in (0 : ℝ)..(2 * Real.pi), minimalPhaseForm (θ - Real.pi) =
          ∫ θ in (0 : ℝ)..(2 * Real.pi), -minimalPhaseForm θ := by
      -- `simp` uses `h_shifted_integrand` pointwise.
      have : (fun θ : ℝ => minimalPhaseForm (θ - Real.pi))
          = fun θ : ℝ => -minimalPhaseForm θ := by
        funext θ; exact h_shifted_integrand θ
      simp [this]
    -- Combine the two equalities.
    simpa [h_left] using this

  -- Now the right-hand integral in `h_neg` is zero by `h_symm`.
  have h_neg_zero :
      ∫ θ in (0 : ℝ)..(2 * Real.pi), -minimalPhaseForm θ = 0 := by
    simpa [h_symm] using h_neg

  -- Finally, use linearity of the integral under negation.
  have h_final :
      - ∫ θ in (0 : ℝ)..(2 * Real.pi), minimalPhaseForm θ = 0 := by
    simpa [intervalIntegral.integral_neg] using h_neg_zero

  -- Taking negation of both sides gives the desired result.
  have := congrArg Neg.neg h_final
  simpa using this

/-- Local nontriviality: on the half-open interval `[0, 2π)`, the minimal phase
form is pointwise injective. -/
lemma minimalPhase_locally_nontrivial
    (θ₁ θ₂ : ℝ)
    (h : θ₁ ≠ θ₂)
    (h₁ : θ₁ ∈ Set.Ico 0 (2 * Real.pi))
    (h₂ : θ₂ ∈ Set.Ico 0 (2 * Real.pi)) :
    minimalPhaseForm θ₁ ≠ minimalPhaseForm θ₂ := by
  -- Assume equality and derive a contradiction via injectivity of `circleMap` on `[0, 2π)`.
  intro hEq
  have hθ₁_nonneg : 0 ≤ θ₁ := h₁.1
  have hθ₂_nonneg : 0 ≤ θ₂ := h₂.1
  have hθ₁_lt : θ₁ < 2 * Real.pi := h₁.2
  have hθ₂_lt : θ₂ < 2 * Real.pi := h₂.2

  -- Rewrite in terms of `circleMap 0 1`, which is `exp (θ * I)`.
  have hCircle :
      circleMap (0 : ℂ) (1 : ℝ) θ₁ = circleMap 0 1 θ₂ := by
    simpa [minimalPhaseForm, circleMap_zero, mul_comm] using hEq

  -- Bound the distance between the angles: both lie in `[0, 2π)`, so `|θ₁ - θ₂| < 2π`.
  have hDiff1 : θ₁ - θ₂ < 2 * Real.pi := by
    have hle : θ₁ - θ₂ ≤ θ₁ := sub_le_self _ hθ₂_nonneg
    exact lt_of_le_of_lt hle hθ₁_lt
  have hDiff2 : θ₂ - θ₁ < 2 * Real.pi := by
    have hle : θ₂ - θ₁ ≤ θ₂ := sub_le_self _ hθ₁_nonneg
    exact lt_of_le_of_lt hle hθ₂_lt
  have hDist : |θ₁ - θ₂| < 2 * Real.pi :=
    (abs_sub_lt_iff).2 ⟨hDiff1, hDiff2⟩

  -- Use the standard injectivity result for `circleMap` on intervals of length ≤ `2π`.
  have hAngles :
      θ₁ = θ₂ :=
    eq_of_circleMap_eq (c := (0 : ℂ)) (R := (1 : ℝ))
      (h_R := by norm_num) hDist hCircle

  exact h hAngles

/-- Simple “phase coherence” view: an Ωᴿ point is coherent when it is
    fixed by the reentry nucleus. This is definitionally the same as
    `Reentry.Omega.apply_coe` but given a phase-oriented name. -/
def PhaseCoherent {α : Type u} [LoF.PrimaryAlgebra α]
    (R : LoF.Reentry α) (x : R.Omega) : Prop :=
  R ((x : R.Omega) : α) = (x : α)

/-- The Ωᴿ vacuum fixed point is phase‑coherent in the above sense. -/
lemma vacuum_phase_coherent
    {β : Type u} {α : Type v}
    [Quantum.OML.OrthocomplementedLattice β]
    [Quantum.OML.OrthomodularLattice β]
    [LoF.PrimaryAlgebra α]
    (C : VacuumOmegaRContext β α) :
    PhaseCoherent C.R C.vacuumOmega := by
  unfold PhaseCoherent
  -- This is exactly the fixed‑point property witnessed by `apply_coe`.
  simpa using LoF.Reentry.Omega.apply_coe (R := C.R) (a := C.vacuumOmega)

end Phase
end Quantum
end HeytingLean
