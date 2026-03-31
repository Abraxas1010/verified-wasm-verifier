import Mathlib.Data.Real.Basic
import Mathlib.Tactic

import HeytingLean.Bridge.Sharma.AetherGovernor

/-
# AETHER Governor Convergence Scaffolding

This module currently contains two distinct formal tracks:

1. `candidateRho` / `targetRhoRegime`: a static validator-side proxy that
   depends only on parameters.
2. `contractionRho`: the exact one-step no-clamp contraction factor in the
   special regime where the governor starts "from rest" (`s.ePrev = 0`).

Important limitations:

- The exact contraction/descent theorems below are single-step results. They
  all require `s.ePrev = 0`, and `govStep` writes the current error into
  `ePrev`, so this hypothesis is not preserved automatically across iterations.
- The generic geometric lemma is intentionally separate scaffolding. It is not
  yet instantiated to the full PD governor.
- No theorem in this module proves that the static proxy `candidateRho`
  upper-bounds the exact state-dependent `contractionRho`.
-/

namespace HeytingLean.Bridge.Sharma.AetherGovernorConvergence

open HeytingLean.Bridge.Sharma.AetherGovernor

/-- Conservative static validator proxy used by the CLI. -/
def candidateRho (p : GovParams) : Real :=
  1 - p.alpha

/-- A simple operating regime for the current validator surface. -/
def validatorRegime (p : GovParams) (dt : Real) : Prop :=
  1 ≤ dt ∧ p.alpha + p.beta / dt < 1

noncomputable instance instDecidableValidatorRegime (p : GovParams) (dt : Real) :
    Decidable (validatorRegime p dt) := by
  unfold validatorRegime
  infer_instance

/-- Boolean validator surface mirroring `validatorRegime`. -/
noncomputable def validateParams (p : GovParams) (dt : Real) : Bool :=
  decide (validatorRegime p dt)

/--
Exact one-step contraction factor in the no-clamp, from-rest regime.

This factor is only used in the single-step analysis below. It is not currently
proved to control later PD steps once `govStep` has updated `ePrev`.
-/
noncomputable def contractionRho (p : GovParams) (s : GovState) (delta dt : Real) : Real :=
  let γ := p.alpha + p.beta / dt
  let e := govError p s delta
  (s.eps - γ * p.target) / (s.eps + γ * e)

/--
Target-ρ parameter regime for the static validator proxy.

This controls `candidateRho` only. It does not assert that the exact
state-dependent `contractionRho` is bounded by the same `rho`.
-/
def targetRhoRegime (p : GovParams) (dt rho : Real) : Prop :=
  validatorRegime p dt ∧ 0 < rho ∧ rho < 1 ∧ 1 - rho ≤ p.alpha

noncomputable instance instDecidableTargetRhoRegime (p : GovParams) (dt rho : Real) :
    Decidable (targetRhoRegime p dt rho) := by
  unfold targetRhoRegime
  infer_instance

/-- Boolean validator for the target-ρ regime. -/
noncomputable def validateTargetRho (p : GovParams) (dt rho : Real) : Bool :=
  decide (targetRhoRegime p dt rho)

theorem validateParams_eq_true_iff (p : GovParams) (dt : Real) :
    validateParams p dt = true ↔ validatorRegime p dt := by
  unfold validateParams
  exact decide_eq_true_iff

theorem validateTargetRho_eq_true_iff (p : GovParams) (dt rho : Real) :
    validateTargetRho p dt rho = true ↔ targetRhoRegime p dt rho := by
  unfold validateTargetRho
  exact decide_eq_true_iff

theorem candidateRho_lt_one (p : GovParams) : candidateRho p < 1 := by
  unfold candidateRho
  linarith [p.hAlpha]

theorem candidateRho_pos_of_gain_margin
    (p : GovParams) (dt : Real) (hdt : 0 < dt)
    (hGain : p.alpha + p.beta / dt < 1) :
    0 < candidateRho p := by
  have hAlphaLt : p.alpha < 1 := gain_margin_implies_alpha_lt_one p dt hdt hGain
  unfold candidateRho
  linarith

theorem candidateRho_mem_Ioo_of_validatorRegime
    (p : GovParams) (dt : Real)
    (hRegime : validatorRegime p dt) :
    0 < candidateRho p ∧ candidateRho p < 1 := by
  rcases hRegime with ⟨hDt, hGain⟩
  constructor
  · exact candidateRho_pos_of_gain_margin p dt (by linarith) hGain
  · exact candidateRho_lt_one p

theorem validatorRegime_gain_margin_refined
    (p : GovParams) (dt : Real)
    (hRegime : validatorRegime p dt) :
    0 < dt ∧ p.alpha < 1 := by
  rcases hRegime with ⟨hDt, hGain⟩
  constructor
  · linarith
  · exact gain_margin_implies_alpha_lt_one p dt (by linarith) hGain

theorem gamma_pos (p : GovParams) (dt : Real) (hdt : 0 < dt) :
    0 < p.alpha + p.beta / dt := by
  have hBetaTerm : 0 ≤ p.beta / dt := by
    exact div_nonneg p.hBeta (le_of_lt hdt)
  linarith [p.hAlpha, hBetaTerm]

/--
After one concrete step, the derivative-memory field stores the current error.

This is the reason the `hPrev : s.ePrev = 0` hypotheses below describe a
single-step "from rest" regime rather than an automatically iterable one.
-/
theorem govStep_sets_ePrev_to_error (p : GovParams) (s : GovState) (delta dt : Real) :
    (govStep p s delta dt).ePrev = govError p s delta := by
  unfold govStep govError
  simp

theorem contractionRho_den_eq_num_add_term
    (p : GovParams) (s : GovState) (delta dt : Real)
    (hEpsPos : 0 < s.eps) :
    s.eps + (p.alpha + p.beta / dt) * govError p s delta =
      (s.eps - (p.alpha + p.beta / dt) * p.target) +
        (p.alpha + p.beta / dt) * delta / s.eps := by
  unfold govError
  field_simp [hEpsPos.ne']
  ring

theorem contractionRho_nonneg
    (p : GovParams) (s : GovState) (delta dt : Real)
    (hdt : 0 < dt) (hDelta : 0 < delta)
    (hEpsPos : 0 < s.eps)
    (hGammaTargetLeEps : (p.alpha + p.beta / dt) * p.target ≤ s.eps) :
    0 ≤ contractionRho p s delta dt := by
  let γ : Real := p.alpha + p.beta / dt
  let num : Real := s.eps - γ * p.target
  let den : Real := s.eps + γ * govError p s delta
  have hγ_pos : 0 < γ := by
    simpa [γ] using gamma_pos p dt hdt
  have hNumNonneg : 0 ≤ num := by
    exact sub_nonneg.mpr hGammaTargetLeEps
  have hDenEq :
      den = num + γ * delta / s.eps := by
    dsimp [den, num, γ]
    simpa [govError] using contractionRho_den_eq_num_add_term p s delta dt hEpsPos
  have hTermPos : 0 < γ * delta / s.eps := by
    exact div_pos (mul_pos hγ_pos hDelta) hEpsPos
  have hDenPos : 0 < den := by
    rw [hDenEq]
    linarith
  unfold contractionRho
  exact div_nonneg hNumNonneg (le_of_lt hDenPos)

theorem contractionRho_lt_one
    (p : GovParams) (s : GovState) (delta dt : Real)
    (hdt : 0 < dt) (hDelta : 0 < delta)
    (hEpsPos : 0 < s.eps)
    (hGammaTargetLeEps : (p.alpha + p.beta / dt) * p.target ≤ s.eps) :
    contractionRho p s delta dt < 1 := by
  let γ : Real := p.alpha + p.beta / dt
  let num : Real := s.eps - γ * p.target
  let den : Real := s.eps + γ * govError p s delta
  have hγ_pos : 0 < γ := by
    simpa [γ] using gamma_pos p dt hdt
  have hDenEq :
      den = num + γ * delta / s.eps := by
    dsimp [den, num, γ]
    simpa [govError] using contractionRho_den_eq_num_add_term p s delta dt hEpsPos
  have hTermPos : 0 < γ * delta / s.eps := by
    exact div_pos (mul_pos hγ_pos hDelta) hEpsPos
  have hDenPos : 0 < den := by
    rw [hDenEq]
    have hNumNonneg : 0 ≤ num := by
      exact sub_nonneg.mpr hGammaTargetLeEps
    linarith
  have hNumLtDen : num < den := by
    rw [hDenEq]
    linarith
  unfold contractionRho
  exact (div_lt_one hDenPos).2 hNumLtDen

theorem govError_eq_contractionRho_mul_error
    (p : GovParams) (s : GovState)
    (delta : Real) (dt : Real)
    (hEpsPos : 0 < s.eps)
    (hNoClampLo : p.epsMin ≤ s.eps + govAdjustment p s delta dt)
    (hNoClampHi : s.eps + govAdjustment p s delta dt ≤ p.epsMax)
    (hPrev : s.ePrev = 0)
    (hDenom : s.eps + (p.alpha + p.beta / dt) * govError p s delta ≠ 0) :
    govError p (govStep p s delta dt) delta =
      contractionRho p s delta dt * govError p s delta := by
  let γ : Real := p.alpha + p.beta / dt
  let e : Real := govError p s delta
  have hAdj : govAdjustment p s delta dt = γ * e := by
    simpa [γ, e] using
      govAdjustment_eq_gamma_mul_error_of_prev_zero
        (p := p) (s := s) (delta := delta) (dt := dt) hPrev
  rw [govError_step_eq_noclamp (p := p) (s := s) (delta := delta) (dt := dt) hNoClampLo hNoClampHi]
  rw [hAdj]
  have hId := error_ratio_identity s.eps delta p.target γ hEpsPos (by
    simpa [γ, e, govError] using hDenom)
  simpa [contractionRho, γ, e, govError, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]
    using hId

theorem abs_govError_eq_contractionRho_mul_abs
    (p : GovParams) (s : GovState)
    (delta : Real) (dt : Real) (hdt : 0 < dt) (hDelta : 0 < delta)
    (hEpsPos : 0 < s.eps)
    (hNoClampLo : p.epsMin ≤ s.eps + govAdjustment p s delta dt)
    (hNoClampHi : s.eps + govAdjustment p s delta dt ≤ p.epsMax)
    (hPrev : s.ePrev = 0)
    (hGammaTargetLeEps : (p.alpha + p.beta / dt) * p.target ≤ s.eps) :
    |govError p (govStep p s delta dt) delta| =
      contractionRho p s delta dt * |govError p s delta| := by
  have hDenNonzero :
      s.eps + (p.alpha + p.beta / dt) * govError p s delta ≠ 0 := by
    let γ : Real := p.alpha + p.beta / dt
    let num : Real := s.eps - γ * p.target
    let den : Real := s.eps + γ * govError p s delta
    have hγ_pos : 0 < γ := by
      simpa [γ] using gamma_pos p dt hdt
    have hDenEq :
        den = num + γ * delta / s.eps := by
      dsimp [den, num, γ]
      simpa [govError] using contractionRho_den_eq_num_add_term p s delta dt hEpsPos
    have hTermPos : 0 < γ * delta / s.eps := by
      exact div_pos (mul_pos hγ_pos hDelta) hEpsPos
    have hNumNonneg : 0 ≤ num := by
      exact sub_nonneg.mpr hGammaTargetLeEps
    have hDenPos : 0 < den := by
      rw [hDenEq]
      linarith
    exact by
      simpa [den, γ] using ne_of_gt hDenPos
  have hEq := govError_eq_contractionRho_mul_error
    p s delta dt hEpsPos hNoClampLo hNoClampHi hPrev hDenNonzero
  have hRhoNonneg := contractionRho_nonneg p s delta dt hdt hDelta hEpsPos hGammaTargetLeEps
  rw [hEq, abs_mul, abs_of_nonneg hRhoNonneg]

theorem lyapunov_eq_contractionRho_sq_mul
    (p : GovParams) (s : GovState)
    (delta : Real) (dt : Real) (hdt : 0 < dt) (hDelta : 0 < delta)
    (hEpsPos : 0 < s.eps)
    (hNoClampLo : p.epsMin ≤ s.eps + govAdjustment p s delta dt)
    (hNoClampHi : s.eps + govAdjustment p s delta dt ≤ p.epsMax)
    (hPrev : s.ePrev = 0)
    (hGammaTargetLeEps : (p.alpha + p.beta / dt) * p.target ≤ s.eps) :
    lyapunov (govError p (govStep p s delta dt) delta) =
      (contractionRho p s delta dt) ^ 2 * lyapunov (govError p s delta) := by
  have hDenNonzero :
      s.eps + (p.alpha + p.beta / dt) * govError p s delta ≠ 0 := by
    let γ : Real := p.alpha + p.beta / dt
    let num : Real := s.eps - γ * p.target
    let den : Real := s.eps + γ * govError p s delta
    have hγ_pos : 0 < γ := by
      simpa [γ] using gamma_pos p dt hdt
    have hDenEq :
        den = num + γ * delta / s.eps := by
      dsimp [den, num, γ]
      simpa [govError] using contractionRho_den_eq_num_add_term p s delta dt hEpsPos
    have hTermPos : 0 < γ * delta / s.eps := by
      exact div_pos (mul_pos hγ_pos hDelta) hEpsPos
    have hNumNonneg : 0 ≤ num := by
      exact sub_nonneg.mpr hGammaTargetLeEps
    have hDenPos : 0 < den := by
      rw [hDenEq]
      linarith
    exact by
      simpa [den, γ] using ne_of_gt hDenPos
  have hEq := govError_eq_contractionRho_mul_error
    p s delta dt hEpsPos hNoClampLo hNoClampHi hPrev hDenNonzero
  unfold lyapunov
  rw [hEq]
  ring

theorem lyapunov_strict_descent
    (p : GovParams) (s : GovState)
    (delta : Real) (dt : Real) (hdt : 0 < dt) (hDelta : 0 < delta)
    (hEpsPos : 0 < s.eps)
    (hNoClampLo : p.epsMin ≤ s.eps + govAdjustment p s delta dt)
    (hNoClampHi : s.eps + govAdjustment p s delta dt ≤ p.epsMax)
    (hPrev : s.ePrev = 0)
    (hGammaTargetLeEps : (p.alpha + p.beta / dt) * p.target ≤ s.eps)
    (hErrNe : govError p s delta ≠ 0) :
    lyapunov (govError p (govStep p s delta dt) delta) <
      lyapunov (govError p s delta) := by
  let ρ := contractionRho p s delta dt
  have hRhoNonneg : 0 ≤ ρ := by
    exact contractionRho_nonneg p s delta dt hdt hDelta hEpsPos hGammaTargetLeEps
  have hRhoLtOne : ρ < 1 := by
    exact contractionRho_lt_one p s delta dt hdt hDelta hEpsPos hGammaTargetLeEps
  have hLyapEq :
      lyapunov (govError p (govStep p s delta dt) delta) =
        ρ ^ 2 * lyapunov (govError p s delta) := by
    simpa [ρ] using
      lyapunov_eq_contractionRho_sq_mul
        p s delta dt hdt hDelta hEpsPos hNoClampLo hNoClampHi hPrev hGammaTargetLeEps
  have hLyapPos : 0 < lyapunov (govError p s delta) := by
    unfold lyapunov
    have hSqPos : 0 < (govError p s delta) ^ 2 := by
      exact sq_pos_of_ne_zero hErrNe
    nlinarith
  have hRhoSqLtOne : ρ ^ 2 < 1 := by
    nlinarith
  calc
    lyapunov (govError p (govStep p s delta dt) delta)
        = ρ ^ 2 * lyapunov (govError p s delta) := hLyapEq
    _ < 1 * lyapunov (govError p s delta) := by
        exact mul_lt_mul_of_pos_right hRhoSqLtOne hLyapPos
    _ = lyapunov (govError p s delta) := by ring

/--
Generic geometric-convergence scaffolding.

This lemma is intentionally independent of the governor. The current module does
not yet provide a theorem instantiating `hStep` for the full PD dynamics after
the first step, because the exact factorization results require `s.ePrev = 0`.
-/
theorem geometric_convergence_of_stepwise_contraction
    {rho : Real} (hRhoNonneg : 0 ≤ rho)
    (errors : Nat → Real)
    (hStep : ∀ k : Nat, |errors (k + 1)| ≤ rho * |errors k|) :
    ∀ n : Nat, |errors n| ≤ rho ^ n * |errors 0| := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        |errors (n + 1)| ≤ rho * |errors n| := hStep n
        _ ≤ rho * (rho ^ n * |errors 0|) := by
          exact mul_le_mul_of_nonneg_left ih hRhoNonneg
        _ = rho ^ (n + 1) * |errors 0| := by
          rw [pow_succ]
          ring

theorem candidateRho_le_of_targetRhoRegime
    (p : GovParams) (dt rho : Real)
    (hTarget : targetRhoRegime p dt rho) :
    candidateRho p ≤ rho := by
  rcases hTarget with ⟨_hRegime, _hRhoPos, _hRhoLt, hAlphaLower⟩
  unfold candidateRho
  linarith

theorem candidateRho_mem_Ioc_of_targetRhoRegime
    (p : GovParams) (dt rho : Real)
    (hTarget : targetRhoRegime p dt rho) :
    0 < candidateRho p ∧ candidateRho p ≤ rho := by
  rcases hTarget with ⟨hRegime, hRhoPos, hRhoLt, hAlphaLower⟩
  constructor
  · exact (candidateRho_mem_Ioo_of_validatorRegime p dt hRegime).1
  · exact candidateRho_le_of_targetRhoRegime p dt rho
      ⟨hRegime, hRhoPos, hRhoLt, hAlphaLower⟩

theorem validateTargetRho_sound
    (p : GovParams) (dt rho : Real)
    (hValid : validateTargetRho p dt rho = true) :
    0 < candidateRho p ∧ candidateRho p ≤ rho := by
  exact candidateRho_mem_Ioc_of_targetRhoRegime p dt rho
    ((validateTargetRho_eq_true_iff p dt rho).1 hValid)

/-! ## Counterexamples closing over-broad governor claims -/

noncomputable def candidateBridgeWitnessParams : GovParams where
  alpha := (1 : Real) / 10
  beta := (1 : Real) / 10
  epsMin := (1 : Real) / 1000
  epsMax := 1000
  target := 1
  hAlpha := by norm_num
  hBeta := by norm_num
  hEps := by norm_num
  hEpsMinPos := by norm_num

noncomputable def candidateBridgeWitnessState : GovState where
  eps := 100
  ePrev := 0

/--
The global inequality `contractionRho ≤ candidateRho` is false without extra
state constraints. This concrete witness lives inside `validatorRegime`.
-/
theorem candidateRho_lt_contractionRho_counterexample :
    candidateRho candidateBridgeWitnessParams <
      contractionRho candidateBridgeWitnessParams candidateBridgeWitnessState 100 1 := by
  norm_num [candidateRho, contractionRho, govError, candidateBridgeWitnessParams,
    candidateBridgeWitnessState]

theorem validatorRegime_candidateBridgeWitness :
    validatorRegime candidateBridgeWitnessParams 1 := by
  constructor
  · norm_num
  · norm_num [candidateBridgeWitnessParams]

noncomputable def pdCounterexampleParams : GovParams where
  alpha := (1 : Real) / 100
  beta := (1 : Real) / 100
  epsMin := (1 : Real) / 1000
  epsMax := 1000
  target := (1 : Real) / 2
  hAlpha := by norm_num
  hBeta := by norm_num
  hEps := by norm_num
  hEpsMinPos := by norm_num

noncomputable def pdCounterexampleState0 : GovState where
  eps := (1 : Real) / 2
  ePrev := 0

noncomputable def pdCounterexampleState1 : GovState :=
  govStep pdCounterexampleParams pdCounterexampleState0 20 1

noncomputable def pdCounterexampleState2 : GovState :=
  govStep pdCounterexampleParams pdCounterexampleState1 20 1

theorem validatorRegime_pdCounterexample :
    validatorRegime pdCounterexampleParams 1 := by
  constructor
  · norm_num
  · norm_num [pdCounterexampleParams]

/--
Even under `validatorRegime`, the full PD dynamics need not have monotone
Lyapunov descent across successive steps. So the current single-step theorem
cannot be upgraded to a global PD result without stronger hypotheses.
-/
theorem lyapunov_rises_on_second_pd_step_counterexample :
    lyapunov (govError pdCounterexampleParams pdCounterexampleState2 20) >
      lyapunov (govError pdCounterexampleParams pdCounterexampleState1 20) := by
  norm_num [pdCounterexampleState2, pdCounterexampleState1, pdCounterexampleState0,
    pdCounterexampleParams, govStep, govAdjustment, govError, lyapunov, clamp]

end HeytingLean.Bridge.Sharma.AetherGovernorConvergence
