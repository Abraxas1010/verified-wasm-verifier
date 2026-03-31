import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# AETHER Geometric Governor: Lyapunov Stability

Discrete-time PD-style governor scaffolding with a Lyapunov descent lemma.
-/

namespace HeytingLean.Bridge.Sharma.AetherGovernor

/-- Clamp a value to `[lo, hi]`. -/
def clamp (x lo hi : Real) : Real :=
  max lo (min x hi)

theorem clamp_le_hi (x lo hi : Real) (h : lo ≤ hi) : clamp x lo hi ≤ hi := by
  unfold clamp
  exact max_le h (min_le_right _ _)

theorem lo_le_clamp (x lo hi : Real) (_h : lo ≤ hi) : lo ≤ clamp x lo hi := by
  unfold clamp
  exact le_max_left _ _

/-- Governor parameters. -/
structure GovParams where
  alpha : Real
  beta : Real
  epsMin : Real
  epsMax : Real
  target : Real
  hAlpha : 0 < alpha
  hBeta : 0 ≤ beta
  hEps : epsMin < epsMax
  hEpsMinPos : 0 < epsMin

/-- Governor state. -/
structure GovState where
  eps : Real
  ePrev : Real

/-- The additive update term used by the governor before clamping. -/
noncomputable def govAdjustment (p : GovParams) (s : GovState) (delta : Real) (dt : Real) : Real :=
  let e := delta / s.eps - p.target
  let dError := (e - s.ePrev) / dt
  p.alpha * e + p.beta * dError

/-- One discrete PD step with clamped threshold. -/
noncomputable def govStep (p : GovParams) (s : GovState) (delta : Real) (dt : Real) : GovState :=
  let e := delta / s.eps - p.target
  let adjustment := govAdjustment p s delta dt
  let eps' := clamp (s.eps + adjustment) p.epsMin p.epsMax
  { eps := eps', ePrev := e }

/-- Error for current state and observed interval `delta`. -/
noncomputable def govError (p : GovParams) (s : GovState) (delta : Real) : Real :=
  delta / s.eps - p.target

/-- Lyapunov candidate. -/
noncomputable def lyapunov (e : Real) : Real :=
  e ^ 2 / 2

theorem lyapunov_nonneg (e : Real) : 0 ≤ lyapunov e := by
  unfold lyapunov
  exact div_nonneg (sq_nonneg e) (by norm_num)

theorem lyapunov_eq_zero_iff (e : Real) : lyapunov e = 0 ↔ e = 0 := by
  unfold lyapunov
  constructor
  · intro h
    have hsq : e ^ 2 = 0 := by linarith
    exact pow_eq_zero hsq
  · intro he
    simp [he]

theorem gain_margin_implies_alpha_lt_one
    (p : GovParams) (dt : Real) (hdt : 0 < dt)
    (hGain : p.alpha + p.beta / dt < 1) :
    p.alpha < 1 := by
  have hBetaTerm : 0 ≤ p.beta / dt := by
    exact div_nonneg p.hBeta (le_of_lt hdt)
  linarith

/-- Combined gain stability condition for the corrected-sign governor. -/
def gainStable (p : GovParams) (delta : Real) (dt : Real) : Prop :=
  let gamma := p.alpha + p.beta / dt
  gamma * p.target ^ 2 / delta < 2

/-- If clamp is inactive, the next epsilon equals the unclamped update. -/
theorem govStep_eps_eq_noclamp (p : GovParams) (s : GovState)
    (delta : Real) (dt : Real)
    (hNoClampLo : p.epsMin ≤ s.eps + govAdjustment p s delta dt)
    (hNoClampHi : s.eps + govAdjustment p s delta dt ≤ p.epsMax) :
    (govStep p s delta dt).eps = s.eps + govAdjustment p s delta dt := by
  unfold govStep clamp
  simp [min_eq_left hNoClampHi, max_eq_right hNoClampLo]

/--
Exact next-error expression when the clamp is inactive.
-/
theorem govError_step_eq_noclamp (p : GovParams) (s : GovState)
    (delta : Real) (dt : Real)
    (hNoClampLo : p.epsMin ≤ s.eps + govAdjustment p s delta dt)
    (hNoClampHi : s.eps + govAdjustment p s delta dt ≤ p.epsMax) :
    govError p (govStep p s delta dt) delta =
      delta / (s.eps + govAdjustment p s delta dt) - p.target := by
  unfold govError
  rw [govStep_eps_eq_noclamp (p := p) (s := s) (delta := delta) (dt := dt) hNoClampLo hNoClampHi]

/-- With zero previous error memory, the PD update is `gamma * e`. -/
theorem govAdjustment_eq_gamma_mul_error_of_prev_zero
    (p : GovParams) (s : GovState) (delta : Real) (dt : Real)
    (hPrev : s.ePrev = 0) :
    govAdjustment p s delta dt =
      (p.alpha + p.beta / dt) * govError p s delta := by
  unfold govAdjustment govError
  simp [hPrev]
  ring

/--
Algebraic factorization of one no-clamp update step for corrected-sign error.
-/
theorem error_ratio_identity (eps delta target gamma : Real)
    (hEps : 0 < eps)
    (hDenom : eps + gamma * (delta / eps - target) ≠ 0) :
    delta / (eps + gamma * (delta / eps - target)) - target =
      (delta / eps - target) * (eps - gamma * target) /
        (eps + gamma * (delta / eps - target)) := by
  set k : Real := eps + gamma * (delta / eps - target)
  have hk : k ≠ 0 := by simpa [k] using hDenom
  calc
    delta / k - target = (delta - target * k) / k := by
      field_simp [hk]
    _ = ((delta / eps - target) * (eps - gamma * target)) / k := by
      congr 1
      field_simp [hEps.ne']
      simp [k]
      field_simp [hEps.ne']
      ring
    _ = (delta / eps - target) * (eps - gamma * target) /
          (eps + gamma * (delta / eps - target)) := by
      simp [k]

/--
Contraction in the explicitly no-clamp regime.

This is the honest Path-B closure: the nonlinear PD contraction obligation is
stated directly on the concrete no-clamp update formula.
-/
theorem govError_contraction_noclamp (p : GovParams) (s : GovState)
    (delta : Real) (dt : Real) (hdt : 0 < dt) (hDelta : 0 < delta)
    (hEpsPos : 0 < s.eps)
    (hNoClampLo : p.epsMin ≤ s.eps + govAdjustment p s delta dt)
    (hNoClampHi : s.eps + govAdjustment p s delta dt ≤ p.epsMax)
    (hPrev : s.ePrev = 0)
    (hGammaTargetLeEps : (p.alpha + p.beta / dt) * p.target ≤ s.eps) :
    |govError p (govStep p s delta dt) delta| ≤
      |govError p s delta| := by
  let γ : Real := p.alpha + p.beta / dt
  let e : Real := govError p s delta
  let num : Real := s.eps - γ * p.target
  let den : Real := s.eps + γ * e
  have hγ_pos : 0 < γ := by
    dsimp [γ]
    have hBetaTerm : 0 ≤ p.beta / dt := div_nonneg p.hBeta (le_of_lt hdt)
    linarith [p.hAlpha, hBetaTerm]
  have hNumNonneg : 0 ≤ num := by
    dsimp [num, γ]
    exact sub_nonneg.mpr hGammaTargetLeEps
  have hDenEq : den = num + γ * delta / s.eps := by
    dsimp [den, num, γ, e]
    unfold govError
    field_simp [hEpsPos.ne']
    ring
  have hTermPos : 0 < γ * delta / s.eps := by
    exact div_pos (mul_pos hγ_pos hDelta) hEpsPos
  have hDenPos : 0 < den := by
    rw [hDenEq]
    linarith
  have hNumLeDen : num ≤ den := by
    rw [hDenEq]
    nlinarith [hTermPos]
  have hRatioLeOne : num / den ≤ 1 := by
    exact (div_le_one hDenPos).2 hNumLeDen
  have hStepErr :
      govError p (govStep p s delta dt) delta = e * num / den := by
    have hAdj : govAdjustment p s delta dt = γ * e := by
      simpa [γ, e] using
        govAdjustment_eq_gamma_mul_error_of_prev_zero (p := p) (s := s)
          (delta := delta) (dt := dt) hPrev
    rw [govError_step_eq_noclamp (p := p) (s := s) (delta := delta) (dt := dt) hNoClampLo hNoClampHi]
    rw [hAdj]
    have hId := error_ratio_identity s.eps delta p.target γ hEpsPos (ne_of_gt hDenPos)
    simpa [γ, e, num, den, govError] using hId
  have hNumAbs : |num| = num := abs_of_nonneg hNumNonneg
  have hDenAbs : |den| = den := abs_of_pos hDenPos
  calc
    |govError p (govStep p s delta dt) delta|
        = |e * num / den| := by simp [hStepErr]
    _ = |e| * (num / den) := by
        rw [abs_div, abs_mul, hNumAbs, hDenAbs]
        ring
    _ ≤ |e| * 1 := by
        exact mul_le_mul_of_nonneg_left hRatioLeOne (abs_nonneg e)
    _ = |govError p s delta| := by simp [e]

/--
Lyapunov descent from an explicit one-step contraction inequality.
-/
theorem lyapunov_descent_of_contraction (p : GovParams) (s : GovState)
    (delta : Real) (dt : Real) (_hdt : 0 < dt) (_hDelta : 0 < delta)
    (_hEpsLo : p.epsMin ≤ s.eps) (_hEpsHi : s.eps ≤ p.epsMax)
    (hContract :
      |govError p (govStep p s delta dt) delta| ≤
        |govError p s delta|) :
    lyapunov (govError p (govStep p s delta dt) delta) ≤
      lyapunov (govError p s delta) := by
  have hSqAbs :
      |govError p (govStep p s delta dt) delta| ^ 2 ≤
        |govError p s delta| ^ 2 := by
    simpa [pow_two] using
      (mul_self_le_mul_self (abs_nonneg (govError p (govStep p s delta dt) delta)) hContract)
  have hSq :
      (govError p (govStep p s delta dt) delta) ^ 2 ≤
        (govError p s delta) ^ 2 := by
    simpa [sq_abs] using hSqAbs
  unfold lyapunov
  nlinarith [hSq]

/--
Main Phase-2 descent theorem in the no-clamp operating regime.

This theorem no longer assumes a standalone `hContract` on `govError`; instead
it derives that inequality from `govStep` via `govError_contraction_noclamp`.
-/
theorem lyapunov_descent (p : GovParams) (s : GovState)
    (delta : Real) (dt : Real) (hdt : 0 < dt) (hDelta : 0 < delta)
    (hEpsPos : 0 < s.eps)
    (hEpsLo : p.epsMin ≤ s.eps) (hEpsHi : s.eps ≤ p.epsMax)
    (hNoClampLo : p.epsMin ≤ s.eps + govAdjustment p s delta dt)
    (hNoClampHi : s.eps + govAdjustment p s delta dt ≤ p.epsMax)
    (hPrev : s.ePrev = 0)
    (hGammaTargetLeEps : (p.alpha + p.beta / dt) * p.target ≤ s.eps) :
    lyapunov (govError p (govStep p s delta dt) delta) ≤
      lyapunov (govError p s delta) := by
  apply lyapunov_descent_of_contraction p s delta dt hdt hDelta hEpsLo hEpsHi
  exact govError_contraction_noclamp p s delta dt hdt hDelta hEpsPos
    hNoClampLo hNoClampHi hPrev hGammaTargetLeEps

/--
Contraction holds at equilibrium (`govError = 0`, `ePrev = 0`) in the no-clamp regime.
-/
theorem govError_contraction_equilibrium (p : GovParams) (s : GovState)
    (delta : Real) (dt : Real) (_hdt : 0 < dt) (_hDelta : 0 < delta)
    (hNoClampLo : p.epsMin ≤ s.eps + govAdjustment p s delta dt)
    (hNoClampHi : s.eps + govAdjustment p s delta dt ≤ p.epsMax)
    (hErr : govError p s delta = 0) (hPrev : s.ePrev = 0) :
    |govError p (govStep p s delta dt) delta| ≤
      |govError p s delta| := by
  have he : delta / s.eps - p.target = 0 := by
    simpa [govError] using hErr
  have hadj : govAdjustment p s delta dt = 0 := by
    unfold govAdjustment
    simp [he, hPrev]
  have hstep : (govStep p s delta dt).eps = s.eps := by
    rw [govStep_eps_eq_noclamp (p := p) (s := s) (delta := delta) (dt := dt) hNoClampLo hNoClampHi]
    simp [hadj]
  have hnextErr : govError p (govStep p s delta dt) delta = 0 := by
    unfold govError
    rw [hstep]
    simp [he]
  simp [hnextErr, hErr]

/-- The clamped update always remains in parameter bounds. -/
theorem epsilon_bounded (p : GovParams) (s : GovState) (delta dt : Real)
    (_hdt : 0 < dt) :
    let s' := govStep p s delta dt
    p.epsMin ≤ s'.eps ∧ s'.eps ≤ p.epsMax := by
  intro s'
  subst s'
  unfold govStep
  constructor
  · exact lo_le_clamp _ _ _ (le_of_lt p.hEps)
  · exact clamp_le_hi _ _ _ (le_of_lt p.hEps)

/-- The naive gain margin fails for Teerth's default `dt = 0.001`. -/
theorem hft_gain_margin :
    (0.01 : Real) + 0.05 / 0.001 < 1 → False := by
  norm_num

/-- Refined gain margin with a lower bound on `dt`. -/
theorem hft_gain_margin_refined (dt : Real) (hdt : 1 ≤ dt) :
    (0.01 : Real) + 0.05 / dt < 1 := by
  have hdtPos : 0 < dt := lt_of_lt_of_le (by norm_num : (0 : Real) < 1) hdt
  have hInv : (1 : Real) / dt ≤ 1 := by
    exact (div_le_one hdtPos).2 hdt
  have hDiv : (0.05 : Real) / dt ≤ 0.05 := by
    calc
      (0.05 : Real) / dt = 0.05 * ((1 : Real) / dt) := by ring
      _ ≤ 0.05 * 1 := by nlinarith [hInv]
      _ = 0.05 := by ring
  nlinarith [hDiv]

end HeytingLean.Bridge.Sharma.AetherGovernor
