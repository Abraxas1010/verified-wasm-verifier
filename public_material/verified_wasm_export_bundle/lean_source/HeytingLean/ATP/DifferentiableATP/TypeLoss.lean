import HeytingLean.ATP.DifferentiableATP.CoreOps
import HeytingLean.ATP.DifferentiableATP.Util

/-!
# ATP.DifferentiableATP.TypeLoss

PSR-style type loss and multi-objective loss terms for differentiable ATP.
-/

namespace HeytingLean
namespace ATP
namespace DifferentiableATP

open HeytingLean.LoF
open HeytingLean.LoF.Combinators.Differential
open HeytingLean.LoF.Combinators.Differential.Compute

def fsumDiff (a b : FSum) : FSum :=
  Compute.sub a b

/-- Robust squared norm for `FSum`: normalize before dot, then force non-negativity. -/
def fsumNormSq (w : FSum) : Rat :=
  absRat (Compute.l2NormSq (Compute.normalize w))

theorem fsumNormSq_nonneg (w : FSum) : 0 ≤ fsumNormSq w := by
  unfold fsumNormSq
  by_cases h : Compute.l2NormSq (Compute.normalize w) < 0
  ·
    have hneg : 0 ≤ -(Compute.l2NormSq (Compute.normalize w)) := by
      exact neg_nonneg.mpr (le_of_lt h)
    simpa [absRat, h] using hneg
  · have hge : 0 ≤ Compute.l2NormSq (Compute.normalize w) := le_of_not_gt h
    simp [absRat, h, hge]

private theorem absRat_nonneg (r : Rat) : 0 ≤ absRat r := by
  unfold absRat
  by_cases h : r < 0
  ·
    have hneg : 0 ≤ -r := by
      exact neg_nonneg.mpr (le_of_lt h)
    simpa [h] using hneg
  ·
    have hge : 0 ≤ r := le_of_not_gt h
    simp [h, hge]

private def support (w : FSum) : List Comb :=
  (w.map (fun tc => tc.1)).eraseDups

private def mergedSupport (a b : FSum) : List Comb :=
  (support a ++ support b).eraseDups

private def coeffAbs (w : FSum) (c : Comb) : Rat :=
  absRat (Compute.coeff c w)

/-- Pointwise absolute max over merged support. -/
def fsumMaxAbs (a b : FSum) : FSum :=
  (mergedSupport a b).foldl
    (fun acc c =>
      let v := max (coeffAbs a c) (coeffAbs b c)
      addTerm c v acc)
    []

/-- PSR loss: squared distance to the nucleus-fixed subspace. -/
def psrLoss (R : Comb → Comb) (w : FSum) : Rat :=
  let projected := projectToFixedWeights R w
  fsumNormSq (fsumDiff w projected)

theorem psrLoss_nonneg (R : Comb → Comb) (w : FSum) : 0 ≤ psrLoss R w := by
  unfold psrLoss
  exact fsumNormSq_nonneg (fsumDiff w (projectToFixedWeights R w))

/-- Dialectic loss analog: disagreement between synthesis projection and union signal. -/
def dialecticLoss (R : Comb → Comb) (thesis antithesis : FSum) : Rat :=
  let union := fsumMaxAbs thesis antithesis
  let synthesized := projectToFixedWeights R union
  fsumNormSq (fsumDiff synthesized union)

def occamLoss (w : FSum) : Rat :=
  w.foldl (fun acc tc => acc + absRat tc.2) 0

private theorem occamLoss_fold_nonneg (w : FSum) (acc : Rat) (hacc : 0 ≤ acc) :
    0 ≤ w.foldl (fun a tc => a + absRat tc.2) acc := by
  induction w generalizing acc with
  | nil =>
      simpa using hacc
  | cons hd tl ih =>
      have hacc' : 0 ≤ acc + absRat hd.2 := add_nonneg hacc (absRat_nonneg hd.2)
      simpa using ih (acc + absRat hd.2) hacc'

theorem occamLoss_nonneg (w : FSum) : 0 ≤ occamLoss w := by
  unfold occamLoss
  simpa using occamLoss_fold_nonneg w 0 (show (0 : Rat) ≤ 0 by rfl)

/-- PSR-dynamics loss on the predicted-next weights. -/
def psrDynamicsLoss (R : Comb → Comb) (wNext : FSum) : Rat :=
  psrLoss R wNext

theorem psrDynamicsLoss_nonneg (R : Comb → Comb) (wNext : FSum) : 0 ≤ psrDynamicsLoss R wNext := by
  unfold psrDynamicsLoss
  exact psrLoss_nonneg R wNext

structure CurriculumConfig where
  stage1Steps : Nat := 5
  rampSteps : Nat := 10
  deriving Repr

private def natToRat (n : Nat) : Rat :=
  (Int.ofNat n : Rat)

/-- Curriculum ramp: 0 (stage1), then linear 0→1 (ramp), then 1. -/
def curriculumWeight (cfg : CurriculumConfig) (iteration : Nat) : Rat :=
  if iteration < cfg.stage1Steps then
    0
  else if cfg.rampSteps = 0 then
    1
  else if iteration < cfg.stage1Steps + cfg.rampSteps then
    natToRat (iteration - cfg.stage1Steps) / natToRat cfg.rampSteps
  else
    1

structure TypeLossConfig where
  psrWeight : Rat := (1 : Rat) / 10
  dialecticWeight : Rat := (1 : Rat) / 20
  occamWeight : Rat := (1 : Rat) / 100
  psrDynamicsWeight : Rat := (1 : Rat) / 20
  psrEps : Rat := (1 : Rat) / 1000
  curriculum : CurriculumConfig := {}
  deriving Repr

def combinedLossV2
    (cfg : TypeLossConfig)
    (R : Comb → Comb)
    (ioLoss : Rat)
    (w : FSum)
    (wPrev : Option FSum)
    (iteration : Nat) : Rat :=
  let ramp := curriculumWeight cfg.curriculum iteration
  let psr := psrLoss R w
  let dial :=
    match wPrev with
    | some prev => dialecticLoss R prev w
    | none => 0
  let occam := occamLoss w
  let dyn :=
    match wPrev with
    | some _ => psrDynamicsLoss R w
    | none => 0
  ioLoss
    + ramp * cfg.psrWeight * psr
    + ramp * cfg.dialecticWeight * dial
    + ramp * cfg.occamWeight * occam
    + ramp * cfg.psrDynamicsWeight * dyn

/-- Backward-compatible loss combination (no curriculum/Occam/dynamics terms). -/
def combinedLoss
    (cfg : TypeLossConfig)
    (R : Comb → Comb)
    (ioLoss : Rat)
    (w : FSum)
    (wPrev : Option FSum) : Rat :=
  let psr := psrLoss R w
  let dial :=
    match wPrev with
    | some prev => dialecticLoss R prev w
    | none => 0
  ioLoss + cfg.psrWeight * psr + cfg.dialecticWeight * dial

end DifferentiableATP
end ATP
end HeytingLean
