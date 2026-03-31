import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import HeytingLean.PathIntegral.ProofPath
import HeytingLean.ATP.LensTransport.FaithfulTransportGraph

/-!
# PathIntegral.Action

Action function on proof paths.
-/

namespace HeytingLean
namespace PathIntegral

open HeytingLean.Embeddings
open HeytingLean.ATP
open HeytingLean.ATP.LensTransport
open HeytingLean.ATP.DifferentiableATP
open HeytingLean.LoF
open HeytingLean.LoF.Combinators.Differential.Compute

def ratToFloat (q : Rat) : Float :=
  Float.ofInt q.num / Float.ofNat q.den

/-- Probe matching the measure-layer basis witness, kept local to avoid
introducing a circular `Action ← Measure ← Action` import. Keep the shape in
lockstep with `Measure.measureTransportProbe`; Action-side transport tests rely
on this exact witness rather than a reduced seed. -/
private def actionTransportProbe : FSum :=
  [(.K, 1), (.S, 1), (.Y, 1), (.app .S .K, 1), (.app .K .S, 1), (.app .Y .K, 1)]

def transportProfileRat (src dst : LensID) : Rat :=
  l2NormSq (LaxCrossLensTransport.forward sheafTransport src dst actionTransportProbe)

/-- Maintenance guard: the action-layer witness must preserve the same total
information mass as the measure-layer probe. -/
private theorem actionTransportProbe_norm : l2NormSq actionTransportProbe = 6 := by
  native_decide

/-- Exact region witness preserved by the action-layer transport probe. -/
theorem actionTransportProbe_region_profile :
    transportProfileRat .omega .region = 2 := by
  native_decide

/-- Exact matula witness preserved by the action-layer transport probe. -/
theorem actionTransportProbe_matula_profile :
    transportProfileRat .omega .matula = 5 := by
  native_decide

theorem transportProfileRat_nonneg (src dst : LensID) :
    0 ≤ transportProfileRat src dst := by
  unfold transportProfileRat
  exact l2NormSq_nonneg _

def operationNaturalnessRat (sig : StepSignature) : Rat :=
  if sig.tacticLength ≤ 4 then
    1
  else if sig.tacticLength ≤ 10 then
    2
  else
    3

def transportCostRat (sig : StepSignature) : Rat :=
  let src := sig.sourceLens
  let dst := sig.targetLens
  if src = dst then
    0
  else if isSafeTransport src dst then
    1 + transportProfileRat src dst
  else
    3 + transportProfileRat src dst

def informationCompressionRat (sig : StepSignature) : Rat :=
  if sig.targetGoalComplexity ≤ sig.sourceGoalComplexity then
    if sig.sourceDepth + 1 = sig.targetDepth then
      (1 : Rat) / 2
    else
      1
  else
    2

def stepActionFromSignatureRat (sig : StepSignature) : Rat :=
  operationNaturalnessRat sig +
    transportCostRat sig +
    informationCompressionRat sig

def stepActionRat (step : ProofStep) : Rat :=
  stepActionFromSignatureRat step.signature

def pathActionRat (p : ProofPath) : Rat :=
  (p.steps.map stepActionRat).sum

noncomputable def transportProfile (src dst : LensID) : ℝ :=
  transportProfileRat src dst

noncomputable def operationNaturalness (step : ProofStep) : ℝ :=
  operationNaturalnessRat step.signature

noncomputable def transportCost (step : ProofStep) : ℝ :=
  transportCostRat step.signature

noncomputable def informationCompression (step : ProofStep) : ℝ :=
  informationCompressionRat step.signature

noncomputable def stepAction (step : ProofStep) : ℝ :=
  stepActionRat step

noncomputable def pathAction (p : ProofPath) : ℝ :=
  pathActionRat p

def transportProfileFloat (src dst : LensID) : Float :=
  ratToFloat (transportProfileRat src dst)

def operationNaturalnessFloat (step : ProofStep) : Float :=
  ratToFloat (operationNaturalnessRat step.signature)

def transportCostFloat (step : ProofStep) : Float :=
  ratToFloat (transportCostRat step.signature)

def informationCompressionFloat (step : ProofStep) : Float :=
  ratToFloat (informationCompressionRat step.signature)

def stepActionFloat (step : ProofStep) : Float :=
  ratToFloat (stepActionRat step)

def pathActionFloat (p : ProofPath) : Float :=
  ratToFloat (pathActionRat p)

theorem operationNaturalnessRat_nonneg (sig : StepSignature) :
    0 ≤ operationNaturalnessRat sig := by
  unfold operationNaturalnessRat
  by_cases h4 : sig.tacticLength ≤ 4
  · simp [h4]
  · by_cases h10 : sig.tacticLength ≤ 10
    · simp [h4, h10]
    · simp [h4, h10]

theorem transportCostRat_nonneg (sig : StepSignature) :
    0 ≤ transportCostRat sig := by
  unfold transportCostRat
  by_cases hsame : sig.sourceLens = sig.targetLens
  · simp [hsame]
  · by_cases hsafe : isSafeTransport sig.sourceLens sig.targetLens
    · have hprof := transportProfileRat_nonneg sig.sourceLens sig.targetLens
      have hone : (0 : Rat) ≤ 1 := by norm_num
      simp [hsame, hsafe]
      exact add_nonneg hone hprof
    · have hprof := transportProfileRat_nonneg sig.sourceLens sig.targetLens
      have hthree : (0 : Rat) ≤ 3 := by norm_num
      simp [hsame, hsafe]
      exact add_nonneg hthree hprof

theorem informationCompressionRat_nonneg (sig : StepSignature) :
    0 ≤ informationCompressionRat sig := by
  unfold informationCompressionRat
  by_cases hcomp : sig.targetGoalComplexity ≤ sig.sourceGoalComplexity
  · by_cases hdepth : sig.sourceDepth + 1 = sig.targetDepth
    · simp [hcomp, hdepth]
    · simp [hcomp, hdepth]
  · simp [hcomp]

theorem stepActionRat_nonneg (step : ProofStep) :
    0 ≤ stepActionRat step := by
  unfold stepActionRat stepActionFromSignatureRat
  have h1 := operationNaturalnessRat_nonneg step.signature
  have h2 := transportCostRat_nonneg step.signature
  have h3 := informationCompressionRat_nonneg step.signature
  exact add_nonneg (add_nonneg h1 h2) h3

theorem pathActionRat_nonneg (p : ProofPath) :
    0 ≤ pathActionRat p := by
  unfold pathActionRat
  induction p.steps with
  | nil =>
      simp
  | cons step rest ih =>
      simp [stepActionRat_nonneg, ih, add_nonneg]

theorem action_comp_rat (p q : ProofPath) :
    pathActionRat (ProofPath.comp p q) = pathActionRat p + pathActionRat q := by
  simp [pathActionRat, ProofPath.comp, List.map_append, List.sum_append]

private theorem stepListSum_eq_signatureSum (steps : List ProofStep) :
    (steps.map stepActionRat).sum =
      (steps.map (fun step => stepActionFromSignatureRat step.signature)).sum := by
  induction steps with
  | nil =>
      simp
  | cons step rest ih =>
      simp [stepActionRat, ih]

theorem pathActionRat_eq_signatureSum (p : ProofPath) :
    pathActionRat p = (p.signature.map stepActionFromSignatureRat).sum := by
  cases p
  rename_i start finish steps
  simpa [pathActionRat, ProofPath.signature] using stepListSum_eq_signatureSum steps

theorem action_comp (p q : ProofPath) :
    pathAction (ProofPath.comp p q) = pathAction p + pathAction q := by
  simp [pathAction, action_comp_rat]

theorem action_id (s : ProofState) :
    pathAction (ProofPath.id s) = 0 := by
  simp [pathAction, pathActionRat, ProofPath.id]

theorem action_nonneg (p : ProofPath) :
    0 ≤ pathAction p := by
  have hq : (0 : Rat) ≤ pathActionRat p := pathActionRat_nonneg p
  have hr : 0 ≤ (pathActionRat p : ℝ) := by
    exact (Rat.cast_nonneg (K := ℝ)).2 hq
  simpa [pathAction] using hr

theorem nucleus_step_zero_transport (step : ProofStep)
    (h : step.source.lens = step.target.lens) :
    transportCost step = 0 := by
  unfold transportCost transportCostRat
  simp [ProofStep.signature, h]

end PathIntegral
end HeytingLean
