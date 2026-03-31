import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.Filter.AtTopBot.Field
import HeytingLean.PathIntegral.Action

/-!
# PathIntegral.Measure

Boltzmann weights over proof paths, together with a sheaf-consistent transport
factor that measures information loss across lenses using the live sheaf
transport infrastructure.
-/

namespace HeytingLean
namespace PathIntegral

open HeytingLean.Embeddings
open HeytingLean.ATP.DifferentiableATP
open HeytingLean.LoF.Combinators.Differential.Compute
open scoped BigOperators

/-- Full-basis probe for measure-side transport accounting. -/
def measureTransportProbe : FSum :=
  [(.K, 1), (.S, 1), (.Y, 1), (.app .S .K, 1), (.app .K .S, 1), (.app .Y .K, 1)]

/-- Total information content carried by `measureTransportProbe`. -/
def measureTransportProbeNorm : Rat :=
  l2NormSq measureTransportProbe

/-- Because `sheafTransport.toPlato` is the identity, forwarding the probe only
depends on the destination lens. -/
theorem forward_probe_depends_on_dst (src dst : LensID) :
    LaxCrossLensTransport.forward sheafTransport src dst measureTransportProbe =
      lensProjection dst measureTransportProbe := by
  rfl

theorem preservedProbeNorm_eq_basisSize (src dst : LensID) :
    l2NormSq (LaxCrossLensTransport.forward sheafTransport src dst measureTransportProbe) =
      (basisSizeForLens dst : Rat) := by
  rw [forward_probe_depends_on_dst]
  cases dst <;> native_decide

theorem preservedProbeNorm_depends_only_on_dst (src₁ src₂ dst : LensID) :
    l2NormSq (LaxCrossLensTransport.forward sheafTransport src₁ dst measureTransportProbe) =
      l2NormSq (LaxCrossLensTransport.forward sheafTransport src₂ dst measureTransportProbe) := by
  rw [preservedProbeNorm_eq_basisSize, preservedProbeNorm_eq_basisSize]

theorem measureTransportProbeNorm_eq : measureTransportProbeNorm = 6 := by
  native_decide

theorem measureTransportProbeNorm_pos : 0 < measureTransportProbeNorm := by
  rw [measureTransportProbeNorm_eq]
  norm_num

theorem basisSizeForLens_nonneg (dst : LensID) : 0 ≤ (basisSizeForLens dst : Rat) := by
  exact_mod_cast Nat.zero_le (basisSizeForLens dst)

theorem basisSizeForLens_le_probeNorm (dst : LensID) :
    (basisSizeForLens dst : Rat) ≤ measureTransportProbeNorm := by
  rw [measureTransportProbeNorm_eq]
  cases dst <;> native_decide

/-- Rat-valued transport factor: `1 +` the fraction of probe information lost by
cross-lens projection. Self transport costs exactly `1`. -/
def lensTransitionFactorRat (src dst : LensID) : Rat :=
  if src = dst then
    1
  else
    let preserved := l2NormSq (LaxCrossLensTransport.forward sheafTransport src dst measureTransportProbe)
    1 + (measureTransportProbeNorm - preserved) / measureTransportProbeNorm

theorem lensTransitionFactorRat_eq_of_ne (src dst : LensID) (h : src ≠ dst) :
    lensTransitionFactorRat src dst =
      1 + (measureTransportProbeNorm - (basisSizeForLens dst : Rat)) / measureTransportProbeNorm := by
  simp [lensTransitionFactorRat, h, preservedProbeNorm_eq_basisSize]

theorem lensTransitionFactorRat_depends_only_on_dst
    {src₁ src₂ dst : LensID}
    (h₁ : src₁ ≠ dst)
    (h₂ : src₂ ≠ dst) :
    lensTransitionFactorRat src₁ dst = lensTransitionFactorRat src₂ dst := by
  rw [lensTransitionFactorRat_eq_of_ne _ _ h₁, lensTransitionFactorRat_eq_of_ne _ _ h₂]

theorem lensTransitionFactorRat_ge_one (src dst : LensID) :
    1 ≤ lensTransitionFactorRat src dst := by
  by_cases h : src = dst
  · simp [lensTransitionFactorRat, h]
  · rw [lensTransitionFactorRat_eq_of_ne _ _ h]
    have hnum :
        0 ≤ measureTransportProbeNorm - (basisSizeForLens dst : Rat) := by
      exact sub_nonneg.mpr (basisSizeForLens_le_probeNorm dst)
    have hfrac :
        0 ≤ (measureTransportProbeNorm - (basisSizeForLens dst : Rat)) / measureTransportProbeNorm := by
      exact div_nonneg hnum (le_of_lt measureTransportProbeNorm_pos)
    linarith

theorem lensTransitionFactorRat_le_two (src dst : LensID) :
    lensTransitionFactorRat src dst ≤ 2 := by
  by_cases h : src = dst
  · simp [lensTransitionFactorRat, h]
  · rw [lensTransitionFactorRat_eq_of_ne _ _ h]
    have hnonneg : 0 ≤ (basisSizeForLens dst : Rat) := basisSizeForLens_nonneg dst
    have hnum :
        measureTransportProbeNorm - (basisSizeForLens dst : Rat) ≤ measureTransportProbeNorm := by
      linarith
    have hfrac :
        (measureTransportProbeNorm - (basisSizeForLens dst : Rat)) / measureTransportProbeNorm ≤ 1 := by
      rw [show (1 : Rat) = measureTransportProbeNorm / measureTransportProbeNorm by
        field_simp [measureTransportProbeNorm_pos.ne']]
      exact div_le_div_of_nonneg_right hnum (le_of_lt measureTransportProbeNorm_pos)
    linarith

noncomputable section

def pathWeight (β : ℝ) (p : ProofPath) : ℝ :=
  Real.exp (-β * pathAction p)

def propagator (β : ℝ) (paths : Finset ProofPath) : ℝ :=
  Finset.sum paths (fun p => pathWeight β p)

def partitionFunction (β : ℝ) (paths : Finset ProofPath) : ℝ :=
  propagator β paths

def pathProbability (β : ℝ) (paths : Finset ProofPath)
    (p : ProofPath) (_h : p ∈ paths) (_hZ : partitionFunction β paths ≠ 0) : ℝ :=
  pathWeight β p / partitionFunction β paths

def lensTransitionFactor (src dst : LensID) : ℝ :=
  lensTransitionFactorRat src dst

structure SheafConsistentMeasure where
  weight : ProofPath → ℝ
  nonneg : ∀ p, 0 ≤ weight p
  transportFactor : LensID → LensID → ℝ
  cocycle_compatible :
    ∀ src mid dst, transportFactor src dst ≤ transportFactor src mid * transportFactor mid dst

end

def lensTransitionFactorFloat (src dst : LensID) : Float :=
  ratToFloat (lensTransitionFactorRat src dst)

def pathWeightFloat (β : Float) (p : ProofPath) : Float :=
  Float.exp (-β * pathActionFloat p)

def propagatorFloat (β : Float) (paths : List ProofPath) : Float :=
  paths.foldl (fun acc p => acc + pathWeightFloat β p) 0

def partitionFunctionFloat (β : Float) (paths : List ProofPath) : Float :=
  propagatorFloat β paths

def pathProbabilityFloat (β : Float) (paths : List ProofPath) (p : ProofPath) : Float :=
  let z := partitionFunctionFloat β paths
  if z == 0 then
    0
  else
    pathWeightFloat β p / z

theorem weight_comp (β : ℝ) (p q : ProofPath) :
    pathWeight β (ProofPath.comp p q) = pathWeight β p * pathWeight β q := by
  have haction : pathAction (ProofPath.comp p q) = pathAction p + pathAction q := action_comp p q
  rw [pathWeight, haction, pathWeight, pathWeight]
  have hexp : -β * (pathAction p + pathAction q) = (-β * pathAction p) + (-β * pathAction q) := by
    ring
  rw [hexp, Real.exp_add]

theorem weight_nonneg (β : ℝ) (p : ProofPath) :
    0 ≤ pathWeight β p := by
  unfold pathWeight
  exact Real.exp_nonneg _

theorem lensTransitionFactor_nonneg (src dst : LensID) :
    0 ≤ lensTransitionFactor src dst := by
  have hnonRat : (0 : Rat) ≤ lensTransitionFactorRat src dst := by
    have hgeRat : (1 : Rat) ≤ lensTransitionFactorRat src dst := lensTransitionFactorRat_ge_one src dst
    linarith
  have hnon : (0 : ℝ) ≤ (lensTransitionFactorRat src dst : ℝ) := by
    exact_mod_cast hnonRat
  simpa [lensTransitionFactor] using hnon

theorem lensTransitionFactor_refl (l : LensID) :
    lensTransitionFactor l l = 1 := by
  simp [lensTransitionFactor, lensTransitionFactorRat]

theorem lensTransitionFactor_cocycle (src mid dst : LensID) :
    lensTransitionFactor src dst ≤
      lensTransitionFactor src mid * lensTransitionFactor mid dst := by
  by_cases hsd : src = dst
  · subst hsd
    have h₁Rat : (1 : Rat) ≤ lensTransitionFactorRat src mid := lensTransitionFactorRat_ge_one src mid
    have h₂Rat : (1 : Rat) ≤ lensTransitionFactorRat mid src := lensTransitionFactorRat_ge_one mid src
    have h₁ : (1 : ℝ) ≤ lensTransitionFactor src mid := by
      have hcast : (1 : ℝ) ≤ (lensTransitionFactorRat src mid : ℝ) := by
        exact_mod_cast h₁Rat
      simpa [lensTransitionFactor] using hcast
    have h₂ : (1 : ℝ) ≤ lensTransitionFactor mid src := by
      have hcast : (1 : ℝ) ≤ (lensTransitionFactorRat mid src : ℝ) := by
        exact_mod_cast h₂Rat
      simpa [lensTransitionFactor] using hcast
    have hmul : 1 ≤ lensTransitionFactor src mid * lensTransitionFactor mid src := by
      nlinarith [h₁, h₂, lensTransitionFactor_nonneg src mid, lensTransitionFactor_nonneg mid src]
    simpa [lensTransitionFactor_refl] using hmul
  · by_cases hsm : src = mid
    · subst hsm
      simp [lensTransitionFactor, lensTransitionFactorRat, hsd]
    · by_cases hmd : mid = dst
      · subst hmd
        simp [lensTransitionFactor, lensTransitionFactorRat, hsm]
      · have hsameRat :
          lensTransitionFactorRat src dst = lensTransitionFactorRat mid dst :=
            lensTransitionFactorRat_depends_only_on_dst hsd hmd
        have hsame : lensTransitionFactor src dst = lensTransitionFactor mid dst := by
          simpa [lensTransitionFactor] using congrArg (fun q : Rat => (q : ℝ)) hsameRat
        rw [hsame]
        have h₁Rat : (1 : Rat) ≤ lensTransitionFactorRat src mid := lensTransitionFactorRat_ge_one src mid
        have h₁ : (1 : ℝ) ≤ lensTransitionFactor src mid := by
          have hcast : (1 : ℝ) ≤ (lensTransitionFactorRat src mid : ℝ) := by
            exact_mod_cast h₁Rat
          simpa [lensTransitionFactor] using hcast
        nlinarith [h₁, lensTransitionFactor_nonneg mid dst]

theorem lensTransitionFactor_asymmetry_witness :
    lensTransitionFactorRat .omega .region ≠ lensTransitionFactorRat .omega .matula := by
  native_decide

theorem pathWeight_ratio_eq_exp_gap (p q : ProofPath) :
    (fun β : ℝ => pathWeight β p / pathWeight β q) =
      (fun β : ℝ => Real.exp (-(β * (pathAction p - pathAction q)))) := by
  funext β
  unfold pathWeight
  rw [div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add]
  congr 1
  ring

theorem beta_limit_classical (p p_min : ProofPath)
    (h : pathAction p_min < pathAction p) :
    Filter.Tendsto (fun β => pathWeight β p / pathWeight β p_min)
      Filter.atTop (nhds 0) := by
  rw [pathWeight_ratio_eq_exp_gap]
  have hgap : 0 < pathAction p - pathAction p_min := sub_pos.mpr h
  have htop :
      Filter.Tendsto (fun β : ℝ => β * (pathAction p - pathAction p_min))
        Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_mul_const hgap Filter.tendsto_id
  have hbot :
      Filter.Tendsto (fun β : ℝ => -(β * (pathAction p - pathAction p_min)))
        Filter.atTop Filter.atBot :=
    Filter.tendsto_neg_atTop_atBot.comp htop
  exact Real.tendsto_exp_atBot.comp hbot

theorem beta_limit_uniform (p : ProofPath) :
    pathWeight 0 p = 1 := by
  simp [pathWeight]

theorem propagator_nonneg (β : ℝ) (paths : Finset ProofPath) :
    0 ≤ propagator β paths := by
  classical
  unfold propagator
  exact Finset.sum_nonneg (fun p _ => weight_nonneg β p)

noncomputable def boltzmannMeasure (β : ℝ) : SheafConsistentMeasure where
  weight := pathWeight β
  nonneg := weight_nonneg β
  transportFactor := lensTransitionFactor
  cocycle_compatible := lensTransitionFactor_cocycle

theorem weight_sheaf_consistency (β : ℝ) :
    ∀ src mid dst,
      (boltzmannMeasure β).transportFactor src dst ≤
        (boltzmannMeasure β).transportFactor src mid *
          (boltzmannMeasure β).transportFactor mid dst :=
  (boltzmannMeasure β).cocycle_compatible

end PathIntegral
end HeytingLean
