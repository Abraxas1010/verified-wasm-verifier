import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Order.Basic
import HeytingLean.PathIntegral.Measure

/-!
# PathIntegral.AnnealingTheory

Finite-path annealing theory for Boltzmann-weighted proof search.
-/

namespace HeytingLean
namespace PathIntegral

open scoped BigOperators

/-- Linear annealing schedule. -/
def linearBeta (β₀ rate : ℝ) (n : ℕ) : ℝ :=
  β₀ + rate * n

/-- Geometric annealing schedule. -/
def geometricBeta (β₀ c : ℝ) (n : ℕ) : ℝ :=
  β₀ * c ^ n

/-- Logarithmic annealing schedule (Hajek-style cooling). -/
noncomputable def logarithmicBeta (d : ℝ) (n : ℕ) : ℝ :=
  d * Real.log ((n : ℝ) + 2)

/-- Runtime schedule selector for the executable search surface. -/
inductive AnnealingSchedule where
  | linear (rate : Float)
  | geometric (ratio : Float)
  | logarithmic (scale : Float)
  deriving Repr

namespace AnnealingSchedule

def betaAt (sched : AnnealingSchedule) (β₀ : Float) (n : Nat) : Float :=
  match sched with
  | .linear rate => β₀ + rate * Float.ofNat n
  | .geometric ratio => β₀ * Float.pow ratio (Float.ofNat n)
  | .logarithmic scale => scale * Float.log (Float.ofNat n + 2.0)

def name : AnnealingSchedule → String
  | .linear _ => "linear"
  | .geometric _ => "geometric"
  | .logarithmic _ => "logarithmic"

def nextBeta (sched : AnnealingSchedule) (β₀ _currentβ : Float) (step : Nat)
    (_beam : List (ProofPath × Float)) : Float :=
  sched.betaAt β₀ step

end AnnealingSchedule

noncomputable section

/-- Candidate action gaps against a distinguished minimizer. -/
def actionGapCandidates (paths : Finset ProofPath) (p_min : ProofPath) : Finset ℝ :=
  (paths.erase p_min).image (fun q => pathAction q - pathAction p_min)

theorem erased_paths_nonempty (paths : Finset ProofPath) (p_min : ProofPath)
    (hp : p_min ∈ paths) (hcard : 1 < paths.card) :
    (paths.erase p_min).Nonempty := by
  have hpos : 0 < (paths.erase p_min).card := by
    rw [Finset.card_erase_of_mem hp]
    exact Nat.sub_pos_of_lt hcard
  exact Finset.card_pos.mp hpos

theorem actionGapCandidates_nonempty (paths : Finset ProofPath) (p_min : ProofPath)
    (hp : p_min ∈ paths) (hcard : 1 < paths.card) :
    (actionGapCandidates paths p_min).Nonempty := by
  classical
  exact (erased_paths_nonempty paths p_min hp hcard).image _

/-- Minimum positive action separation from the distinguished minimizer. Returns
`0` only in the degenerate singleton case. -/
noncomputable def actionGap (paths : Finset ProofPath) (p_min : ProofPath) : ℝ :=
  if hne : (actionGapCandidates paths p_min).Nonempty then
    (actionGapCandidates paths p_min).min' hne
  else
    0

theorem actionGapCandidates_pos (paths : Finset ProofPath) (p_min : ProofPath)
    (hstrict : ∀ q ∈ paths, q ≠ p_min → pathAction p_min < pathAction q) :
    ∀ x ∈ actionGapCandidates paths p_min, 0 < x := by
  classical
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨q, hq, rfl⟩
  have hq_paths : q ∈ paths := Finset.mem_of_mem_erase hq
  have hq_ne : q ≠ p_min := Finset.ne_of_mem_erase hq
  exact sub_pos.mpr (hstrict q hq_paths hq_ne)

theorem actionGap_pos (paths : Finset ProofPath) (p_min : ProofPath)
    (hp : p_min ∈ paths)
    (hstrict : ∀ q ∈ paths, q ≠ p_min → pathAction p_min < pathAction q)
    (hcard : 1 < paths.card) :
    0 < actionGap paths p_min := by
  classical
  have hne : (actionGapCandidates paths p_min).Nonempty :=
    actionGapCandidates_nonempty paths p_min hp hcard
  have hpos :
      0 < (actionGapCandidates paths p_min).min' hne :=
    actionGapCandidates_pos paths p_min hstrict _ (Finset.min'_mem _ _)
  simpa [actionGap, hne] using hpos

theorem actionGap_le_gap (paths : Finset ProofPath) (p_min q : ProofPath)
    (hq : q ∈ paths) (hneq : q ≠ p_min) :
    actionGap paths p_min ≤ pathAction q - pathAction p_min := by
  classical
  have hmem : pathAction q - pathAction p_min ∈ actionGapCandidates paths p_min := by
    refine Finset.mem_image.mpr ?_
    exact ⟨q, Finset.mem_erase.mpr ⟨hneq, hq⟩, rfl⟩
  unfold actionGap
  have hne : (actionGapCandidates paths p_min).Nonempty := ⟨_, hmem⟩
  simp [hne]
  exact Finset.min'_le _ _ hmem

theorem geometricBeta_nonneg (β₀ c : ℝ) (hβ : 0 ≤ β₀) (hc : 0 ≤ c) (n : ℕ) :
    0 ≤ geometricBeta β₀ c n := by
  unfold geometricBeta
  exact mul_nonneg hβ (pow_nonneg hc _)

theorem geometricBeta_tendsto_atTop (β₀ : ℝ) (hβ : 0 < β₀) (c : ℝ) (hc : 1 < c) :
    Filter.Tendsto (geometricBeta β₀ c) Filter.atTop Filter.atTop := by
  have hpow : Filter.Tendsto (fun n : ℕ => (c ^ n : ℝ)) Filter.atTop Filter.atTop := by
    simpa using tendsto_pow_atTop_atTop_of_one_lt hc
  simpa [geometricBeta] using hpow.const_mul_atTop hβ

theorem logarithmicBeta_tendsto_atTop (d : ℝ) (hd : 0 < d) :
    Filter.Tendsto (logarithmicBeta d) Filter.atTop Filter.atTop := by
  have hnat :
      Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 2)) Filter.atTop Filter.atTop := by
    simpa using
      (Filter.tendsto_atTop_add_const_right Filter.atTop (2 : ℝ)
        (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop))
  have hlog :
      Filter.Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 2)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp hnat
  simpa [logarithmicBeta, mul_comm] using hlog.const_mul_atTop hd

theorem geometric_convergence_rate
    (paths : Finset ProofPath)
    (p_min : ProofPath) (_hp : p_min ∈ paths)
    (_hstrict : ∀ q ∈ paths, q ≠ p_min → pathAction p_min < pathAction q)
    (_hcard : 1 < paths.card)
    (β₀ c : ℝ) (hβ : 0 < β₀) (hc : 1 < c) :
    ∀ p ∈ paths, p ≠ p_min →
      ∀ n : ℕ,
        pathWeight (geometricBeta β₀ c n) p / pathWeight (geometricBeta β₀ c n) p_min ≤
          Real.exp (-(actionGap paths p_min * geometricBeta β₀ c n)) := by
  intro p hp_mem hp_ne n
  rw [show pathWeight (geometricBeta β₀ c n) p / pathWeight (geometricBeta β₀ c n) p_min =
      Real.exp (-(geometricBeta β₀ c n * (pathAction p - pathAction p_min))) by
      simpa using congrFun (pathWeight_ratio_eq_exp_gap p p_min) (geometricBeta β₀ c n)]
  have hgap_le : actionGap paths p_min ≤ pathAction p - pathAction p_min :=
    actionGap_le_gap paths p_min p hp_mem hp_ne
  have hβ_nonneg : 0 ≤ geometricBeta β₀ c n := by
    exact geometricBeta_nonneg β₀ c hβ.le (le_trans (by norm_num) hc.le) n
  have harg :
      -(geometricBeta β₀ c n * (pathAction p - pathAction p_min)) ≤
        -(actionGap paths p_min * geometricBeta β₀ c n) := by
    nlinarith
  have hexp := Real.exp_le_exp.mpr harg
  simpa [mul_assoc, mul_left_comm, mul_comm] using hexp

theorem geometric_convergence_rate_tendsto
    (paths : Finset ProofPath)
    (p_min : ProofPath) (hp : p_min ∈ paths)
    (hstrict : ∀ q ∈ paths, q ≠ p_min → pathAction p_min < pathAction q)
    (hcard : 1 < paths.card)
    (β₀ c : ℝ) (hβ : 0 < β₀) (hc : 1 < c) :
    ∀ p ∈ paths, p ≠ p_min →
      Filter.Tendsto
        (fun n => pathWeight (geometricBeta β₀ c n) p / pathWeight (geometricBeta β₀ c n) p_min)
        Filter.atTop (nhds 0) := by
  intro p hp_mem hp_ne
  have hΔ : 0 < actionGap paths p_min := actionGap_pos paths p_min hp hstrict hcard
  have hβt : Filter.Tendsto (geometricBeta β₀ c) Filter.atTop Filter.atTop :=
    geometricBeta_tendsto_atTop β₀ hβ c hc
  have hscaled :
      Filter.Tendsto (fun n => actionGap paths p_min * geometricBeta β₀ c n)
        Filter.atTop Filter.atTop := by
    simpa [mul_comm] using hβt.const_mul_atTop hΔ
  have hupper :
      Filter.Tendsto (fun n => Real.exp (-(actionGap paths p_min * geometricBeta β₀ c n)))
        Filter.atTop (nhds 0) := by
    exact Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot.comp hscaled)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper ?_ ?_
  · intro n
    have hnum : 0 < pathWeight (geometricBeta β₀ c n) p := by
      unfold pathWeight
      exact Real.exp_pos _
    have hden : 0 < pathWeight (geometricBeta β₀ c n) p_min := by
      unfold pathWeight
      exact Real.exp_pos _
    exact le_of_lt (div_pos hnum hden)
  · intro n
    exact geometric_convergence_rate paths p_min hp hstrict hcard β₀ c hβ hc p hp_mem hp_ne n

end

end PathIntegral
end HeytingLean
