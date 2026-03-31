import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import HeytingLean.Probability.InfoTheory
import HeytingLean.Economics.Kelly.Discrete

namespace HeytingLean
namespace Economics
namespace Kelly

noncomputable section

open scoped BigOperators

open HeytingLean.Probability.InfoTheory
open HeytingLean.Probability.InfoTheory.FinDist

namespace SideInfo

variable {Signal Outcome : Type u} [Fintype Signal] [Fintype Outcome]

def growthRateWithInfo (PXY : FinDist (Signal × Outcome)) (odds : Outcome → ℝ)
    (g : Signal → FinDist Outcome) : ℝ :=
  ∑ ab : Signal × Outcome, PXY.pmf ab * Real.log ((g ab.1).pmf ab.2 * odds ab.2)

def condBet (PXY : FinDist (Signal × Outcome)) (hP : PXY.Pos) : Signal → FinDist Outcome :=
  fun s => HeytingLean.Probability.InfoTheory.FinDist.condDistOfPos (α := Signal) (β := Outcome) PXY hP s

def optimalWithInfo (PXY : FinDist (Signal × Outcome)) (hP : PXY.Pos) (odds : Outcome → ℝ) : ℝ :=
  growthRateWithInfo (Signal := Signal) (Outcome := Outcome) PXY odds (condBet PXY hP)

def optimalNoInfo (PXY : FinDist (Signal × Outcome)) (odds : Outcome → ℝ) : ℝ :=
  let PY := marginalRight (α := Signal) (β := Outcome) PXY
  growthRate (Outcome := Outcome) PY PY odds

theorem condBet_optimal_pointwise
    (PXY : FinDist (Signal × Outcome)) (hP : PXY.Pos) (odds : Outcome → ℝ)
    (hodds : ∀ y, 0 < odds y) (g : Signal → FinDist Outcome) (hg : ∀ s, (g s).Pos) :
    growthRateWithInfo (Signal := Signal) (Outcome := Outcome) PXY odds g
      ≤ growthRateWithInfo (Signal := Signal) (Outcome := Outcome) PXY odds (condBet PXY hP) := by
  classical
  let PX := marginalLeft (α := Signal) (β := Outcome) PXY
  have hPXpos : PX.Pos :=
    HeytingLean.Probability.InfoTheory.FinDist.marginalLeft_pos_of_Pos (α := Signal) (β := Outcome) PXY hP
  -- Rewrite the joint-weighted sum into `∑ s, PX(s) * growthRate(cond(s), g(s))`.
  have factor (g' : Signal → FinDist Outcome) :
      growthRateWithInfo (Signal := Signal) (Outcome := Outcome) PXY odds g'
        = ∑ s : Signal,
            PX.pmf s * growthRate (Outcome := Outcome)
              (HeytingLean.Probability.InfoTheory.FinDist.condDistOfPos (α := Signal) (β := Outcome) PXY hP s)
              (g' s) odds := by
    unfold growthRateWithInfo
    calc
      (∑ ab : Signal × Outcome, PXY.pmf ab * Real.log ((g' ab.1).pmf ab.2 * odds ab.2))
          = ∑ s : Signal, ∑ y : Outcome, PXY.pmf (s, y) * Real.log ((g' s).pmf y * odds y) := by
              simpa using
                (Fintype.sum_prod_type (fun ab : Signal × Outcome =>
                  PXY.pmf ab * Real.log ((g' ab.1).pmf ab.2 * odds ab.2)))
      _ = ∑ s : Signal,
            PX.pmf s * (∑ y : Outcome,
              (HeytingLean.Probability.InfoTheory.FinDist.condDistOfPos (α := Signal) (β := Outcome) PXY hP s).pmf y
                * Real.log ((g' s).pmf y * odds y)) := by
              refine Finset.sum_congr rfl ?_
              intro s _
              have hmul : ∀ y : Outcome,
                  PXY.pmf (s, y) =
                    PX.pmf s
                      * (HeytingLean.Probability.InfoTheory.FinDist.condDistOfPos (α := Signal) (β := Outcome) PXY hP s).pmf y := by
                intro y
                have h :=
                  HeytingLean.Probability.InfoTheory.FinDist.condDistOfPos_pmf_mul_marginalLeft
                    (α := Signal) (β := Outcome) (PXY := PXY) hP (s, y)
                simpa [PX] using h.symm
              -- substitute and factor out `PX(s)`
              have :
                  (∑ y : Outcome, PXY.pmf (s, y) * Real.log ((g' s).pmf y * odds y))
                    = PX.pmf s * (∑ y : Outcome,
                        (HeytingLean.Probability.InfoTheory.FinDist.condDistOfPos (α := Signal) (β := Outcome) PXY hP s).pmf y
                          * Real.log ((g' s).pmf y * odds y)) := by
                  calc
                    (∑ y : Outcome, PXY.pmf (s, y) * Real.log ((g' s).pmf y * odds y))
                        = ∑ y : Outcome,
                            (PX.pmf s
                              * (HeytingLean.Probability.InfoTheory.FinDist.condDistOfPos (α := Signal) (β := Outcome) PXY hP s).pmf y)
                              * Real.log ((g' s).pmf y * odds y) := by
                                refine Finset.sum_congr rfl ?_
                                intro y _
                                simp [hmul y, mul_assoc]
                    _ = PX.pmf s * (∑ y : Outcome,
                          (HeytingLean.Probability.InfoTheory.FinDist.condDistOfPos (α := Signal) (β := Outcome) PXY hP s).pmf y
                            * Real.log ((g' s).pmf y * odds y)) := by
                          simp [Finset.mul_sum, mul_assoc]
              simpa [growthRate] using this
      _ = ∑ s : Signal, PX.pmf s * growthRate
            (Outcome := Outcome)
            (HeytingLean.Probability.InfoTheory.FinDist.condDistOfPos (α := Signal) (β := Outcome) PXY hP s)
            (g' s) odds := by
              simp [growthRate]
  -- Pointwise apply the Phase-2 inequality and sum.
  have hpoint :
      ∀ s : Signal,
        growthRate (Outcome := Outcome)
            (HeytingLean.Probability.InfoTheory.FinDist.condDistOfPos (α := Signal) (β := Outcome) PXY hP s)
            (g s) odds
          ≤ growthRate (Outcome := Outcome)
            (HeytingLean.Probability.InfoTheory.FinDist.condDistOfPos (α := Signal) (β := Outcome) PXY hP s)
            (HeytingLean.Probability.InfoTheory.FinDist.condDistOfPos (α := Signal) (β := Outcome) PXY hP s) odds := by
    intro s
    have hcondpos : (HeytingLean.Probability.InfoTheory.FinDist.condDistOfPos (α := Signal) (β := Outcome) PXY hP s).Pos := by
      intro y
      -- positive ratio of positive terms
      have hp : 0 < PXY.pmf (s, y) := hP (s, y)
      have hx : 0 < PX.pmf s := hPXpos s
      -- unfold `condDistOfPos`
      simp [HeytingLean.Probability.InfoTheory.FinDist.condDistOfPos, PX, div_pos hp hx]
    exact
      growthRate_le_at_true (Outcome := Outcome)
        (p := HeytingLean.Probability.InfoTheory.FinDist.condDistOfPos (α := Signal) (β := Outcome) PXY hP s)
        (b := g s) (odds := odds) hcondpos (hg s) hodds
  have hsum :
      (∑ s : Signal,
        PX.pmf s * growthRate (Outcome := Outcome)
          (HeytingLean.Probability.InfoTheory.FinDist.condDistOfPos (α := Signal) (β := Outcome) PXY hP s)
          (g s) odds)
        ≤
      (∑ s : Signal,
        PX.pmf s * growthRate (Outcome := Outcome)
          (HeytingLean.Probability.InfoTheory.FinDist.condDistOfPos (α := Signal) (β := Outcome) PXY hP s)
          (HeytingLean.Probability.InfoTheory.FinDist.condDistOfPos (α := Signal) (β := Outcome) PXY hP s) odds) := by
    refine Finset.sum_le_sum ?_
    intro s _
    have hsnonneg : 0 ≤ PX.pmf s := PX.nonneg s
    exact mul_le_mul_of_nonneg_left (hpoint s) hsnonneg
  -- Put it together.
  have hL := factor g
  have hR : growthRateWithInfo (Signal := Signal) (Outcome := Outcome) PXY odds (condBet PXY hP)
      = ∑ s : Signal,
          PX.pmf s * growthRate (Outcome := Outcome)
            (HeytingLean.Probability.InfoTheory.FinDist.condDistOfPos (α := Signal) (β := Outcome) PXY hP s)
            (HeytingLean.Probability.InfoTheory.FinDist.condDistOfPos (α := Signal) (β := Outcome) PXY hP s) odds := by
    simpa [condBet] using (factor (condBet PXY hP))
  linarith [hL, hR, hsum]

theorem value_of_side_information_eq_mutualInfo
    (PXY : FinDist (Signal × Outcome)) (hP : PXY.Pos) (odds : Outcome → ℝ) (hodds : ∀ y, 0 < odds y) :
    optimalWithInfo (Signal := Signal) (Outcome := Outcome) PXY hP odds
      - optimalNoInfo (Signal := Signal) (Outcome := Outcome) PXY odds
      = mutualInfo (α := Signal) (β := Outcome) PXY := by
  classical
  let PX := marginalLeft (α := Signal) (β := Outcome) PXY
  let PY := marginalRight (α := Signal) (β := Outcome) PXY
  have hPXpos : PX.Pos :=
    HeytingLean.Probability.InfoTheory.FinDist.marginalLeft_pos_of_Pos (α := Signal) (β := Outcome) PXY hP
  have hPYpos : PY.Pos :=
    HeytingLean.Probability.InfoTheory.FinDist.marginalRight_pos_of_Pos (α := Signal) (β := Outcome) PXY hP
  -- Expand optimal-with-info using the conditional bet:
  -- `log((PXY/PX)*odds) = log(PXY/PX) + log odds`.
  have hoptInfo :
      optimalWithInfo (Signal := Signal) (Outcome := Outcome) PXY hP odds
        = (∑ ab : Signal × Outcome, PXY.pmf ab * Real.log (PXY.pmf ab / PX.pmf ab.1))
          + (∑ y : Outcome, PY.pmf y * Real.log (odds y)) := by
    unfold optimalWithInfo growthRateWithInfo condBet
    -- split sum over `(s,y)`
    have hlogmul :
        ∀ ab : Signal × Outcome,
          Real.log ((PXY.pmf ab / PX.pmf ab.1) * odds ab.2)
            = Real.log (PXY.pmf ab / PX.pmf ab.1) + Real.log (odds ab.2) := by
      intro ab
      have hp : 0 < PXY.pmf ab := hP ab
      have hx : 0 < PX.pmf ab.1 := hPXpos ab.1
      have ho : 0 < odds ab.2 := hodds ab.2
      have hratio : 0 < PXY.pmf ab / PX.pmf ab.1 := div_pos hp hx
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (Real.log_mul (ne_of_gt hratio) (ne_of_gt ho))
    -- compute the log-odds marginalization: `∑_{s,y} p(s,y) log odds(y) = ∑_y p(y) log odds(y)`
    have hsumOdds :
        (∑ ab : Signal × Outcome, PXY.pmf ab * Real.log (odds ab.2))
          = ∑ y : Outcome, PY.pmf y * Real.log (odds y) := by
      -- rewrite as an iterated sum and use the definition of `PY`.
      calc
        (∑ ab : Signal × Outcome, PXY.pmf ab * Real.log (odds ab.2))
            = ∑ y : Outcome, ∑ s : Signal, PXY.pmf (s, y) * Real.log (odds y) := by
                simpa using
                  (Fintype.sum_prod_type_right (fun ab : Signal × Outcome =>
                    PXY.pmf ab * Real.log (odds ab.2)))
        _ = ∑ y : Outcome, (∑ s : Signal, PXY.pmf (s, y)) * Real.log (odds y) := by
                simp [Finset.sum_mul]
        _ = ∑ y : Outcome, PY.pmf y * Real.log (odds y) := by
                rfl
    calc
      (∑ ab : Signal × Outcome,
          PXY.pmf ab
            * Real.log ((HeytingLean.Probability.InfoTheory.FinDist.condDistOfPos (α := Signal) (β := Outcome) PXY hP ab.1).pmf ab.2 * odds ab.2))
          = (∑ ab : Signal × Outcome,
              PXY.pmf ab * Real.log ((PXY.pmf ab / PX.pmf ab.1) * odds ab.2)) := by
                refine Finset.sum_congr rfl ?_
                intro ab _
                -- unfold `condDistOfPos` (pmf is exactly `PXY/ PX`), then simplify.
                simp [HeytingLean.Probability.InfoTheory.FinDist.condDistOfPos, PX]
      _ = (∑ ab : Signal × Outcome,
              PXY.pmf ab * (Real.log (PXY.pmf ab / PX.pmf ab.1) + Real.log (odds ab.2))) := by
                refine Finset.sum_congr rfl ?_
                intro ab _
                simpa using congrArg (fun t => PXY.pmf ab * t) (hlogmul ab)
      _ = (∑ ab : Signal × Outcome, PXY.pmf ab * Real.log (PXY.pmf ab / PX.pmf ab.1))
            + (∑ ab : Signal × Outcome, PXY.pmf ab * Real.log (odds ab.2)) := by
                simp [mul_add, Finset.sum_add_distrib]
      _ = (∑ ab : Signal × Outcome, PXY.pmf ab * Real.log (PXY.pmf ab / PX.pmf ab.1))
            + (∑ y : Outcome, PY.pmf y * Real.log (odds y)) := by simp [hsumOdds]
  -- Expand optimal-no-info similarly:
  have hoptNo :
      optimalNoInfo (Signal := Signal) (Outcome := Outcome) PXY odds
        = (∑ y : Outcome, PY.pmf y * Real.log (PY.pmf y))
          + (∑ y : Outcome, PY.pmf y * Real.log (odds y)) := by
    -- Expand `growthRate PY PY odds` using `log_mul`.
    have hlogmul :
        ∀ y : Outcome, Real.log ((marginalRight (α := Signal) (β := Outcome) PXY).pmf y * odds y)
          = Real.log ((marginalRight (α := Signal) (β := Outcome) PXY).pmf y) + Real.log (odds y) := by
      intro y
      have hp : 0 < PY.pmf y := hPYpos y
      have ho : 0 < odds y := hodds y
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (Real.log_mul (ne_of_gt hp) (ne_of_gt ho))
    simp [optimalNoInfo, growthRate, PY, hlogmul, mul_add, Finset.sum_add_distrib]
  -- Difference is exactly the KL ratio form of mutual information.
  have hMI :
      mutualInfo (α := Signal) (β := Outcome) PXY
        = (∑ ab : Signal × Outcome, PXY.pmf ab * Real.log (PXY.pmf ab / (PX.pmf ab.1 * PY.pmf ab.2))) := by
    simpa [PX, PY] using
      (HeytingLean.Probability.InfoTheory.FinDist.mutualInfo_eq_sum_mul_log_ratio_of_Pos
        (α := Signal) (β := Outcome) (PXY := PXY) hP)
  -- Rewrite the difference into that same expression using `log_div` and `log_mul`.
  have hdiff :
      (∑ ab : Signal × Outcome, PXY.pmf ab * Real.log (PXY.pmf ab / PX.pmf ab.1))
        - (∑ y : Outcome, PY.pmf y * Real.log (PY.pmf y))
        = ∑ ab : Signal × Outcome, PXY.pmf ab * Real.log (PXY.pmf ab / (PX.pmf ab.1 * PY.pmf ab.2)) := by
    -- `log(p/(PX*PY)) = log(p/PX) - log PY` and sum over joint gives the marginal term.
    have hlog :
        ∀ ab : Signal × Outcome,
          Real.log (PXY.pmf ab / (PX.pmf ab.1 * PY.pmf ab.2))
            = Real.log (PXY.pmf ab / PX.pmf ab.1) - Real.log (PY.pmf ab.2) := by
      intro ab
      have hp : 0 < PXY.pmf ab := hP ab
      have hx : 0 < PX.pmf ab.1 := hPXpos ab.1
      have hy : 0 < PY.pmf ab.2 := hPYpos ab.2
      have hx0 : PX.pmf ab.1 ≠ 0 := ne_of_gt hx
      have hy0 : PY.pmf ab.2 ≠ 0 := ne_of_gt hy
      have hxy0 : PX.pmf ab.1 * PY.pmf ab.2 ≠ 0 := mul_ne_zero hx0 hy0
      have hmul : Real.log (PX.pmf ab.1 * PY.pmf ab.2) = Real.log (PX.pmf ab.1) + Real.log (PY.pmf ab.2) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using (Real.log_mul hx0 hy0)
      have hdiv : Real.log (PXY.pmf ab / PX.pmf ab.1) = Real.log (PXY.pmf ab) - Real.log (PX.pmf ab.1) := by
        simpa [div_eq_mul_inv] using Real.log_div (ne_of_gt hp) hx0
      calc
        Real.log (PXY.pmf ab / (PX.pmf ab.1 * PY.pmf ab.2))
            = Real.log (PXY.pmf ab) - Real.log (PX.pmf ab.1 * PY.pmf ab.2) := by
                simpa [div_eq_mul_inv] using Real.log_div (ne_of_gt hp) hxy0
        _ = Real.log (PXY.pmf ab) - (Real.log (PX.pmf ab.1) + Real.log (PY.pmf ab.2)) := by
                simp [hmul]
        _ = (Real.log (PXY.pmf ab) - Real.log (PX.pmf ab.1)) - Real.log (PY.pmf ab.2) := by ring
        _ = Real.log (PXY.pmf ab / PX.pmf ab.1) - Real.log (PY.pmf ab.2) := by simp [hdiv]
    have hsumMarg :
        (∑ ab : Signal × Outcome, PXY.pmf ab * Real.log (PY.pmf ab.2))
          = ∑ y : Outcome, PY.pmf y * Real.log (PY.pmf y) := by
      calc
        (∑ ab : Signal × Outcome, PXY.pmf ab * Real.log (PY.pmf ab.2))
            = ∑ y : Outcome, ∑ s : Signal, PXY.pmf (s, y) * Real.log (PY.pmf y) := by
                simpa using
                  (Fintype.sum_prod_type_right (fun ab : Signal × Outcome =>
                    PXY.pmf ab * Real.log (PY.pmf ab.2)))
        _ = ∑ y : Outcome, (∑ s : Signal, PXY.pmf (s, y)) * Real.log (PY.pmf y) := by
                simp [Finset.sum_mul]
        _ = ∑ y : Outcome, PY.pmf y * Real.log (PY.pmf y) := by rfl
    calc
      (∑ ab : Signal × Outcome, PXY.pmf ab * Real.log (PXY.pmf ab / PX.pmf ab.1))
          - (∑ y : Outcome, PY.pmf y * Real.log (PY.pmf y))
          = (∑ ab : Signal × Outcome, PXY.pmf ab * Real.log (PXY.pmf ab / PX.pmf ab.1))
              - (∑ ab : Signal × Outcome, PXY.pmf ab * Real.log (PY.pmf ab.2)) := by
                  simp [hsumMarg]
      _ = ∑ ab : Signal × Outcome,
            (PXY.pmf ab * Real.log (PXY.pmf ab / PX.pmf ab.1) - PXY.pmf ab * Real.log (PY.pmf ab.2)) := by
            simp [Finset.sum_sub_distrib]
      _ = ∑ ab : Signal × Outcome,
            PXY.pmf ab * (Real.log (PXY.pmf ab / PX.pmf ab.1) - Real.log (PY.pmf ab.2)) := by
            refine Finset.sum_congr rfl ?_
            intro ab _
            ring
      _ = ∑ ab : Signal × Outcome, PXY.pmf ab * Real.log (PXY.pmf ab / (PX.pmf ab.1 * PY.pmf ab.2)) := by
            refine Finset.sum_congr rfl ?_
            intro ab _
            simp [hlog ab, mul_sub]
  -- Put everything together.
  have : optimalWithInfo (Signal := Signal) (Outcome := Outcome) PXY hP odds
        - optimalNoInfo (Signal := Signal) (Outcome := Outcome) PXY odds
        = (∑ ab : Signal × Outcome, PXY.pmf ab * Real.log (PXY.pmf ab / PX.pmf ab.1))
          - (∑ y : Outcome, PY.pmf y * Real.log (PY.pmf y)) := by
    -- odds terms cancel
    simp [hoptInfo, hoptNo, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  -- finish via `hMI` and `hdiff`
  calc
    optimalWithInfo (Signal := Signal) (Outcome := Outcome) PXY hP odds
        - optimalNoInfo (Signal := Signal) (Outcome := Outcome) PXY odds
        = (∑ ab : Signal × Outcome, PXY.pmf ab * Real.log (PXY.pmf ab / PX.pmf ab.1))
          - (∑ y : Outcome, PY.pmf y * Real.log (PY.pmf y)) := this
    _ = ∑ ab : Signal × Outcome, PXY.pmf ab * Real.log (PXY.pmf ab / (PX.pmf ab.1 * PY.pmf ab.2)) := hdiff
    _ = mutualInfo (α := Signal) (β := Outcome) PXY := by simp [hMI]

end SideInfo

end

end Kelly
end Economics
end HeytingLean
