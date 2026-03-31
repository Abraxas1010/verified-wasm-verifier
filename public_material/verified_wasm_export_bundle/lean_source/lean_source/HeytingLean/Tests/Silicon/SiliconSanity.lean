import HeytingLean.Silicon

namespace HeytingLean.Tests.Silicon

open HeytingLean

open HeytingLean.Probability.InfoTheory

noncomputable section

example :
    Silicon.Leakage (S := Bool) (O := Bool) (FinDist.prod Silicon.Examples.unifBool Silicon.Examples.unifBool) = 0 := by
  classical
  refine Silicon.leakage_eq_zero_of_independent (S := Bool) (O := Bool)
    (P := FinDist.prod Silicon.Examples.unifBool Silicon.Examples.unifBool) ?_
  exact ⟨Silicon.Examples.unifBool, Silicon.Examples.unifBool, rfl⟩

example :
    ∃ a : Bool,
      FinDist.probEvent Silicon.Examples.unifBool (fun x : Bool => x = a)
        ≠ FinDist.probEvent Silicon.Examples.deltaTrue (fun x : Bool => x = a) := by
  classical
  have h : Silicon.Examples.unifBool ≠ Silicon.Examples.deltaTrue := by
    intro hEq
    have hpmf : (1 / 2 : ℝ) = (1 : ℝ) := by
      have hpmf' :
          Silicon.Examples.unifBool.pmf true = Silicon.Examples.deltaTrue.pmf true := by
        simp [hEq]
      simp [Silicon.Examples.unifBool, Silicon.Examples.deltaTrue] at hpmf'
    have hne : (1 / 2 : ℝ) ≠ (1 : ℝ) := by norm_num
    exact hne hpmf
  exact Silicon.Signature.exists_singleton_prob_ne (α := Bool)
    (P := Silicon.Examples.unifBool) (Q := Silicon.Examples.deltaTrue) h

/-- Delta distribution on `Bool`. -/
def deltaBool (b0 : Bool) : FinDist Bool where
  pmf b := if b = b0 then (1 : ℝ) else 0
  nonneg := by
    intro b
    by_cases h : b = b0 <;> simp [h]
  sum_one := by
    classical
    cases b0 <;> simp

def idChannel : Silicon.Channel Bool Bool :=
  fun b => deltaBool b

def corrBool : Silicon.Run Bool Bool :=
  Silicon.Channel.joint Silicon.Examples.unifBool idChannel

example : (Silicon.Empirical.uniform Bool).pmf true = (1 / 2 : ℝ) := by
  simp [Silicon.Empirical.uniform, Fintype.card_bool]

lemma obsMixture_idChannel :
    Silicon.Channel.obsMixture (S := Bool) (O := Bool) Silicon.Examples.unifBool idChannel =
      Silicon.Examples.unifBool := by
  classical
  ext b
  cases b <;> simp [Silicon.Channel.obsMixture, idChannel, deltaBool, Silicon.Examples.unifBool]

lemma corrBool_accuracy :
    Silicon.Predictability.accuracy (X := Bool) (Y := Bool) corrBool (fun b => b) = 1 := by
  classical
  unfold corrBool idChannel
  unfold Silicon.Predictability.accuracy
  rw [FinDist.probEvent_eq_sum]
  have hpoint :
      (∑ bb : Bool × Bool,
          if (fun xy : Bool × Bool => xy.1 = xy.2) bb then
              (Silicon.Channel.joint Silicon.Examples.unifBool (fun b => deltaBool b)).pmf bb
            else 0) =
        ∑ bb : Bool × Bool, (Silicon.Channel.joint Silicon.Examples.unifBool (fun b => deltaBool b)).pmf bb := by
    classical
    refine Finset.sum_congr rfl ?_
    intro bb _
    by_cases h : bb.1 = bb.2
    · simp [h]
    · cases bb with
      | mk b₁ b₂ =>
        have h' : ¬b₂ = b₁ := by
          intro hb
          exact h hb.symm
        simp [Silicon.Channel.joint, deltaBool, Silicon.Examples.unifBool, h, h']
  simpa [hpoint] using (Silicon.Channel.joint Silicon.Examples.unifBool (fun b => deltaBool b)).sum_one

lemma corrBool_baseline :
    Silicon.Predictability.baseline (X := Bool) (Y := Bool) corrBool = (1 / 2 : ℝ) := by
  classical
  have hObs :
      Silicon.Run.obsMarginal (S := Bool) (O := Bool) corrBool = Silicon.Examples.unifBool := by
    have h := Silicon.Channel.obsMarginal_joint (S := Bool) (O := Bool)
      (PS := Silicon.Examples.unifBool) (K := idChannel)
    simpa [corrBool, obsMixture_idChannel] using h
  have hMax : Silicon.Predictability.maxMass (Y := Bool) Silicon.Examples.unifBool = (1 / 2 : ℝ) := by
    simp [Silicon.Predictability.maxMass, Silicon.Examples.unifBool]
  simp [Silicon.Predictability.baseline, hObs, hMax]

example :
    ¬ Silicon.Independent (S := Bool) (O := Bool) corrBool := by
  classical
  -- Use: accuracy > baseline ⇒ not independent.
  refine Silicon.Predictability.not_independent_of_accuracy_gt_baseline (X := Bool) (Y := Bool)
    (P := corrBool) (g := fun b => b) ?_
  have hB := corrBool_baseline
  have hA := corrBool_accuracy
  simpa [hB, hA] using (by norm_num : (1 / 2 : ℝ) < 1)

example : (1 - (5 : ℝ) / (64 : ℝ)) = (59 : ℝ) / (64 : ℝ) := by
  norm_num

end

end HeytingLean.Tests.Silicon
