import HeytingLean.ATP.DifferentiableATP.CoreOps

/-!
# ATP.DifferentiableATP.RetractedGD

Riemannian-style (retracted) gradient updates for the differentiable ATP lane.

For the fixed-point subspace induced by `nucleusR`, this reduces to projecting
the gradient direction before applying the step.
-/

namespace HeytingLean
namespace ATP
namespace DifferentiableATP

open HeytingLean.LoF
open HeytingLean.LoF.Combinators.Differential
open HeytingLean.LoF.Combinators.Differential.Compute

def allFixed (R : Comb → Comb) (v : FSum) : Prop :=
  ∀ tc ∈ v, R tc.1 = tc.1

private theorem allFixed_nil (R : Comb → Comb) : allFixed R [] := by
  intro tc htc
  cases htc

/-- `addTerm` preserves fixed-support when the inserted term is fixed. -/
private theorem addTerm_preserves_fixed
    (R : Comb → Comb)
    (t : Comb)
    (c : Rat)
    (acc : FSum)
    (ht : R t = t)
    (hacc : allFixed R acc) :
    allFixed R (addTerm t c acc) := by
  induction acc with
  | nil =>
      intro tc htc
      by_cases hc : c = 0
      · simp [Compute.addTerm, hc] at htc
      · have hsingle : tc = (t, c) := by
          simpa [Compute.addTerm, hc] using htc
        cases hsingle
        simpa using ht
  | cons hd tl ih =>
      rcases hd with ⟨t', c'⟩
      intro tc htc
      have htl : allFixed R tl := by
        intro u hu
        exact hacc u (by simp [hu])
      have hhd : R t' = t' := hacc (t', c') (by simp)
      by_cases hEq : t' = t
      · by_cases hZero : c' + c = 0
        · simp [Compute.addTerm, hEq, hZero] at htc
          exact htl tc htc
        · simp [Compute.addTerm, hEq, hZero] at htc
          rcases htc with htc | htc
          · cases htc
            simpa using ht
          · exact htl tc htc
      · simp [Compute.addTerm, hEq] at htc
        rcases htc with htc | htc
        · cases htc
          exact hhd
        · exact ih htl tc htc

private theorem fold_addTerm_preserves_fixed
    (R : Comb → Comb)
    (v : FSum)
    (acc : FSum)
    (hacc : allFixed R acc)
    (hv : allFixed R v) :
    allFixed R (v.foldl (fun a tc => addTerm tc.1 tc.2 a) acc) := by
  induction v generalizing acc with
  | nil =>
      simpa using hacc
  | cons hd tl ih =>
      rcases hd with ⟨t, c⟩
      have hHead : R t = t := hv (t, c) (by simp)
      have hTail : allFixed R tl := by
        intro tc htc
        exact hv tc (by simp [htc])
      have hAcc' : allFixed R (addTerm t c acc) := by
        exact addTerm_preserves_fixed R t c acc hHead hacc
      simpa using ih (addTerm t c acc) hAcc' hTail

private theorem normalize_preserves_fixed
    (R : Comb → Comb)
    (v : FSum)
    (hv : allFixed R v) :
    allFixed R (normalize v) := by
  unfold Compute.normalize
  exact fold_addTerm_preserves_fixed R v [] (allFixed_nil R) hv

private theorem map_preserves_fixed
    (R : Comb → Comb)
    (r : Rat)
    (v : FSum)
    (hv : allFixed R v) :
    allFixed R (v.map (fun tc => (tc.1, r * tc.2))) := by
  intro tc htc
  rcases List.mem_map.mp htc with ⟨u, hu, huEq⟩
  cases u with
  | mk t c =>
      simp at huEq
      cases huEq
      simpa using hv (t, c) hu

private theorem neg_preserves_fixed
    (R : Comb → Comb)
    (v : FSum)
    (hv : allFixed R v) :
    allFixed R (Compute.neg v) := by
  intro tc htc
  rcases List.mem_map.mp htc with ⟨u, hu, huEq⟩
  cases u with
  | mk t c =>
      simp at huEq
      cases huEq
      simpa using hv (t, c) hu

private theorem add_preserves_fixed
    (R : Comb → Comb)
    (a b : FSum)
    (ha : allFixed R a)
    (hb : allFixed R b) :
    allFixed R (Compute.add a b) := by
  unfold Compute.add
  exact fold_addTerm_preserves_fixed R b a ha hb

private theorem smul_preserves_fixed
    (R : Comb → Comb)
    (r : Rat)
    (v : FSum)
    (hv : allFixed R v) :
    allFixed R (Compute.smul r v) := by
  unfold Compute.smul
  exact normalize_preserves_fixed R _ (map_preserves_fixed R r v hv)

private theorem sub_preserves_fixed
    (R : Comb → Comb)
    (a b : FSum)
    (ha : allFixed R a)
    (hb : allFixed R b) :
    allFixed R (Compute.sub a b) := by
  unfold Compute.sub
  exact add_preserves_fixed R a (Compute.neg b) ha (neg_preserves_fixed R b hb)

private theorem fold_projectToParams_preserves_fixed
    (R : Comb → Comb)
    (params : List Comb)
    (v : FSum)
    (acc : FSum)
    (hacc : allFixed R acc)
    (hv : allFixed R v) :
    allFixed R (v.foldl (fun a tc => if tc.1 ∈ params then addTerm tc.1 tc.2 a else a) acc) := by
  induction v generalizing acc with
  | nil =>
      simpa using hacc
  | cons hd tl ih =>
      rcases hd with ⟨t, c⟩
      have hHead : R t = t := hv (t, c) (by simp)
      have hTail : allFixed R tl := by
        intro tc htc
        exact hv tc (by simp [htc])
      by_cases hIn : t ∈ params
      · have hAcc' : allFixed R (addTerm t c acc) := by
          exact addTerm_preserves_fixed R t c acc hHead hacc
        simpa [hIn] using ih (addTerm t c acc) hAcc' hTail
      · simpa [hIn] using ih acc hacc hTail

private theorem projectToParams_preserves_fixed
    (R : Comb → Comb)
    (params : List Comb)
    (v : FSum)
    (hv : allFixed R v) :
    allFixed R (projectToParams params v) := by
  unfold Compute.projectToParams
  by_cases hParams : params = []
  · simp [hParams]
    exact hv
  · simp [hParams]
    exact fold_projectToParams_preserves_fixed R params v [] (allFixed_nil R) hv

/-- Project a gradient direction onto the `R`-fixed coordinate subspace. -/
def projectGradientToFixed (R : Comb → Comb) (grad : FSum) : FSum :=
  projectToFixedWeights R grad

private theorem projectGradientToFixed_preserves_fixed
    (R : Comb → Comb)
    (grad : FSum) :
    allFixed R (projectGradientToFixed R grad) := by
  intro tc htc
  unfold projectGradientToFixed projectToFixedWeights at htc
  have hFilter : tc ∈ grad ∧ decide (R tc.1 = tc.1) = true := by
    simpa [List.mem_filter] using htc
  have hEq : R tc.1 = tc.1 := by
    simpa using hFilter.2
  exact hEq

/-- Retracted gradient step: project gradient first, then step.
    Applies `truncRat` to prevent Rat numeral explosion in iterated GD. -/
def retractedGradientStep (config : GDConfig) (examples : List IOExample) (w : FSum) : FSum :=
  let grad := totalGrad config.params config.regularization w examples
  let projGrad := projectGradientToFixed nucleusR grad
  let truncGrad := projGrad.map (fun tc => (tc.1, truncRat tc.2))
  let stepped := (sub w (smul config.learningRate truncGrad)).map (fun tc => (tc.1, truncRat tc.2))
  projectToParams config.params stepped

private theorem mapCoeffTrunc_preserves_fixed
    (R : Comb → Comb) (f : Rat → Rat) (v : FSum) (hv : allFixed R v) :
    allFixed R (v.map (fun tc => (tc.1, f tc.2))) := by
  intro tc htc
  rcases List.mem_map.mp htc with ⟨u, hu, huEq⟩
  cases u with
  | mk t c =>
      simp at huEq
      cases huEq
      simpa using hv (t, c) hu

theorem retractedStep_preserves_fixed
    (config : GDConfig)
    (examples : List IOExample)
    (w : FSum)
    (hw : allFixed nucleusR w) :
    allFixed nucleusR (retractedGradientStep config examples w) := by
  unfold retractedGradientStep
  have hProj :
      allFixed nucleusR
        (projectGradientToFixed nucleusR (totalGrad config.params config.regularization w examples)) := by
    exact projectGradientToFixed_preserves_fixed nucleusR _
  have hTruncGrad :
      allFixed nucleusR
        ((projectGradientToFixed nucleusR (totalGrad config.params config.regularization w examples)).map
          (fun tc => (tc.1, truncRat tc.2))) := by
    exact mapCoeffTrunc_preserves_fixed nucleusR truncRat _ hProj
  have hSmul :
      allFixed nucleusR
        (smul config.learningRate
          ((projectGradientToFixed nucleusR (totalGrad config.params config.regularization w examples)).map
            (fun tc => (tc.1, truncRat tc.2)))) := by
    exact smul_preserves_fixed nucleusR config.learningRate _ hTruncGrad
  have hSub :
      allFixed nucleusR
        (sub w
          (smul config.learningRate
            ((projectGradientToFixed nucleusR (totalGrad config.params config.regularization w examples)).map
              (fun tc => (tc.1, truncRat tc.2))))) := by
    exact sub_preserves_fixed nucleusR _ _ hw hSmul
  have hTruncStep :
      allFixed nucleusR
        ((sub w
          (smul config.learningRate
            ((projectGradientToFixed nucleusR (totalGrad config.params config.regularization w examples)).map
              (fun tc => (tc.1, truncRat tc.2))))).map
          (fun tc => (tc.1, truncRat tc.2))) := by
    exact mapCoeffTrunc_preserves_fixed nucleusR truncRat _ hSub
  exact projectToParams_preserves_fixed nucleusR config.params _ hTruncStep

end DifferentiableATP
end ATP
end HeytingLean
