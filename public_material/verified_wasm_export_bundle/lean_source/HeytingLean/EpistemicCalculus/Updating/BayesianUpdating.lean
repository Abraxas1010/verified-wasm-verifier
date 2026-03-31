import HeytingLean.EpistemicCalculus.Updating.VUpdating
import HeytingLean.EpistemicCalculus.Examples.CertaintyFactors
import Mathlib.Tactic.FieldSimp

namespace HeytingLean.EpistemicCalculus.Updating

open HeytingLean.EpistemicCalculus.Enrichment
open HeytingLean.EpistemicCalculus.Examples

noncomputable section

/-- Likelihood ratios reuse the certainty-factor carrier and instances. -/
abbrev LikelihoodRatio := CF

abbrev lrOne : LikelihoodRatio := cfOne
abbrev lrTwo : LikelihoodRatio := cfTwo

theorem likelihood_ratio_nontrivial :
    ∃ x y : LikelihoodRatio, x ≠ y := by
  exact EpistemicCalculus.nontrivial (V := LikelihoodRatio)

/-- Value-level form of `ihom` for certainty-factor / likelihood-ratio carrier. -/
@[simp] theorem likelihoodRatio_ihom_val (a b : LikelihoodRatio) :
    ((Closed.ihom a b : LikelihoodRatio) : ℝ) = (b : ℝ) / (a : ℝ) := rfl

/-- Telescoping identity used in odds-form Bayesian updates. -/
theorem likelihood_telescope (pH pH' pE : ℝ)
    (hH : pH ≠ 0) (hH' : pH' ≠ 0) :
    (pH' / pH) * (pE / pH') = pE / pH := by
  field_simp [hH, hH']

def priorOdds (pH pH' : ℝ) : ℝ := pH' / pH

def updatedOdds (pH pH' pEgH pEgH' : ℝ) : ℝ :=
  pEgH / (priorOdds pH pH' * pEgH')

def posteriorOdds (pH pH' pEgH pEgH' : ℝ) : ℝ :=
  (pEgH * pH) / (pEgH' * pH')

/--
Bayesian recovery in odds form:
the `vUpdate`-style ratio expression equals posterior odds after algebraic
normalization.
-/
theorem bayesian_recovery (pH pH' pEgH pEgH' : ℝ)
    (hH : pH ≠ 0) (hH' : pH' ≠ 0) (hEgH' : pEgH' ≠ 0) :
    updatedOdds pH pH' pEgH pEgH' = posteriorOdds pH pH' pEgH pEgH' := by
  unfold updatedOdds priorOdds posteriorOdds
  field_simp [hH, hH', hEgH']

/--
Categorical bridge: if three distinguished hom-values are identified with
Bayesian prior/likelihood components, the `vUpdate` hom-value is exactly the
odds-form Bayesian update term.
-/
theorem vUpdate_hom_eq_updatedOdds
    (H : VEnrichedCat LikelihoodRatio) (x y E : H.Obj)
    (hid : ∀ u : H.Obj, H.hom u u fus H.hom u E ≤ H.hom u E)
    (hcomp :
      ∀ u v w : H.Obj,
        Closed.ihom (H.hom v w fus H.hom w E) (H.hom v E) fus
            Closed.ihom (H.hom u v fus H.hom v E) (H.hom u E) ≤
          Closed.ihom (H.hom u w fus H.hom w E) (H.hom u E))
    (pH pH' pEgH pEgH' : ℝ)
    (hxy : (H.hom x y : ℝ) = priorOdds pH pH')
    (hyE : (H.hom y E : ℝ) = pEgH')
    (hxE : (H.hom x E : ℝ) = pEgH) :
    ((vUpdate H E hid hcomp).hom x y : ℝ) = updatedOdds pH pH' pEgH pEgH' := by
  calc
    ((vUpdate H E hid hcomp).hom x y : ℝ)
        = (H.hom x E : ℝ) / ((H.hom x y : ℝ) * (H.hom y E : ℝ)) := by
            have hfus :
                ((H.hom x y fus H.hom y E : LikelihoodRatio) : ℝ) =
                  (H.hom x y : ℝ) * (H.hom y E : ℝ) := by
              rfl
            simpa [vUpdate_hom] using
              congrArg (fun t : ℝ => (H.hom x E : ℝ) / t) hfus
    _ = updatedOdds pH pH' pEgH pEgH' := by
          simp [updatedOdds, priorOdds, hxy, hyE, hxE]

/--
`vUpdate` recovers posterior odds once the odds-form identity is normalized.
-/
theorem vUpdate_hom_eq_posteriorOdds
    (H : VEnrichedCat LikelihoodRatio) (x y E : H.Obj)
    (hid : ∀ u : H.Obj, H.hom u u fus H.hom u E ≤ H.hom u E)
    (hcomp :
      ∀ u v w : H.Obj,
        Closed.ihom (H.hom v w fus H.hom w E) (H.hom v E) fus
            Closed.ihom (H.hom u v fus H.hom v E) (H.hom u E) ≤
          Closed.ihom (H.hom u w fus H.hom w E) (H.hom u E))
    (pH pH' pEgH pEgH' : ℝ)
    (hH : pH ≠ 0) (hH' : pH' ≠ 0) (hEgH' : pEgH' ≠ 0)
    (hxy : (H.hom x y : ℝ) = priorOdds pH pH')
    (hyE : (H.hom y E : ℝ) = pEgH')
    (hxE : (H.hom x E : ℝ) = pEgH) :
    ((vUpdate H E hid hcomp).hom x y : ℝ) = posteriorOdds pH pH' pEgH pEgH' := by
  calc
    ((vUpdate H E hid hcomp).hom x y : ℝ)
        = updatedOdds pH pH' pEgH pEgH' :=
          vUpdate_hom_eq_updatedOdds H x y E hid hcomp pH pH' pEgH pEgH' hxy hyE hxE
    _ = posteriorOdds pH pH' pEgH pEgH' := bayesian_recovery pH pH' pEgH pEgH' hH hH' hEgH'

/-- Two-object ratio-enriched category used as a concrete Bayesian scenario. -/
def oddsWeight : Bool → ℝ
  | false => 1
  | true => 2

theorem oddsWeight_pos (b : Bool) : 0 < oddsWeight b := by
  cases b <;> norm_num [oddsWeight]

def oddsHom (x y : Bool) : LikelihoodRatio :=
  ⟨oddsWeight y / oddsWeight x, div_pos (oddsWeight_pos y) (oddsWeight_pos x)⟩

def oddsBayesCat : VEnrichedCat LikelihoodRatio where
  Obj := Bool
  hom := oddsHom
  identity := by
    intro x
    change (1 : ℝ) ≤ oddsWeight x / oddsWeight x
    have hx : oddsWeight x ≠ 0 := ne_of_gt (oddsWeight_pos x)
    field_simp [hx]
    exact le_rfl
  composition := by
    intro x y z
    change (oddsWeight z / oddsWeight y) * (oddsWeight y / oddsWeight x) ≤ oddsWeight z / oddsWeight x
    have hx : oddsWeight x ≠ 0 := ne_of_gt (oddsWeight_pos x)
    have hy : oddsWeight y ≠ 0 := ne_of_gt (oddsWeight_pos y)
    field_simp [hx, hy]
    exact le_rfl

theorem oddsBayes_hid :
    ∀ u : oddsBayesCat.Obj, oddsBayesCat.hom u u fus oddsBayesCat.hom u true ≤ oddsBayesCat.hom u true := by
  intro u
  change (oddsWeight u / oddsWeight u) * (oddsWeight true / oddsWeight u) ≤ oddsWeight true / oddsWeight u
  have hu : oddsWeight u ≠ 0 := ne_of_gt (oddsWeight_pos u)
  field_simp [hu]
  exact le_rfl

/-- Composition in `oddsBayesCat` is pointwise ratio telescoping. -/
theorem oddsBayes_hom_comp (x y z : oddsBayesCat.Obj) :
    oddsBayesCat.hom x y fus oddsBayesCat.hom y z = oddsBayesCat.hom x z := by
  apply Subtype.ext
  change (oddsWeight y / oddsWeight x) * (oddsWeight z / oddsWeight y) = oddsWeight z / oddsWeight x
  have hx : oddsWeight x ≠ 0 := ne_of_gt (oddsWeight_pos x)
  have hy : oddsWeight y ≠ 0 := ne_of_gt (oddsWeight_pos y)
  field_simp [hx, hy]

/-- Internal hom collapses to unit when source and target coincide. -/
theorem oddsBayes_ihom_self (x y : oddsBayesCat.Obj) :
    Closed.ihom (oddsBayesCat.hom x y) (oddsBayesCat.hom x y) = cfOne := by
  apply Subtype.ext
  change (oddsWeight y / oddsWeight x) / (oddsWeight y / oddsWeight x) = 1
  have hx : oddsWeight x ≠ 0 := ne_of_gt (oddsWeight_pos x)
  have hy : oddsWeight y ≠ 0 := ne_of_gt (oddsWeight_pos y)
  field_simp [hx, hy]

/-- Composition coherence for the concrete two-object odds scenario. -/
theorem oddsBayes_hcomp :
    ∀ u v w : oddsBayesCat.Obj,
      Closed.ihom (oddsBayesCat.hom v w fus oddsBayesCat.hom w true) (oddsBayesCat.hom v true) fus
          Closed.ihom (oddsBayesCat.hom u v fus oddsBayesCat.hom v true) (oddsBayesCat.hom u true) ≤
        Closed.ihom (oddsBayesCat.hom u w fus oddsBayesCat.hom w true) (oddsBayesCat.hom u true) := by
  intro u v w
  simp [oddsBayes_hom_comp, oddsBayes_ihom_self, cfOne]
  change cfFusion cfOne cfOne ≤ cfOne
  change ((1 : ℝ) * 1 ≤ 1)
  norm_num

/--
Concrete bridge witness:
for the two-object odds category, `vUpdate` at evidence `true` matches posterior
odds exactly.
-/
theorem oddsBayes_recovery_vUpdate :
    ((vUpdate oddsBayesCat true oddsBayes_hid oddsBayes_hcomp).hom false true : ℝ) =
      posteriorOdds 1 2 2 1 := by
  have hH : (1 : ℝ) ≠ 0 := by norm_num
  have hH' : (2 : ℝ) ≠ 0 := by norm_num
  have hEgH' : (1 : ℝ) ≠ 0 := by norm_num
  have hxy : (oddsBayesCat.hom false true : ℝ) = priorOdds 1 2 := by
    simp [oddsBayesCat, oddsHom, oddsWeight, priorOdds]
  have hyE : (oddsBayesCat.hom true true : ℝ) = (1 : ℝ) := by
    simp [oddsBayesCat, oddsHom, oddsWeight]
  have hxE : (oddsBayesCat.hom false true : ℝ) = (2 : ℝ) := by
    simp [oddsBayesCat, oddsHom, oddsWeight]
  simpa using
    vUpdate_hom_eq_posteriorOdds
      oddsBayesCat false true true oddsBayes_hid oddsBayes_hcomp
      1 2 2 1 hH hH' hEgH' hxy hyE hxE

/-- Runtime-shaped Bayesian evidence item in false-over-true odds orientation. -/
structure EvidenceLikelihood where
  likelihoodGivenTrue : ℝ
  likelihoodGivenFalse : ℝ

/-- Single-step multiplicative update factor for one evidence item. -/
def EvidenceLikelihood.factor (e : EvidenceLikelihood) : ℝ :=
  e.likelihoodGivenFalse / e.likelihoodGivenTrue

/-- Iterated odds update matching `combine_evidence()` in the runtime. -/
def vUpdateChainOdds (priorOddsFalseOverTrue : ℝ) (evidence : List EvidenceLikelihood) : ℝ :=
  evidence.foldl (fun odds e => odds * e.factor) priorOddsFalseOverTrue

/-- Closed form of the odds chain: prior times the product of all likelihood factors. -/
theorem vUpdate_chain_telescopes
    (priorOddsFalseOverTrue : ℝ) (evidence : List EvidenceLikelihood) :
    vUpdateChainOdds priorOddsFalseOverTrue evidence =
      priorOddsFalseOverTrue * (evidence.map EvidenceLikelihood.factor).prod := by
  induction evidence generalizing priorOddsFalseOverTrue with
  | nil =>
      simp [vUpdateChainOdds]
  | cons head tail ih =>
      simpa [vUpdateChainOdds, mul_assoc, mul_left_comm, mul_comm] using
        ih (priorOddsFalseOverTrue * head.factor)

/-- The order of evidence does not matter: only the product of factors matters. -/
theorem vUpdate_chain_comm
    (priorOddsFalseOverTrue : ℝ)
    {left right : List EvidenceLikelihood}
    (hperm : List.Perm left right) :
    vUpdateChainOdds priorOddsFalseOverTrue left =
      vUpdateChainOdds priorOddsFalseOverTrue right := by
  have hmap : List.Perm (left.map EvidenceLikelihood.factor) (right.map EvidenceLikelihood.factor) :=
    hperm.map _
  calc
    vUpdateChainOdds priorOddsFalseOverTrue left =
        priorOddsFalseOverTrue * (left.map EvidenceLikelihood.factor).prod :=
          vUpdate_chain_telescopes priorOddsFalseOverTrue left
    _ = priorOddsFalseOverTrue * (right.map EvidenceLikelihood.factor).prod := by
          simp [hmap.prod_eq]
    _ = vUpdateChainOdds priorOddsFalseOverTrue right := by
          symm
          exact vUpdate_chain_telescopes priorOddsFalseOverTrue right

/-- Positive prior odds stay positive under positive likelihoods. -/
theorem vUpdate_chain_positive
    (priorOddsFalseOverTrue : ℝ)
    (evidence : List EvidenceLikelihood)
    (hPrior : 0 < priorOddsFalseOverTrue)
    (hEvidence :
      ∀ e ∈ evidence, 0 < e.likelihoodGivenTrue ∧ 0 < e.likelihoodGivenFalse) :
    0 < vUpdateChainOdds priorOddsFalseOverTrue evidence := by
  rw [vUpdate_chain_telescopes]
  refine mul_pos hPrior ?_
  induction evidence with
  | nil =>
      simp
  | cons head tail ih =>
      have hHead : 0 < head.factor := by
        have h := hEvidence head (by simp)
        exact div_pos h.2 h.1
      have hTail :
          ∀ e ∈ tail, 0 < e.likelihoodGivenTrue ∧ 0 < e.likelihoodGivenFalse := by
        intro e he
        exact hEvidence e (by simp [he])
      simpa [EvidenceLikelihood.factor] using mul_pos hHead (ih hTail)

end
end HeytingLean.EpistemicCalculus.Updating
