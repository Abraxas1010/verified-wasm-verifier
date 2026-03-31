import HeytingLean.EpistemicCalculus.EpistemicCalculus

namespace HeytingLean.Tests.EpistemicCalculus

open HeytingLean.EpistemicCalculus
open HeytingLean.EpistemicCalculus.Examples
open HeytingLean.EpistemicCalculus.ChangeOfCalculi
open HeytingLean.EpistemicCalculus.Enrichment
open HeytingLean.EpistemicCalculus.Updating
open HeytingLean.EpistemicCalculus.Magnitude

noncomputable section

example (x : PTbi) : ChangeOfCalculi.Examples.ptbiIsoIp.map x = x := rfl

def oneObjPTbi : VEnrichedCat PTbi where
  Obj := Unit
  hom := fun _ _ => ptbiUnit
  identity := by intro _; exact le_rfl
  composition := by
    intro _ _ _
    exact le_of_eq (EpistemicCalculus.fusion_unit_left (V := PTbi) ptbiUnit)

def oneObjIP : VEnrichedCat IP :=
  changeEnrichment (ChangeOfCalculi.Examples.ptbiIsoIp.toConservative) oneObjPTbi

def boolIdNucleus : HeytingLean.Core.Heyting.Nucleus Bool where
  op := id
  extensive := by intro x; exact le_rfl
  idempotent := by intro x; rfl
  preserves_meet := by intro x y; rfl

def boolNucleusNontrivial : ∃ x y : Bool, boolIdNucleus.op x ≠ boolIdNucleus.op y :=
  ⟨false, true, by decide⟩

def boolNucleusHimpClosed : ∀ a b : Bool, boolIdNucleus.op (a ⇨ b) = (a ⇨ b) := by
  intro a b
  rfl

instance : Fact (∃ x y : Bool, boolIdNucleus.op x ≠ boolIdNucleus.op y) :=
  ⟨boolNucleusNontrivial⟩

example : EpistemicCalculus (NucleusFixedPt boolIdNucleus) :=
  nucleusEpistemicCalculus (N := boolIdNucleus)

example : Closed (NucleusFixedPt boolIdNucleus) :=
  nucleusClosed (N := boolIdNucleus) boolNucleusHimpClosed

example (pH pH' pEgH pEgH' : ℝ)
    (hH : pH ≠ 0) (hH' : pH' ≠ 0) (hEgH' : pEgH' ≠ 0) :
    updatedOdds pH pH' pEgH pEgH' = posteriorOdds pH pH' pEgH pEgH' :=
  bayesian_recovery pH pH' pEgH pEgH' hH hH' hEgH'

example :
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

example :
    ((vUpdate oddsBayesCat true oddsBayes_hid oddsBayes_hcomp).hom false true : ℝ) =
      posteriorOdds 1 2 2 1 :=
  oddsBayes_recovery_vUpdate

example (p : Fin 3 → ℝ) :
    tsallisEntropy 2 p = 1 - Finset.sum Finset.univ (fun i => (p i) ^ (2 : ℝ)) :=
  tsallis_two_eq p

end
end HeytingLean.Tests.EpistemicCalculus
