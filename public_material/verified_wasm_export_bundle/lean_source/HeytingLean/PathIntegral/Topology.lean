import HeytingLean.PathIntegral.Measure
import HeytingLean.PerspectivalPlenum.CechObstruction
import HeytingLean.PerspectivalPlenum.CechCohomology

/-!
# PathIntegral.Topology

Discrete topology over proof paths with a Čech obstruction bridge.
-/

namespace HeytingLean
namespace PathIntegral

open HeytingLean.Embeddings
open HeytingLean.LoF.Combinators.Differential.Compute

def ProofPath.transportSupport (p : ProofPath) : List (LensID × LensID) :=
  p.steps.filterMap ProofStep.lensTransition

def differByOneStep (p q : ProofPath) : Prop :=
  p.start = q.start ∧
    p.finish = q.finish ∧
    p.transportSupport = q.transportSupport ∧
    (p.length + 1 = q.length ∨ q.length + 1 = p.length)

def ProofPath.homotopic (p q : ProofPath) : Prop :=
  p.start = q.start ∧
    p.finish = q.finish ∧
    p.transportSupport = q.transportSupport

instance ProofPath.homotopicSetoid : Setoid ProofPath where
  r := ProofPath.homotopic
  iseqv := by
    constructor
    · intro p
      exact ⟨rfl, rfl, rfl⟩
    · intro p q h
      exact ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩
    · intro p q r hpq hqr
      exact ⟨hpq.1.trans hqr.1, hpq.2.1.trans hqr.2.1, hpq.2.2.trans hqr.2.2⟩

def ProofGroupoid := Quotient ProofPath.homotopicSetoid

def ProofPath.loopLike (p : ProofPath) : Bool :=
  p.start = p.finish

def ProofPath.usesMultipleLenses (p : ProofPath) : Bool :=
  (p.lensSet.eraseDups.length > 1)

def detectTopologyHeuristic (paths : List ProofPath) : Bool :=
  paths.any (fun p => p.loopLike && p.usesMultipleLenses)

private def witnessGoal : FSum := [(.K, 1)]

private def witnessState (lens : LensID) (depth : Nat) (history : List LensID) : ProofState :=
  {
    lens := lens
    goal := witnessGoal
    context := "witness"
    depth := depth
    history := history
  }

private def stationaryState : ProofState :=
  witnessState .omega 0 []

private def remoteState : ProofState :=
  witnessState .region 1 [.region, .omega]

private def enterRemote : ProofStep :=
  {
    source := stationaryState
    target := remoteState
    tactic := "transport:region"
    lensTransition := some (.omega, .region)
  }

private def returnHome : ProofStep :=
  {
    source := remoteState
    target := stationaryState
    tactic := "transport:omega"
    lensTransition := some (.region, .omega)
  }

def canonicalStationaryLoop : ProofPath :=
  ProofPath.id stationaryState

def canonicalObstructedLoop : ProofPath :=
  ProofPath.comp (ProofPath.singleton enterRemote) (ProofPath.singleton returnHome)

def obstructionClass (loop : ProofPath) :
    HeytingLean.PerspectivalPlenum.ContextualityEngine.CechObstructionClass :=
  if loop.loopLike && loop.usesMultipleLenses then
    HeytingLean.PerspectivalPlenum.ContextualityEngine.triangleObstructionClass
  else
    .none

def h1Witness? (loop : ProofPath) :
    Option
      (HeytingLean.PerspectivalPlenum.LensSheaf.Cech.True.H1Class
        HeytingLean.PerspectivalPlenum.LensSheaf.Cech.True.Triangle.skeleton) :=
  if loop.loopLike && loop.usesMultipleLenses then
    some HeytingLean.PerspectivalPlenum.LensSheaf.Cech.True.Triangle.parityClass
  else
    none

theorem differByOneStep_implies_homotopic (p q : ProofPath)
    (h : differByOneStep p q) :
    ProofPath.homotopic p q := by
  exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem homotopic_same_transportSupport (p q : ProofPath)
    (h : ProofPath.homotopic p q) :
    p.transportSupport = q.transportSupport := h.2.2

private theorem filterMap_lensTransition_eq_nil_of_all_none :
    ∀ steps : List ProofStep,
      (∀ s ∈ steps, s.lensTransition = none) →
      steps.filterMap ProofStep.lensTransition = []
  | [], _ => by simp
  | step :: rest, h => by
      have hstep : step.lensTransition = none := h step (by simp)
      have hrest : ∀ s ∈ rest, s.lensTransition = none := by
        intro s hs
        exact h s (by simp [hs])
      simp [hstep, filterMap_lensTransition_eq_nil_of_all_none rest hrest]

theorem transportSupport_nil_of_transport_free (p : ProofPath)
    (hfree : ∀ s ∈ p.steps, s.lensTransition = none) :
    p.transportSupport = [] := by
  unfold ProofPath.transportSupport
  exact filterMap_lensTransition_eq_nil_of_all_none p.steps hfree

theorem obstructionClass_of_multilens_loop (loop : ProofPath)
    (h : loop.loopLike = true ∧ loop.usesMultipleLenses = true) :
    obstructionClass loop =
      HeytingLean.PerspectivalPlenum.ContextualityEngine.CechObstructionClass.h1_global_section := by
  unfold obstructionClass
  simp [h.1, h.2, HeytingLean.PerspectivalPlenum.ContextualityEngine.triangleObstructionClass]

theorem h1Witness_exists_of_multilens_loop (loop : ProofPath)
    (h : loop.loopLike = true ∧ loop.usesMultipleLenses = true) :
    ∃ w, h1Witness? loop = some w := by
  refine ⟨HeytingLean.PerspectivalPlenum.LensSheaf.Cech.True.Triangle.parityClass, ?_⟩
  unfold h1Witness?
  simp [h.1, h.2]

theorem nontrivial_H1_implies_inequivalent
    (_h1 : HeytingLean.PerspectivalPlenum.LensSheaf.Cech.True.H1Class
      HeytingLean.PerspectivalPlenum.LensSheaf.Cech.True.Triangle.skeleton) :
    ∃ (p q : ProofPath),
      obstructionClass q =
        HeytingLean.PerspectivalPlenum.ContextualityEngine.CechObstructionClass.h1_global_section ∧
      obstructionClass p =
        HeytingLean.PerspectivalPlenum.ContextualityEngine.CechObstructionClass.none ∧
      ¬ ProofPath.homotopic p q := by
  refine ⟨canonicalStationaryLoop, canonicalObstructedLoop, ?_, ?_, ?_⟩
  · unfold canonicalObstructedLoop
    apply obstructionClass_of_multilens_loop
    decide
  · native_decide
  · intro hhom
    have hnil :
        enterRemote.lensTransition = none ∧ returnHome.lensTransition = none := by
      simpa [canonicalStationaryLoop, canonicalObstructedLoop, ProofPath.transportSupport,
        ProofPath.id, ProofPath.comp, ProofPath.singleton] using hhom.2.2
    simp [enterRemote, returnHome] at hnil

theorem single_lens_all_homotopic
    (paths : List ProofPath)
    (h : ∀ p ∈ paths, ∀ s ∈ p.steps, s.lensTransition = none) :
    ∀ p ∈ paths, ∀ q ∈ paths, p.start = q.start → p.finish = q.finish → ProofPath.homotopic p q := by
  intro p hp q hq hstart hfinish
  refine ⟨hstart, hfinish, ?_⟩
  rw [transportSupport_nil_of_transport_free p (h p hp), transportSupport_nil_of_transport_free q (h q hq)]

theorem same_transport_support_homotopic
    (p q : ProofPath)
    (hstart : p.start = q.start)
    (hfinish : p.finish = q.finish)
    (hsupport : p.transportSupport = q.transportSupport) :
    ProofPath.homotopic p q := by
  exact ⟨hstart, hfinish, hsupport⟩

end PathIntegral
end HeytingLean
