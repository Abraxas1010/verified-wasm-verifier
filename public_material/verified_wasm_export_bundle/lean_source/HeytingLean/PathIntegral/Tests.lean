import HeytingLean.PathIntegral.Action
import HeytingLean.PathIntegral.Measure
import HeytingLean.PathIntegral.AnnealingTheory
import HeytingLean.PathIntegral.Adapter
import HeytingLean.PathIntegral.GroupoidBridge

/-!
# PathIntegral.Tests

Small sanity tests for the path-integral ATP stack.
-/

namespace HeytingLean
namespace PathIntegral
namespace Tests

open HeytingLean.Embeddings
open HeytingLean.LoF
open HeytingLean.LoF.Combinators.Differential.Compute

def baseGoal : FSum := [(.K, 1)]
def reducedGoal : FSum := []

def s0 : ProofState := {
  lens := .omega
  goal := baseGoal
  context := "goal"
  depth := 0
  history := []
}

def s1 : ProofState := {
  lens := .omega
  goal := reducedGoal
  context := "goal"
  depth := 1
  history := [.omega]
}

def localStep : ProofStep := {
  source := s0
  target := s1
  tactic := "simp"
}

def stayStep : ProofStep := {
  source := s0
  target := s0
  tactic := "id"
}

def loopState : ProofState := {
  lens := .region
  goal := baseGoal
  context := "loop"
  depth := 1
  history := [.region]
}

def transportStep : ProofStep := {
  source := s1
  target := { loopState with lens := .region, depth := 2, history := [.region, .omega] }
  tactic := "transport:region"
  lensTransition := some (.omega, .region)
}

def matulaState : ProofState := {
  lens := .matula
  goal := reducedGoal
  context := "move"
  depth := 2
  history := [.matula, .omega]
}

def regionActionStep : ProofStep := {
  source := s1
  target := { loopState with goal := reducedGoal, context := "move", depth := 2, history := [.region, .omega] }
  tactic := "move"
  lensTransition := some (.omega, .region)
}

def matulaActionStep : ProofStep := {
  source := s1
  target := matulaState
  tactic := "move"
  lensTransition := some (.omega, .matula)
}

def returnStep : ProofStep := {
  source := transportStep.target
  target := s0
  tactic := "transport:omega"
  lensTransition := some (.region, .omega)
}

def p0 : ProofPath := ProofPath.id s0
def p1 : ProofPath := ProofPath.singleton localStep
def pStay : ProofPath := ProofPath.singleton stayStep
def loopPath : ProofPath := ProofPath.comp (ProofPath.singleton localStep)
  (ProofPath.comp (ProofPath.singleton transportStep) (ProofPath.singleton returnStep))

def testConstructors (state : ProofState) : List (TacticId × FSum) :=
  if state.goal = [] then
    []
  else
    [("simp", []), ("normalize", state.goal)]

def goalClosed (s : ProofState) : Bool :=
  s.goal = []

def testTransport := HeytingLean.ATP.DifferentiableATP.sheafTransport

example : p1.valid := ProofPath.singleton_valid localStep

example : pathAction p0 = 0 := by
  simpa [p0] using action_id s0

example : pathWeight 0 p1 = 1 := by
  simpa [p1] using beta_limit_uniform p1

example : transportProfileRat .omega .region = 2 := by
  simpa using actionTransportProbe_region_profile

example : transportProfileRat .omega .matula = 5 := by
  simpa using actionTransportProbe_matula_profile

example : 0 < actionGap ({p0, p1} : Finset ProofPath) p0 := by
  apply actionGap_pos
  · simp [p0]
  · intro q hq hneq
    simp at hq
    rcases hq with rfl | rfl
    · contradiction
    · have hp0 : pathAction p0 = 0 := by
        simpa [p0] using action_id s0
      rw [hp0]
      exact Rat.cast_pos.mpr (by native_decide : 0 < pathActionRat p1)
  · native_decide

example : AnnealingSchedule.betaAt (.linear 0.5) 1.0 2 > 1.9 := by
  native_decide

example : AnnealingSchedule.betaAt (.linear 0.5) 1.0 2 < 2.1 := by
  native_decide

example : AnnealingSchedule.betaAt (.geometric 2.0) 1.0 3 > 7.9 := by
  native_decide

example : AnnealingSchedule.betaAt (.geometric 2.0) 1.0 3 < 8.1 := by
  native_decide

example :
    AnnealingSchedule.betaAt (.logarithmic 2.0) 1.0 2 > 2.7 := by
  native_decide

example :
    AnnealingSchedule.betaAt (.logarithmic 2.0) 1.0 2 < 2.8 := by
  native_decide

example : transportProfileRat .omega .region ≠ transportProfileRat .omega .matula := by
  rw [actionTransportProbe_region_profile, actionTransportProbe_matula_profile]
  norm_num

example : measureTransportProbeNorm = 6 := by
  exact measureTransportProbeNorm_eq

example : lensTransitionFactorRat .omega .omega = 1 := by
  simp [lensTransitionFactorRat]

example : lensTransitionFactorRat .omega .region = (5 : Rat) / 3 := by
  native_decide

example : lensTransitionFactorRat .omega .matula = (7 : Rat) / 6 := by
  native_decide

example : lensTransitionFactorRat .omega .region ≠ lensTransitionFactorRat .omega .matula := by
  exact lensTransitionFactor_asymmetry_witness

example : lensTransitionFactorRat .omega .region > lensTransitionFactorRat .omega .matula := by
  native_decide

example : lensTransitionFactorFloat .omega .region > lensTransitionFactorFloat .omega .matula := by
  native_decide

example : transportCostRat regionActionStep.signature = 3 := by
  have hsafe : HeytingLean.ATP.LensTransport.isSafeTransport .omega .region = true := by
    native_decide
  simp [transportCostRat, ProofStep.signature, regionActionStep, s1, loopState,
    actionTransportProbe_region_profile, hsafe]
  norm_num

example : transportCostRat matulaActionStep.signature = 6 := by
  have hsafe : HeytingLean.ATP.LensTransport.isSafeTransport .omega .matula = true := by
    native_decide
  simp [transportCostRat, ProofStep.signature, matulaActionStep, matulaState, s1,
    actionTransportProbe_matula_profile, hsafe]
  norm_num

example : stepActionRat regionActionStep = (9 : Rat) / 2 := by
  have hcost : transportCostRat regionActionStep.signature = 3 := by
    have hsafe : HeytingLean.ATP.LensTransport.isSafeTransport .omega .region = true := by
      native_decide
    simp [transportCostRat, ProofStep.signature, regionActionStep, s1, loopState,
      actionTransportProbe_region_profile, hsafe]
    norm_num
  have hnat : operationNaturalnessRat regionActionStep.signature = 1 := by
    native_decide
  have hcompress : informationCompressionRat regionActionStep.signature = (1 : Rat) / 2 := by
    native_decide
  simp [stepActionRat, stepActionFromSignatureRat, hcost, hnat, hcompress]
  norm_num

example : stepActionRat matulaActionStep = (15 : Rat) / 2 := by
  have hcost : transportCostRat matulaActionStep.signature = 6 := by
    have hsafe : HeytingLean.ATP.LensTransport.isSafeTransport .omega .matula = true := by
      native_decide
    simp [transportCostRat, ProofStep.signature, matulaActionStep, matulaState, s1,
      actionTransportProbe_matula_profile, hsafe]
    norm_num
  have hnat : operationNaturalnessRat matulaActionStep.signature = 1 := by
    native_decide
  have hcompress : informationCompressionRat matulaActionStep.signature = (1 : Rat) / 2 := by
    native_decide
  simp [stepActionRat, stepActionFromSignatureRat, hcost, hnat, hcompress]
  norm_num

example : stepActionRat regionActionStep ≠ stepActionRat matulaActionStep := by
  rw [show stepActionRat regionActionStep = (9 : Rat) / 2 by
        have hcost : transportCostRat regionActionStep.signature = 3 := by
          have hsafe : HeytingLean.ATP.LensTransport.isSafeTransport .omega .region = true := by
            native_decide
          simp [transportCostRat, ProofStep.signature, regionActionStep, s1, loopState,
            actionTransportProbe_region_profile, hsafe]
          norm_num
        have hnat : operationNaturalnessRat regionActionStep.signature = 1 := by
          native_decide
        have hcompress : informationCompressionRat regionActionStep.signature = (1 : Rat) / 2 := by
          native_decide
        simp [stepActionRat, stepActionFromSignatureRat, hcost, hnat, hcompress]
        norm_num,
      show stepActionRat matulaActionStep = (15 : Rat) / 2 by
        have hcost : transportCostRat matulaActionStep.signature = 6 := by
          have hsafe : HeytingLean.ATP.LensTransport.isSafeTransport .omega .matula = true := by
            native_decide
          simp [transportCostRat, ProofStep.signature, matulaActionStep, matulaState, s1,
            actionTransportProbe_matula_profile, hsafe]
          norm_num
        have hnat : operationNaturalnessRat matulaActionStep.signature = 1 := by
          native_decide
        have hcompress : informationCompressionRat matulaActionStep.signature = (1 : Rat) / 2 := by
          native_decide
        simp [stepActionRat, stepActionFromSignatureRat, hcost, hnat, hcompress]
        norm_num]
  norm_num

example : detectTopologyHeuristic [p1] = false := by
  native_decide

example : (findEquivalents s0).length > 0 := by
  native_decide

example :
    Adapter.parseGoalToFSum "⊢ True" .omega ≠ [] := by
  native_decide

example :
    let node : HeytingLean.ATP.DifferentiableATP.SearchNode :=
      { goal := "⊢ True"
        depth := 2
        parentTactic := some "intro"
        preferredTactic := some "simp"
        groupId := none
        groupSubgoalIndex := none
        priorityScore := 0
        proofScriptRev := []
        carry := none }
    let state := Adapter.searchNodeToProofState node .graph
    let roundtrip := Adapter.proofStateToSearchNode state
    state.depth = 2 ∧ state.lens = .graph ∧ roundtrip.goal = "⊢ True" ∧ state.goal ≠ [] := by
  native_decide

example :
    (Adapter.standardConstructors { s0 with context := "⊢ ∀ n : Nat, n + 1 > n" }).length ≥ 2 := by
  native_decide

example :
    Adapter.proofPathToScript p1 = [("goal", "simp")] := by
  native_decide

example : (assessPaths s0 testTransport testConstructors).length > 0 := by
  native_decide

example : let decided := decideLane 1.0 (assessPaths s0 testTransport testConstructors)
    decided.length = (assessPaths s0 testTransport testConstructors).length := by
  native_decide

example :
    (Adapter.runPathIntegralSearch "⊢ True" .omega { maxSteps := 3 }).isSome = true := by
  native_decide

example :
    (Adapter.runPathIntegralSearch "⊢ True" .omega
      { maxSteps := 3, schedule := .geometric 1.2 }).isSome = true := by
  native_decide

example :
    (Adapter.runPathIntegralSearch "⊢ True" .omega
      { maxSteps := 3, schedule := .logarithmic 1.0 }).isSome = true := by
  native_decide

example : obstructionClass loopPath =
    HeytingLean.PerspectivalPlenum.ContextualityEngine.CechObstructionClass.h1_global_section := by
  native_decide

example : checkObstruction canonicalObstructedLoop = .obstructed .h1_global_section := by
  simpa using canonical_loop_detected

example : checkObstruction p1 = .clear := by
  simpa [p1] using singleton_clear localStep

example :
    (partitionByObstruction [(loopPath, 1.0), (p1, 0.5)]).1.map Prod.fst = [p1] := by
  native_decide

example :
    (pruneObstructed { obstructionCheckInterval := 1 } 0 [(loopPath, 1.0), (p1, 0.5)]).map Prod.fst = [p1] := by
  native_decide

example :
    (pruneObstructed { obstructionCheckInterval := 0 } 0 [(loopPath, 1.0), (p1, 0.5)]).map Prod.fst =
      [loopPath, p1] := by
  native_decide

example : ProofPath.homotopic p0 pStay := by
  have hfree : ∀ p ∈ [p0, pStay], ∀ s ∈ p.steps, s.lensTransition = none := by
    intro p hp s hs
    simp at hp
    rcases hp with rfl | rfl
    · cases hs
    · simp [pStay, ProofPath.singleton, stayStep] at hs
      rcases hs with rfl
      rfl
  have h :=
    single_lens_all_homotopic [p0, pStay] hfree p0 (by simp) pStay (by simp) rfl rfl
  simpa using h

example :
    Filter.Tendsto (fun β => pathWeight β p1 / pathWeight β p0) Filter.atTop (nhds 0) := by
  apply beta_limit_classical
  have hrat : 0 < pathActionRat p1 := by
    have hlen : "simp".length ≤ 4 := by native_decide
    simp [p1, pathActionRat, stepActionRat, stepActionFromSignatureRat,
      operationNaturalnessRat, transportCostRat, informationCompressionRat, localStep,
      ProofPath.singleton, ProofStep.signature, ProofStep.goalComplexity, s0, s1,
      baseGoal, reducedGoal, hlen]
    by_cases hcmp : l2NormSq [] ≤ l2NormSq [(Comb.K, 1)]
    · simp [hcmp]
      norm_num
    · simp [hcmp]
      norm_num
  have hp0 : pathAction p0 = 0 := by
    simpa [p0] using action_id s0
  rw [hp0]
  simpa [p1, pathAction, ProofPath.singleton] using (Rat.cast_pos.mpr hrat)

example :
    ∃ p q : ProofPath, ¬ ProofPath.homotopic p q := by
  rcases nontrivial_H1_implies_inequivalent
      HeytingLean.PerspectivalPlenum.LensSheaf.Cech.True.Triangle.parityClass with
    ⟨p, q, _, _, hneq⟩
  exact ⟨p, q, hneq⟩

example :
    Nonempty (pathFiber (Quotient.mk ProofPath.homotopicSetoid canonicalObstructedLoop)) := by
  simpa using pathFiber_nonempty
    (Quotient.mk ProofPath.homotopicSetoid canonicalObstructedLoop)

example :
    groupoidObstructionClass
        (Quotient.mk ProofPath.homotopicSetoid canonicalObstructedLoop) =
      .h1_global_section := by
  simpa using groupoidObstructionClass_canonicalObstructedLoop

example :
    obstructionClassT canonicalStationaryLoop = obstructionClass canonicalStationaryLoop := by
  exact obstructionClassT_canonical_stationary

example :
    ∃ w,
      groupoidH1Witness?
          (Quotient.mk ProofPath.homotopicSetoid canonicalObstructedLoop) = some w := by
  exact groupoid_obstruction_yields_H1
    (Quotient.mk ProofPath.homotopicSetoid canonicalObstructedLoop)
    groupoidObstructionClass_canonicalObstructedLoop

example :
    ∃ w,
      groupoidH1Witness?
          (Quotient.mk ProofPath.homotopicSetoid canonicalObstructedLoop) = some w := by
  exact groupoidH1Witness_canonicalObstructedLoop

example :
    groupoidJ (C := fun _ => Nat)
        (d := fun _ => 7)
        (hcompat := by
          intro p q _h
          rfl
        )
        (Quotient.mk ProofPath.homotopicSetoid canonicalObstructedLoop) = 7 := by
  simp

example : (pathIntegralSearch {} s0 testTransport testConstructors goalClosed).isSome = true := by
  native_decide

end Tests
end PathIntegral
end HeytingLean
