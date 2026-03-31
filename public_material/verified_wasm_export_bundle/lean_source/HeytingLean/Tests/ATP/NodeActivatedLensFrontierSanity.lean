import HeytingLean.ATP
import HeytingLean.ATP.NodeActivatedLensFrontier
import Mathlib.Tactic

namespace HeytingLean
namespace Tests
namespace ATP

open HeytingLean.Embeddings
open HeytingLean.ATP

def provedNode : ProofNode where
  id := 7
  lens := .omega
  label := "proved-node"
  outcome := .proved {
    theoremName := "demo_theorem"
    replayScript := some "exact trivial"
    sheafWitnesses := ["wA"]
    transportTrace := [
      { source := .omega, target := .graph, reason := "r1", witnessTheorem := "w1" },
      { source := .omega, target := .tensor, reason := "r2", witnessTheorem := "w2" }
    ]
  }

def blockedNode : ProofNode where
  id := 8
  lens := .graph
  label := "blocked-node"
  outcome := .blockedCertified {
    obstructionClass := "projection_not_verified"
    suggestedLenses := [.omega, .tensor]
  }

def pendingNode : ProofNode where
  id := 9
  lens := .tensor
  label := "pending-node"
  outcome := .inProgress

def mixedTraceNode : ProofNode where
  id := 10
  lens := .omega
  label := "mixed-trace-node"
  outcome := .proved {
    theoremName := "mixed_demo"
    replayScript := some "exact trivial"
    sheafWitnesses := ["wMixed"]
    transportTrace := [
      { source := .omega, target := .graph, reason := "direct", witnessTheorem := "wdirect" },
      { source := .graph, target := .tensor, reason := "second_hop", witnessTheorem := "wsecond" }
    ]
  }

example : (summaryOfProofNode? pendingNode) = none := by
  simp [pendingNode, summaryOfProofNode?_none_of_inProgress]

example : (summaryOfProofNode? provedNode).isSome = true := by
  simp [summaryOfProofNode?, provedNode]

example : (summaryOfProofNode? blockedNode).isSome = true := by
  simp [summaryOfProofNode?, blockedNode]

def provedSummary : NodeActivationSummary :=
  match summaryOfProofNode? provedNode with
  | some s => s
  | none => panic! "impossible"

def blockedSummary : NodeActivationSummary :=
  match summaryOfProofNode? blockedNode with
  | some s => s
  | none => panic! "impossible"

def mixedTraceSummary : NodeActivationSummary :=
  match summaryOfProofNode? mixedTraceNode with
  | some s => s
  | none => panic! "impossible"

example : activationCount provedSummary = 4 := by
  native_decide

example : activationCount blockedSummary = 3 := by
  native_decide

example : activationCount mixedTraceSummary = 3 := by
  native_decide

example : continueOpening provedSummary ∈ activateFrontier provedSummary := by
  exact continue_mem_activateFrontier provedSummary

example : ∀ o ∈ transportOpenings provedSummary, o.targetLens ≠ provedSummary.currentLens := by
  intro o ho
  exact mem_transportOpenings_target_ne_current ho

example : ∀ o ∈ obstructionOpenings blockedSummary, o.targetLens ≠ blockedSummary.currentLens := by
  intro o ho
  exact mem_obstructionOpenings_target_ne_current ho

example : generalizationOpenings provedSummary ≠ [] := by
  native_decide

example : generalizationOpenings blockedSummary = [] := by
  native_decide

example : mixedTraceSummary.transportTargets = [.graph] := by
  native_decide

example : (transportOpenings mixedTraceSummary).map (·.targetLens) = [.graph] := by
  native_decide

end ATP
end Tests
end HeytingLean
