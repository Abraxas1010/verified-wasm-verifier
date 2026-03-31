import HeytingLean.Embeddings.AdelicInstances
import HeytingLean.Embeddings.HolographicScreen
import HeytingLean.Embeddings.CrossLensTransport
import HeytingLean.QuantumActiveInference
import HeytingLean.ATP
import HeytingLean.Noneism.Witness
import HeytingLean.Noneism.GenerativeModel
import Mathlib.Tactic

/-!
# Unified system sanity checks

Compile-time wiring checks for the “HeytingLean unified system” scaffold modules.
-/

namespace HeytingLean
namespace Tests
namespace UnifiedSystem

open HeytingLean.Embeddings

def trivialScreen : HolographicScreen :=
  { Carrier := fun _ => Nat
    Screen := fun _ => Nat
    encode := fun _ x => x
    decode := fun _ x => x
    rt1 := by intro _ x; rfl
    rt2 := by intro _ _; rfl }

def trivialTransport : CrossLensTransport (fun _ : LensID => Nat) Nat :=
  { toPlato := fun _ x => x
    fromPlato := fun _ x => x
    rt1 := by intro _ x; rfl
    rt2 := by intro _ x; rfl }

example : QuantumActiveInference.GluingCondition trivialTransport LensID.omega LensID.graph 3 3 := by
  rfl

def net0 : ATP.ProofNetwork :=
  {}

def net1 : ATP.ProofNetwork :=
  let (g1, n1) := ATP.ProofNetwork.addNode net0 LensID.omega "start"
  let (g2, n2) := ATP.ProofNetwork.addNode g1 LensID.graph "alt"
  ATP.addGlueEdge g2 n1 n2

example : net1.edgeCount = 1 := by
  rfl

example : Bool := net1.phaseTransitionHeuristic

example : ATP.ATPOutcome.toString (ATP.blocked "obstruction" [LensID.graph]) = "blocked_certified" := by
  rfl

example : ATP.ATPOutcome.isBlocked (ATP.blocked "obstruction" [LensID.graph]) = true := by
  rfl

def net2NodeId : Nat :=
  (ATP.ProofNetwork.addNode net1 LensID.omega "end").2

def net2 : ATP.ProofNetwork :=
  let (g1, n1) := ATP.ProofNetwork.addNode net1 LensID.omega "end"
  let proofNodeArtifact := ATP.proofArtifact "bridgeGoal"
  let g2 := ATP.addWitnessedGlueEdge g1 n1 n1 "localWitness"
  let g3 := ATP.ProofNetwork.setNodeOutcome g2 n1 (.proved proofNodeArtifact)
  let witnessTrace : List ATP.LensTransfer := [{
    source := LensID.omega,
    target := LensID.graph,
    reason := "coarse-grain transport",
    witnessTheorem := "simulated_witness"
  }]
  let g4 := ATP.ProofNetwork.setNodeTransferTrace g3 n1 witnessTrace
  ATP.ProofNetwork.setNodeSheafWitnesses g4 n1 ["sheaf-witness-1", "sheaf-witness-2"]

example : ATP.ATPOutcome.isProved ((match ATP.ProofNetwork.findNode net2 net2NodeId with
    | some n => n.outcome
    | none => ATP.ATPOutcome.failed) ) = true := by
  native_decide

example : ATP.ATPOutcome.isOpen ATP.ATPOutcome.inProgress = true := by
  rfl

def wf : HeytingLean.Noneism.WitnessedFormula Unit :=
  { term := .var 0, formula := .top }

example : HeytingLean.Noneism.witnessNecessity wf = HeytingLean.Noneism.Formula.eExists (.var 0) := by
  rfl

example : True := by
  trivial

end UnifiedSystem
end Tests
end HeytingLean
