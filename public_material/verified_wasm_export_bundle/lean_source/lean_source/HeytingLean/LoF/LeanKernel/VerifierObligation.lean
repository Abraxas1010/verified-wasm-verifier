import Lean.Data.Json

namespace HeytingLean.LoF.LeanKernel

open Lean

inductive ReplayKind where
  | whnfCall
  | whnfStep
  | tagCheck
  deriving Inhabited, DecidableEq, Repr, BEq

def ReplayKind.asString : ReplayKind → String
  | .whnfCall => "whnf_call"
  | .whnfStep => "whnf_step"
  | .tagCheck => "tag_check"

structure DependencyRef where
  id : String
  edgeKind : String
  deriving Inhabited, Repr, BEq

structure VerifierObligation where
  id : String
  declName : String
  declKind : String
  traceRole : String
  traceGrain : String := "whnf"
  verificationMode : String := "whnf_call"
  replayKind : ReplayKind := .whnfCall
  joinGroup : String
  deps : Array DependencyRef := #[]
  projectedBetaZetaSteps : Nat := 0
  stepCount : Nat := 0
  deltaIotaSteps : Nat := 0
  nodeCount : Nat := 0
  inputExprRepr : String := ""
  outputExprRepr : String := ""
  nativeWhnfRepr : String := ""
  expectedTagTerm : String := ""
  machineJson : Json := Json.null
  finalJson : Json := Json.null
  deriving Inhabited, BEq

structure VerifierArtifact where
  schemaVersion : Nat := 1
  formatName : String := "sky-v1"
  toolName : String := "verified_check"
  artifactKind : String := "portable_verifier_obligations"
  moduleName : String
  traceGrain : String := "whnf"
  joinStrategy : String := "declaration_all_clean"
  selectedDeclarations : Nat
  totalDeclarations : Nat
  traceMaxSteps : Nat
  fuelWhnf : Nat
  fuelDefEq : Nat
  fuelReduce : Nat
  maxNodes : Nat
  eligibleTraceEntries : Nat
  obligations : Array VerifierObligation
  honestAssessment : String
  deriving Inhabited, BEq

def VerifierArtifact.obligationsTotal (artifact : VerifierArtifact) : Nat :=
  artifact.obligations.size

def VerifierArtifact.omittedTraceEntries (artifact : VerifierArtifact) : Nat :=
  artifact.eligibleTraceEntries - artifact.obligationsTotal

def VerifierArtifact.replayKindCounts (artifact : VerifierArtifact) : Array (String × Nat) :=
  let whnfCalls :=
    artifact.obligations.foldl (init := 0) fun acc obligation =>
      if obligation.replayKind == .whnfCall then acc + 1 else acc
  let whnfSteps :=
    artifact.obligations.foldl (init := 0) fun acc obligation =>
      if obligation.replayKind == .whnfStep then acc + 1 else acc
  let tagChecks :=
    artifact.obligations.foldl (init := 0) fun acc obligation =>
      if obligation.replayKind == .tagCheck then acc + 1 else acc
  #[("whnf_call", whnfCalls), ("whnf_step", whnfSteps), ("tag_check", tagChecks)]

end HeytingLean.LoF.LeanKernel
