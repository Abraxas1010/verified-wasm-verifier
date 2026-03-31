import Lean.Data.Json
import HeytingLean.KernelAssurance.ExportSupport
import HeytingLean.KernelAssurance.ObligationSurface

namespace HeytingLean.KernelAssurance

open Lean
open HeytingLean.LoF.LeanKernel

private structure ObligationEntryMaterial where
  id : String
  declName : String
  declKind : String
  traceRole : String
  traceGrain : String
  verificationMode : String
  replayKind : ReplayKind
  joinGroup : String
  depIds : Array String
  family : ObligationFamilyId
  status : SupportStatus
  projectedBetaZetaSteps : Nat
  stepCount : Nat
  deltaIotaSteps : Nat
  nodeCount : Nat
  inputExprRepr : String
  outputExprRepr : String
  nativeWhnfRepr : String
  expectedTagTerm : String
  machineDigest : String
  finalDigest : String
  deriving Repr, Inhabited, BEq, ToJson

structure ObligationEntry where
  id : String
  declName : String
  declKind : String
  traceRole : String
  traceGrain : String
  verificationMode : String
  replayKind : ReplayKind
  joinGroup : String
  deps : Array DependencyRef
  family : ObligationFamilyId
  status : SupportStatus
  projectedBetaZetaSteps : Nat
  stepCount : Nat
  deltaIotaSteps : Nat
  nodeCount : Nat
  inputExprRepr : String
  outputExprRepr : String
  nativeWhnfRepr : String
  expectedTagTerm : String
  machineDigest : String
  finalDigest : String
  entryDigest : String
  obligation : VerifierObligation
  deriving Inhabited, ToJson

def obligationJsonDigest (json : Json) : String :=
  structuralDigest json

def mkObligationEntryDigest
    (id declName declKind traceRole traceGrain verificationMode joinGroup : String)
    (replayKind : ReplayKind)
    (deps : Array DependencyRef)
    (family : ObligationFamilyId)
    (status : SupportStatus)
    (projectedBetaZetaSteps stepCount deltaIotaSteps nodeCount : Nat)
    (inputExprRepr outputExprRepr nativeWhnfRepr expectedTagTerm machineDigest finalDigest : String) :
    String :=
  structuralDigest ({
    id := id
    declName := declName
    declKind := declKind
    traceRole := traceRole
    traceGrain := traceGrain
    verificationMode := verificationMode
    replayKind := replayKind
    joinGroup := joinGroup
    depIds := deps.map (·.id)
    family := family
    status := status
    projectedBetaZetaSteps := projectedBetaZetaSteps
    stepCount := stepCount
    deltaIotaSteps := deltaIotaSteps
    nodeCount := nodeCount
    inputExprRepr := inputExprRepr
    outputExprRepr := outputExprRepr
    nativeWhnfRepr := nativeWhnfRepr
    expectedTagTerm := expectedTagTerm
    machineDigest := machineDigest
    finalDigest := finalDigest
  } : ObligationEntryMaterial)

def ObligationEntry.recomputedEntryDigest (entry : ObligationEntry) : String :=
  mkObligationEntryDigest
    entry.id entry.declName entry.declKind entry.traceRole entry.traceGrain
    entry.verificationMode entry.joinGroup entry.replayKind entry.deps entry.family entry.status
    entry.projectedBetaZetaSteps entry.stepCount entry.deltaIotaSteps entry.nodeCount
    entry.inputExprRepr entry.outputExprRepr entry.nativeWhnfRepr entry.expectedTagTerm
    entry.machineDigest entry.finalDigest

def mkObligationEntry (obligation : VerifierObligation) : ObligationEntry :=
  let family := familyOfObligation obligation
  let status := statusOfObligation obligation
  let machineDigest := obligationJsonDigest obligation.machineJson
  let finalDigest := obligationJsonDigest obligation.finalJson
  {
    id := obligation.id
    declName := obligation.declName
    declKind := obligation.declKind
    traceRole := obligation.traceRole
    traceGrain := obligation.traceGrain
    verificationMode := obligation.verificationMode
    replayKind := obligation.replayKind
    joinGroup := obligation.joinGroup
    deps := obligation.deps
    family := family
    status := status
    projectedBetaZetaSteps := obligation.projectedBetaZetaSteps
    stepCount := obligation.stepCount
    deltaIotaSteps := obligation.deltaIotaSteps
    nodeCount := obligation.nodeCount
    inputExprRepr := obligation.inputExprRepr
    outputExprRepr := obligation.outputExprRepr
    nativeWhnfRepr := obligation.nativeWhnfRepr
    expectedTagTerm := obligation.expectedTagTerm
    machineDigest := machineDigest
    finalDigest := finalDigest
    entryDigest := mkObligationEntryDigest
      obligation.id obligation.declName obligation.declKind obligation.traceRole obligation.traceGrain
      obligation.verificationMode obligation.joinGroup obligation.replayKind obligation.deps family status
      obligation.projectedBetaZetaSteps obligation.stepCount obligation.deltaIotaSteps obligation.nodeCount
      obligation.inputExprRepr obligation.outputExprRepr obligation.nativeWhnfRepr obligation.expectedTagTerm
      machineDigest finalDigest
    obligation := obligation
  }

private structure ObligationBundleDigestMaterial where
  descriptor : ObligationSliceDescriptor
  selectedDeclarations : Nat
  totalDeclarations : Nat
  eligibleTraceEntries : Nat
  obligationsTotal : Nat
  exportedSupported : Nat
  exportedBlocked : Nat
  exportedUnclassified : Nat
  entryDigests : Array String
  deriving Repr, Inhabited, BEq, ToJson

structure ObligationSliceBundle where
  descriptor : ObligationSliceDescriptor
  selectedDeclarations : Nat
  totalDeclarations : Nat
  eligibleTraceEntries : Nat
  obligationsTotal : Nat
  exportedSupported : Nat
  exportedBlocked : Nat
  exportedUnclassified : Nat
  entries : Array ObligationEntry
  bundleDigest : String
  deriving Inhabited, ToJson

def ObligationSliceBundle.omittedTraceEntries (bundle : ObligationSliceBundle) : Nat :=
  bundle.eligibleTraceEntries - bundle.obligationsTotal

def ObligationSliceBundle.recomputedBundleDigest (bundle : ObligationSliceBundle) : String :=
  structuralDigest ({
    descriptor := bundle.descriptor
    selectedDeclarations := bundle.selectedDeclarations
    totalDeclarations := bundle.totalDeclarations
    eligibleTraceEntries := bundle.eligibleTraceEntries
    obligationsTotal := bundle.obligationsTotal
    exportedSupported := bundle.exportedSupported
    exportedBlocked := bundle.exportedBlocked
    exportedUnclassified := bundle.exportedUnclassified
    entryDigests := bundle.entries.map (·.entryDigest)
  } : ObligationBundleDigestMaterial)

def ObligationSliceBundle.bundleDigestValid (bundle : ObligationSliceBundle) : Bool :=
  bundle.bundleDigest = bundle.recomputedBundleDigest

def ObligationSliceBundle.ofArtifact (artifact : VerifierArtifact) : ObligationSliceBundle :=
  let entries := artifact.obligations.map mkObligationEntry
  let exportedSupported := entries.foldl (fun acc e => if e.status = .supported then acc + 1 else acc) 0
  let exportedBlocked := entries.foldl (fun acc e => if e.status = .blocked then acc + 1 else acc) 0
  let exportedUnclassified := entries.foldl (fun acc e => if e.status = .unclassified then acc + 1 else acc) 0
  let descriptor : ObligationSliceDescriptor :=
    { schemaVersion := artifact.schemaVersion
      formatName := artifact.formatName
      toolName := artifact.toolName
      artifactKind := artifact.artifactKind
      moduleName := artifact.moduleName
      traceGrain := artifact.traceGrain
      joinStrategy := artifact.joinStrategy
      traceMaxSteps := artifact.traceMaxSteps
      fuelWhnf := artifact.fuelWhnf
      fuelDefEq := artifact.fuelDefEq
      fuelReduce := artifact.fuelReduce
      maxNodes := artifact.maxNodes
      honestAssessment := artifact.honestAssessment
      claimBoundary := mkObligationClaimBoundary artifact }
  let base : ObligationSliceBundle :=
    { descriptor := descriptor
      selectedDeclarations := artifact.selectedDeclarations
      totalDeclarations := artifact.totalDeclarations
      eligibleTraceEntries := artifact.eligibleTraceEntries
      obligationsTotal := artifact.obligationsTotal
      exportedSupported := exportedSupported
      exportedBlocked := exportedBlocked
      exportedUnclassified := exportedUnclassified
      entries := entries
      bundleDigest := "" }
  { base with bundleDigest := base.recomputedBundleDigest }

end HeytingLean.KernelAssurance
