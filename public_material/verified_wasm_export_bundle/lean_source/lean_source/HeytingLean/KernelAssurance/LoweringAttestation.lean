import Lean.Data.Json
import HeytingLean.KernelAssurance.ObligationManifest
import HeytingLean.LeanCP.Compile.SKYLoweringSemantics
import HeytingLean.LoF.Combinators.SKYReducerKernel

namespace HeytingLean.KernelAssurance

open HeytingLean.LoF.Combinators.SKYReducerKernel
open HeytingLean.LeanCP.Compile.SKYLoweringSemantics

structure LoweringAttestedTheorem where
  name : String
  type : String
  deriving Repr, Inhabited, BEq, Lean.ToJson, Lean.FromJson

structure LoweringAttestation where
  version : String := "kernel-obligation-lowering-attestation-v1"
  sourceBundleDigest : String
  sourceModule : String
  correspondenceTheorems : Array LoweringAttestedTheorem
  invariantTheorems : Array LoweringAttestedTheorem
  coveredNodeTags : Array String
  coveredFailureModes : Array String
  invariantSurface : String
  allTagsCovered : Bool
  allFailureModesCovered : Bool
  wellFormedStepStable : Bool
  singleKernel : Bool
  fuelBounded : Bool
  oracleParametric : Bool
  attested : Bool
  claimBoundary : String
  deriving Repr, Inhabited, BEq, Lean.ToJson, Lean.FromJson

private theorem loweringSingleStepWitness
    (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) :
    runLoweredStep? s oracleVals = expectedStep? s oracleVals :=
  runLoweredStep?_eq_expectedStep? s oracleVals hwf

private theorem loweringFuelWitness
    (fuel : Nat) (s : State) (oracleVals : Array Int) (hwf : s.WellFormed) :
    runLoweredFuel? fuel s oracleVals = expectedRunFuel? fuel s oracleVals :=
  runLoweredFuel?_eq_expectedRunFuel? fuel s oracleVals hwf

private theorem loweringPushNodeWellFormedWitness
    (s s' : State) (id : Nat) (hwf : s.WellFormed)
    (hpush : s.pushNode .app 0 0 0 = some (s', id)) :
    s'.WellFormed :=
  State.pushNode_wellFormed hwf hpush

private theorem loweringSetFocusStackWellFormedWitness
    (s : State) (hwf : s.WellFormed) (focus : Nat) (stack : List Nat) :
    ({ s with focus := focus, stack := stack }).WellFormed :=
  State.setFocusStack_wellFormed hwf focus stack

private theorem loweringStepWellFormedWitness
    (oracleEval : Nat → Bool) (s : State) (hwf : s.WellFormed) :
    (step oracleEval s).state.WellFormed :=
  step_wellFormed (oracleEval := oracleEval) (s := s) hwf

private def loweringCorrespondenceTheorems : Array LoweringAttestedTheorem :=
  #[
    { name := "HeytingLean.LeanCP.Compile.SKYLoweringSemantics.runLoweredStep?_eq_expectedStep?"
      type := "∀ (s : State) (oracleVals : Array Int), s.WellFormed → runLoweredStep? s oracleVals = expectedStep? s oracleVals" },
    { name := "HeytingLean.LeanCP.Compile.SKYLoweringSemantics.runLoweredFuel?_eq_expectedRunFuel?"
      type := "∀ (fuel : Nat) (s : State) (oracleVals : Array Int), s.WellFormed → runLoweredFuel? fuel s oracleVals = expectedRunFuel? fuel s oracleVals" }
  ]

private def loweringInvariantTheorems : Array LoweringAttestedTheorem :=
  #[
    { name := "HeytingLean.LoF.Combinators.SKYReducerKernel.State.pushNode_wellFormed"
      type := "pushNode preserves structural WellFormed alignment when allocation succeeds" },
    { name := "HeytingLean.LoF.Combinators.SKYReducerKernel.State.setFocusStack_wellFormed"
      type := "setFocusStack preserves structural WellFormed alignment" },
    { name := "HeytingLean.LoF.Combinators.SKYReducerKernel.step_wellFormed"
      type := "∀ oracleEval s, s.WellFormed → (step oracleEval s).state.WellFormed" }
  ]

private def loweringTagCoverage : Array String :=
  #["app", "combK", "combS", "combY", "oracle"]

private def loweringFailureModeCoverage : Array String :=
  #["focus_out_of_range", "invalid_tag", "short_stack", "out_of_heap", "halted"]

def mkLoweringClaimBoundary : String :=
  "This lowering attestation records the proved SKY-lowering correspondence for a single kernel surface. " ++
  "The claim is oracle-parametric and fuel-bounded at the recursive execution layer, with one-step correspondence and step-stable WellFormed invariants proved underneath. " ++
  "It does not by itself prove Lean's full kernel."

def LoweringAttestation.ofBase
    (base : KernelObligationAssuranceManifest) : LoweringAttestation :=
  let claimBoundary := mkLoweringClaimBoundary
  { sourceBundleDigest := base.bundleDigest
    sourceModule := base.descriptor.moduleName
    correspondenceTheorems := loweringCorrespondenceTheorems
    invariantTheorems := loweringInvariantTheorems
    coveredNodeTags := loweringTagCoverage
    coveredFailureModes := loweringFailureModeCoverage
    invariantSurface := "State.WellFormed is the step-stable structural invariant surface used by the lowering correspondence."
    allTagsCovered := loweringTagCoverage.size = 5
    allFailureModesCovered := loweringFailureModeCoverage.size = 5
    wellFormedStepStable := true
    singleKernel := true
    fuelBounded := true
    oracleParametric := true
    attested := true
    claimBoundary := claimBoundary }

end HeytingLean.KernelAssurance
