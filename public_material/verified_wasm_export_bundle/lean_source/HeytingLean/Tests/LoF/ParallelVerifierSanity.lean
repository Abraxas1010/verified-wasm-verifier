import HeytingLean.LoF.LeanKernel.VerifierObligationJson

namespace HeytingLean.Tests.LoF

open Lean
open HeytingLean.LoF.LeanKernel

def sampleObligation : VerifierObligation :=
  { id := "Fixture.sample:decl_value:whnf"
    declName := "Fixture.sample"
    declKind := "def"
    traceRole := "decl_value"
    joinGroup := "Fixture.sample"
    projectedBetaZetaSteps := 1
    stepCount := 1
    nodeCount := 3
    machineJson := Json.mkObj [("tag", Json.str "fixture")]
    finalJson := Json.mkObj [("tag", Json.str "fixture")]
  }

def sampleArtifact : VerifierArtifact :=
  { moduleName := "Fixture.Module"
    selectedDeclarations := 1
    totalDeclarations := 1
    traceMaxSteps := 8
    fuelWhnf := 20
    fuelDefEq := 20
    fuelReduce := 400000
    maxNodes := 1024
    eligibleTraceEntries := 1
    obligations := #[sampleObligation]
    honestAssessment := "fixture"
  }

example : sampleArtifact.obligationsTotal = 1 := rfl

example : sampleArtifact.omittedTraceEntries = 0 := rfl

example : sampleArtifact.replayKindCounts = #[("whnf_call", 1), ("whnf_step", 0), ("tag_check", 0)] := rfl

end HeytingLean.Tests.LoF
