import HeytingLean.ProofState.Snapshot
import HeytingLean.LoF.ICCKernel.ProofState

open HeytingLean.ProofState
open HeytingLean.LoF.ICCKernel
open HeytingLean.LoF.ICCKernel.Lower

namespace HeytingLean.Tests.LoF

def sampleLocal : LocalDeclSnapshot :=
  { index := 0
    userName := "h"
    fvarId := "sampleHyp"
    binderInfo := .default
    isImplementationDetail := false
    typeExpr := .const `Nat []
    valueExpr? := some (.lit (.natVal 7))
    typePP := "Nat"
    valuePP? := some "7" }

def sampleGoal : GoalSnapshot :=
  { goalId := "sampleGoal"
    goalType := .forallE `x (.const `Nat []) (.const `Nat []) .default
    goalTypePP := "Nat -> Nat"
    localContext := #[sampleLocal] }

def sampleEnvelope : ExtractionEnvelope :=
  { ok := true
    requestGoal := "forall x : Nat, Nat"
    appliedTactics := #["intro x"]
    snapshot := { goals := #[sampleGoal], solved := false }
    stderr := ""
    extractionKind := "source_checkpoint"
    sourceFile? := some "lean/HeytingLean/Tests/ProofState/SourceFixture.lean"
    sourceDecl? := some "HeytingLean.Tests.ProofState.sourceFixture_id"
    checkpointIndex? := some 0
    checkpointLabel? := some "body_line_prefix:1" }

def sampleRow : ProofStateCorpusRow :=
  ProofStateCorpusRow.ofEnvelope sampleEnvelope

example : sampleRow.goalCount = 1 := by
  native_decide

example : sampleRow.localDeclCount = 1 := by
  native_decide

example : sampleRow.extractionKind = "source_checkpoint" := by
  native_decide

example : sampleRow.sourceDecl? = some "HeytingLean.Tests.ProofState.sourceFixture_id" := by
  native_decide

example : sampleRow.goals[0]!.goalTypeTerm.structuralKey = (lowerExprCore sampleGoal.goalType).structuralKey := by
  native_decide

example : sampleRow.goals[0]!.localContext[0]!.typeTerm.structuralKey = (lowerExprCore sampleLocal.typeExpr).structuralKey := by
  native_decide

example :
    sampleRow.goals[0]!.localContext[0]!.valueTerm.map Term.structuralKey =
      (sampleLocal.valueExpr?.map lowerExprCore).map Term.structuralKey := by
  native_decide

end HeytingLean.Tests.LoF
