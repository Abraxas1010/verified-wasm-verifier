import Lean
import HeytingLean.ProofState.Snapshot

open Lean
open Lean.Elab.Command
open HeytingLean.ProofState

namespace HeytingLean.Tests.ProofState

def sampleFVarExpr : Expr :=
  .fvar { name := `sampleHyp }

def sampleMVarExpr : Expr :=
  .mvar { name := `sampleGoal }

def sampleLocal : LocalDeclSnapshot :=
  { index := 0
    userName := "h"
    fvarId := "sampleHyp"
    binderInfo := .default
    isImplementationDetail := false
    typeExpr := .const `Nat []
    valueExpr? := some (.lit (.natVal 3))
    typePP := "Nat"
    valuePP? := some "3" }

def sampleGoal : GoalSnapshot :=
  { goalId := "sampleGoal"
    goalType := .forallE `x (.const `Nat []) (.const `Nat []) .default
    goalTypePP := "Nat -> Nat"
    localContext := #[sampleLocal] }

def sampleBatch : GoalBatchSnapshot :=
  { goals := #[sampleGoal], solved := false }

def sampleEnvelope : ExtractionEnvelope :=
  { ok := true
    requestGoal := "forall x : Nat, Nat"
    appliedTactics := #["intro x"]
    snapshot := sampleBatch
    stderr := ""
    extractionKind := "source_checkpoint"
    sourceFile? := some "lean/HeytingLean/Tests/ProofState/SourceFixture.lean"
    sourceDecl? := some "HeytingLean.Tests.ProofState.sourceFixture_id"
    checkpointIndex? := some 0
    checkpointLabel? := some "body_line_prefix:1" }

private def expectOk {α} (label : String) : Except String α → CommandElabM α
  | .ok value => pure value
  | .error err => throwError "{label} failed: {err}"

run_cmd do
  let encoded := HeytingLean.CLI.LeanExprJson.exprToJson sampleFVarExpr
  let decoded ← expectOk "fvar expr roundtrip" <| HeytingLean.CLI.LeanExprJson.exprFromJson encoded
  unless HeytingLean.CLI.LeanExprJson.exprToJson decoded == encoded do
    throwError "fvar expr roundtrip mismatch"

run_cmd do
  let encoded := HeytingLean.CLI.LeanExprJson.exprToJson sampleMVarExpr
  let decoded ← expectOk "mvar expr roundtrip" <| HeytingLean.CLI.LeanExprJson.exprFromJson encoded
  unless HeytingLean.CLI.LeanExprJson.exprToJson decoded == encoded do
    throwError "mvar expr roundtrip mismatch"

run_cmd do
  let decoded ← expectOk "local decl roundtrip" <| LocalDeclSnapshot.fromJson sampleLocal.toJson
  unless decoded.toJson == sampleLocal.toJson do
    throwError "local decl JSON roundtrip mismatch"

run_cmd do
  let decoded ← expectOk "goal roundtrip" <| GoalSnapshot.fromJson sampleGoal.toJson
  unless decoded.toJson == sampleGoal.toJson do
    throwError "goal JSON roundtrip mismatch"

run_cmd do
  let decoded ← expectOk "goal batch roundtrip" <| GoalBatchSnapshot.fromJson sampleBatch.toJson
  unless decoded.toJson == sampleBatch.toJson do
    throwError "goal batch JSON roundtrip mismatch"

run_cmd do
  let decoded ← expectOk "envelope roundtrip" <| ExtractionEnvelope.fromJson sampleEnvelope.toJson
  unless decoded.toJson == sampleEnvelope.toJson do
    throwError "envelope JSON roundtrip mismatch"

end HeytingLean.Tests.ProofState
