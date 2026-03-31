import Lean.Data.Json
import HeytingLean.ProofState.Snapshot
import HeytingLean.LoF.ICCKernel.Corpus
import HeytingLean.LoF.ICCKernel.Lower.Expr

namespace HeytingLean
namespace LoF
namespace ICCKernel

open HeytingLean.ProofState
open HeytingLean.LoF.ICCKernel.Lower

structure ProofStateLocalDeclRow where
  index : Nat
  userName : String
  fvarId : String
  binderInfo : String
  isImplementationDetail : Bool
  typeTerm : Term
  valueTerm : Option Term
  typePP : String
  valuePP? : Option String
  deriving Repr, Inhabited, BEq, Lean.ToJson

structure ProofStateGoalRow where
  goalId : String
  goalTypeTerm : Term
  goalTypePP : String
  localContext : Array ProofStateLocalDeclRow
  deriving Repr, Inhabited, BEq, Lean.ToJson

structure ProofStateCorpusRow where
  rowId : String
  extractionKind : String
  requestGoal : String
  appliedTactics : Array String
  sourceFile? : Option String
  sourceDecl? : Option String
  checkpointIndex? : Option Nat
  checkpointLabel? : Option String
  solved : Bool
  goalCount : Nat
  localDeclCount : Nat
  goals : Array ProofStateGoalRow
  payloadText : String
  payloadKey : String
  deriving Repr, Inhabited, BEq, Lean.ToJson

def ProofStateLocalDeclRow.ofSnapshot (snap : LocalDeclSnapshot) : ProofStateLocalDeclRow :=
  { index := snap.index
    userName := snap.userName
    fvarId := snap.fvarId
    binderInfo := HeytingLean.ProofState.binderInfoToString snap.binderInfo
    isImplementationDetail := snap.isImplementationDetail
    typeTerm := lowerExprCore snap.typeExpr
    valueTerm := snap.valueExpr?.map lowerExprCore
    typePP := snap.typePP
    valuePP? := snap.valuePP? }

def ProofStateGoalRow.ofSnapshot (snap : GoalSnapshot) : ProofStateGoalRow :=
  { goalId := snap.goalId
    goalTypeTerm := lowerExprCore snap.goalType
    goalTypePP := snap.goalTypePP
    localContext := snap.localContext.map ProofStateLocalDeclRow.ofSnapshot }

private def localDeclPayloadText (decl : ProofStateLocalDeclRow) : String :=
  String.intercalate " "
    ([ decl.userName
     , decl.fvarId
     , decl.binderInfo
     , decl.typePP
     ] ++ decl.valuePP?.toList)

private def localDeclPayloadKey (decl : ProofStateLocalDeclRow) : String :=
  String.intercalate "::"
    [ toString decl.index
    , decl.fvarId
    , decl.typeTerm.structuralKey
    , decl.valueTerm.map Term.structuralKey |>.getD ""
    ]

private def goalPayloadText (goal : ProofStateGoalRow) : String :=
  String.intercalate " "
    ([goal.goalId, goal.goalTypePP] ++ goal.localContext.toList.map localDeclPayloadText)

private def goalPayloadKey (goal : ProofStateGoalRow) : String :=
  String.intercalate "::"
    ([goal.goalId, goal.goalTypeTerm.structuralKey] ++ goal.localContext.toList.map localDeclPayloadKey)

private def provenancePayloadText (env : ExtractionEnvelope) : List String :=
  [env.extractionKind] ++ env.sourceFile?.toList ++ env.sourceDecl?.toList ++ env.checkpointLabel?.toList

private def provenancePayloadKey (env : ExtractionEnvelope) : List String :=
  [env.extractionKind]
  ++ env.sourceFile?.toList
  ++ env.sourceDecl?.toList
  ++ (env.checkpointIndex?.map toString).toList
  ++ env.checkpointLabel?.toList

private def countGoalDecls (goal : ProofStateGoalRow) : Nat :=
  goal.localContext.size

private def collectGoalCounts (goal : ProofStateGoalRow) (acc : Array CountEntry) : Array CountEntry :=
  let acc := collectTermCounts goal.goalTypeTerm acc
  goal.localContext.foldl
    (fun running decl =>
      let running := collectTermCounts decl.typeTerm running
      match decl.valueTerm with
      | some value => collectTermCounts value running
      | none => running)
    acc

def ProofStateCorpusRow.ofEnvelope (env : ExtractionEnvelope) : ProofStateCorpusRow :=
  let goals := env.snapshot.goals.map ProofStateGoalRow.ofSnapshot
  let goalCount := goals.size
  let localDeclCount := goals.foldl (fun acc goal => acc + countGoalDecls goal) 0
  let payloadText :=
    String.intercalate " "
      (provenancePayloadText env ++ [env.requestGoal] ++ env.appliedTactics.toList ++ goals.toList.map goalPayloadText)
  let payloadKey :=
    String.intercalate "||"
      (provenancePayloadKey env ++ [env.requestGoal] ++ env.appliedTactics.toList ++ goals.toList.map goalPayloadKey)
  let rowKey :=
    String.intercalate "||"
      (provenancePayloadKey env ++ [env.requestGoal] ++ env.appliedTactics.toList ++ [payloadKey])
  { rowId := s!"proof_state::{hash rowKey}"
    extractionKind := env.extractionKind
    requestGoal := env.requestGoal
    appliedTactics := env.appliedTactics
    sourceFile? := env.sourceFile?
    sourceDecl? := env.sourceDecl?
    checkpointIndex? := env.checkpointIndex?
    checkpointLabel? := env.checkpointLabel?
    solved := env.snapshot.solved
    goalCount := goalCount
    localDeclCount := localDeclCount
    goals := goals
    payloadText := payloadText
    payloadKey := payloadKey }

structure ProofStateCorpusSummary where
  rows : Nat
  solvedRows : Nat
  goalCount : Nat
  localDeclCount : Nat
  exprConstructorCounts : Array CountEntry
  deriving Repr, Inhabited, BEq, Lean.ToJson

structure ProofStateCorpusBundle where
  rows : Array ProofStateCorpusRow
  summary : ProofStateCorpusSummary
  deriving Repr, Inhabited, BEq, Lean.ToJson

def ProofStateCorpusBundle.ofEnvelopes (envs : Array ExtractionEnvelope) : ProofStateCorpusBundle :=
  let rows := envs.map ProofStateCorpusRow.ofEnvelope
  let summary :=
    rows.foldl
      (fun acc row =>
        { rows := acc.rows + 1
          solvedRows := acc.solvedRows + (if row.solved then 1 else 0)
          goalCount := acc.goalCount + row.goalCount
          localDeclCount := acc.localDeclCount + row.localDeclCount
          exprConstructorCounts :=
            row.goals.foldl (fun inner goal => collectGoalCounts goal inner) acc.exprConstructorCounts })
      { rows := 0, solvedRows := 0, goalCount := 0, localDeclCount := 0, exprConstructorCounts := #[] }
  { rows := rows, summary := summary }

end ICCKernel
end LoF
end HeytingLean
