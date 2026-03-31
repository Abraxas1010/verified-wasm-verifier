import Lean
import Lean.Data.Json
import HeytingLean.CLI.LeanExprJson

open Lean

namespace HeytingLean
namespace ProofState

def binderInfoToString : BinderInfo → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

def binderInfoFromString? : String → Option BinderInfo
  | "default" => some .default
  | "implicit" => some .implicit
  | "strictImplicit" => some .strictImplicit
  | "instImplicit" => some .instImplicit
  | _ => none

structure LocalDeclSnapshot where
  index : Nat
  userName : String
  fvarId : String
  binderInfo : BinderInfo
  isImplementationDetail : Bool
  typeExpr : Expr
  valueExpr? : Option Expr
  typePP : String
  valuePP? : Option String
  deriving Inhabited, Repr, BEq

structure GoalSnapshot where
  goalId : String
  goalType : Expr
  goalTypePP : String
  localContext : Array LocalDeclSnapshot
  deriving Inhabited, Repr, BEq

structure GoalBatchSnapshot where
  goals : Array GoalSnapshot
  solved : Bool
  deriving Inhabited, Repr, BEq

structure ExtractionEnvelope where
  ok : Bool
  requestGoal : String
  appliedTactics : Array String
  snapshot : GoalBatchSnapshot
  stderr : String := ""
  extractionKind : String := "wrapper"
  sourceFile? : Option String := none
  sourceDecl? : Option String := none
  checkpointIndex? : Option Nat := none
  checkpointLabel? : Option String := none
  deriving Inhabited, Repr, BEq

private def expectField (j : Json) (name : String) : Except String Json :=
  j.getObjVal? name

private def expectString (j : Json) (name : String) : Except String String :=
  j.getObjValAs? String name

private def expectNat (j : Json) (name : String) : Except String Nat :=
  j.getObjValAs? Nat name

private def expectBool (j : Json) (name : String) : Except String Bool :=
  j.getObjValAs? Bool name

private def expectExpr (j : Json) (name : String) : Except String Expr := do
  let payload ← expectField j name
  HeytingLean.CLI.LeanExprJson.exprFromJson payload

private def expectExprOpt (j : Json) (name : String) : Except String (Option Expr) := do
  let payload ← expectField j name
  if payload == Json.null then
    pure none
  else
    return some (← HeytingLean.CLI.LeanExprJson.exprFromJson payload)

private def expectStringOpt (j : Json) (name : String) : Except String (Option String) := do
  let payload ← expectField j name
  match payload with
  | .null => pure none
  | .str s => pure (some s)
  | _ => throw s!"expected optional string field `{name}`"

private def getStringDefault (j : Json) (name : String) (fallback : String) : Except String String := do
  match j.getObjVal? name with
  | .ok (.str s) => pure s
  | .ok .null => pure fallback
  | .error _ => pure fallback
  | .ok _ => throw s!"expected string field `{name}`"

private def getStringOptDefault (j : Json) (name : String) : Except String (Option String) := do
  match j.getObjVal? name with
  | .ok .null => pure none
  | .ok (.str s) => pure (some s)
  | .error _ => pure none
  | .ok _ => throw s!"expected optional string field `{name}`"

private def getNatOptDefault (j : Json) (name : String) : Except String (Option Nat) := do
  match j.getObjVal? name with
  | .ok .null => pure none
  | .ok v =>
      match v.getNat? with
      | .ok k => pure (some k)
      | .error _ => throw s!"expected optional natural number field `{name}`"
  | .error _ => pure none

private def mapJsonArray {α} (j : Json) (ctx : String) (f : Json → Except String α) : Except String (Array α) := do
  match j with
  | .arr xs =>
      let mut out : Array α := #[]
      for x in xs do
        out := out.push (← f x)
      pure out
  | _ => throw s!"{ctx} must be an array"

def LocalDeclSnapshot.toJson (snap : LocalDeclSnapshot) : Json :=
  Json.mkObj
    [ ("index", Json.num snap.index)
    , ("userName", Json.str snap.userName)
    , ("fvarId", Json.str snap.fvarId)
    , ("binderInfo", Json.str (binderInfoToString snap.binderInfo))
    , ("isImplementationDetail", Json.bool snap.isImplementationDetail)
    , ("typeExpr", HeytingLean.CLI.LeanExprJson.exprToJson snap.typeExpr)
    , ("valueExpr", snap.valueExpr?.map HeytingLean.CLI.LeanExprJson.exprToJson |>.getD Json.null)
    , ("typePP", Json.str snap.typePP)
    , ("valuePP", snap.valuePP?.map Json.str |>.getD Json.null)
    ]

def LocalDeclSnapshot.fromJson (j : Json) : Except String LocalDeclSnapshot := do
  let binderInfoText ← expectString j "binderInfo"
  let some binderInfo := binderInfoFromString? binderInfoText
    | throw s!"unknown binderInfo `{binderInfoText}`"
  pure
    { index := (← expectNat j "index")
      userName := (← expectString j "userName")
      fvarId := (← expectString j "fvarId")
      binderInfo := binderInfo
      isImplementationDetail := (← expectBool j "isImplementationDetail")
      typeExpr := (← expectExpr j "typeExpr")
      valueExpr? := (← expectExprOpt j "valueExpr")
      typePP := (← expectString j "typePP")
      valuePP? := (← expectStringOpt j "valuePP") }

instance : ToJson LocalDeclSnapshot := ⟨LocalDeclSnapshot.toJson⟩

def GoalSnapshot.toJson (snap : GoalSnapshot) : Json :=
  Json.mkObj
    [ ("goalId", Json.str snap.goalId)
    , ("goalType", HeytingLean.CLI.LeanExprJson.exprToJson snap.goalType)
    , ("goalTypePP", Json.str snap.goalTypePP)
    , ("localContext", Json.arr (snap.localContext.map LocalDeclSnapshot.toJson))
    ]

def GoalSnapshot.fromJson (j : Json) : Except String GoalSnapshot := do
  pure
    { goalId := (← expectString j "goalId")
      goalType := (← expectExpr j "goalType")
      goalTypePP := (← expectString j "goalTypePP")
      localContext := (← mapJsonArray (← expectField j "localContext") "localContext" LocalDeclSnapshot.fromJson) }

instance : ToJson GoalSnapshot := ⟨GoalSnapshot.toJson⟩

def GoalBatchSnapshot.toJson (snap : GoalBatchSnapshot) : Json :=
  Json.mkObj
    [ ("goals", Json.arr (snap.goals.map GoalSnapshot.toJson))
    , ("solved", Json.bool snap.solved)
    ]

def GoalBatchSnapshot.fromJson (j : Json) : Except String GoalBatchSnapshot := do
  pure
    { goals := (← mapJsonArray (← expectField j "goals") "goals" GoalSnapshot.fromJson)
      solved := (← expectBool j "solved") }

instance : ToJson GoalBatchSnapshot := ⟨GoalBatchSnapshot.toJson⟩

def ExtractionEnvelope.toJson (env : ExtractionEnvelope) : Json :=
  Json.mkObj
    [ ("ok", Json.bool env.ok)
    , ("requestGoal", Json.str env.requestGoal)
    , ("appliedTactics", Json.arr (env.appliedTactics.map Json.str))
    , ("snapshot", env.snapshot.toJson)
    , ("stderr", Json.str env.stderr)
    , ("extractionKind", Json.str env.extractionKind)
    , ("sourceFile", env.sourceFile?.map Json.str |>.getD Json.null)
    , ("sourceDecl", env.sourceDecl?.map Json.str |>.getD Json.null)
    , ("checkpointIndex", env.checkpointIndex?.map Json.num |>.getD Json.null)
    , ("checkpointLabel", env.checkpointLabel?.map Json.str |>.getD Json.null)
    ]

def ExtractionEnvelope.fromJson (j : Json) : Except String ExtractionEnvelope := do
  let applied :=
    ← mapJsonArray (← expectField j "appliedTactics") "appliedTactics" fun item =>
      match item with
      | .str s => pure s
      | _ => throw "appliedTactics entries must be strings"
  pure
    { ok := (← expectBool j "ok")
      requestGoal := (← expectString j "requestGoal")
      appliedTactics := applied
      snapshot := (← GoalBatchSnapshot.fromJson (← expectField j "snapshot"))
      stderr := (← expectString j "stderr")
      extractionKind := (← getStringDefault j "extractionKind" "wrapper")
      sourceFile? := (← getStringOptDefault j "sourceFile")
      sourceDecl? := (← getStringOptDefault j "sourceDecl")
      checkpointIndex? := (← getNatOptDefault j "checkpointIndex")
      checkpointLabel? := (← getStringOptDefault j "checkpointLabel") }

instance : ToJson ExtractionEnvelope := ⟨ExtractionEnvelope.toJson⟩

def snapshotLocalDecl (idx : Nat) (decl : LocalDecl) : MetaM LocalDeclSnapshot := do
  let typePP := (← Lean.Meta.ppExpr decl.type).pretty
  let valuePP? ←
    match decl.value? with
    | some value => pure (some (← Lean.Meta.ppExpr value).pretty)
    | none => pure none
  pure
    { index := idx
      userName := decl.userName.toString
      fvarId := decl.fvarId.name.toString
      binderInfo := decl.binderInfo
      isImplementationDetail := decl.isImplementationDetail
      typeExpr := decl.type
      valueExpr? := decl.value?
      typePP := typePP
      valuePP? := valuePP? }

def snapshotGoal (goal : MVarId) : MetaM GoalSnapshot := do
  goal.withContext do
    let goalType ← goal.getType
    let goalTypePP := (← Lean.Meta.ppExpr goalType).pretty
    let lctx ← Lean.getLCtx
    let mut locals : Array LocalDeclSnapshot := #[]
    let mut idx := 0
    for decl in lctx do
      locals := locals.push (← snapshotLocalDecl idx decl)
      idx := idx + 1
    pure
      { goalId := goal.name.toString
        goalType := goalType
        goalTypePP := goalTypePP
        localContext := locals }

def snapshotGoals (goals : List MVarId) : MetaM GoalBatchSnapshot := do
  let mut snapshots : Array GoalSnapshot := #[]
  for goal in goals do
    snapshots := snapshots.push (← snapshotGoal goal)
  pure { goals := snapshots, solved := goals.isEmpty }

def readExtractionEnvelopeFile (path : System.FilePath) : IO ExtractionEnvelope := do
  let contents ← IO.FS.readFile path
  let json ←
    match Json.parse contents with
    | .ok j => pure j
    | .error err => throw <| IO.userError s!"failed to parse extraction envelope `{path}`: {err}"
  match ExtractionEnvelope.fromJson json with
  | .ok env => pure env
  | .error err => throw <| IO.userError s!"failed to decode extraction envelope `{path}`: {err}"

end ProofState
end HeytingLean
