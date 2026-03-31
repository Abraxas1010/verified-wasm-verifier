import Lean
import Lean.Data.Json
import HeytingLean.LoF.Combinators.SKYMachineBounded
import HeytingLean.LoF.LeanKernel.Lean4LeanSKY

open Lean

namespace HeytingLean.CLI.SKYStageCore

open HeytingLean.LoF
open HeytingLean.LoF.Combinators
open HeytingLean.LoF.LeanKernel

structure InternState where
  nextId : Nat := 1
  names : Std.HashMap Name Nat := {}
  erasedUniversePayload : Bool := false
  erasedExprMetas : Bool := false
deriving Inhabited

abbrev OracleRef := Unit
abbrev SLevel := LeanKernel.ULevel Unit Unit
abbrev SExpr := LeanKernel.Expr Nat Unit Unit Unit
abbrev ConvertM := StateT InternState (Except String)

private def binderInfoToStaged : Lean.BinderInfo → LeanKernel.BinderInfo
  | .default => .default
  | .implicit => .implicit
  | .strictImplicit => .strictImplicit
  | .instImplicit => .instImplicit

private def stageLiteral : Lean.Literal → Except String LeanKernel.Literal
  | .natVal n => .ok (.natVal n)
  | .strVal s => .ok (.strVal s)

private def internName (n : Name) : ConvertM Nat := do
  let st ← get
  match st.names.get? n with
  | some id => pure id
  | none =>
      let id := st.nextId
      set { st with nextId := id + 1, names := st.names.insert n id }
      pure id

partial def stageLevel : Lean.Level → ConvertM SLevel
  | .zero => pure .zero
  | .succ u => return .succ (← stageLevel u)
  | .max a b => return .max (← stageLevel a) (← stageLevel b)
  | .imax a b => return .imax (← stageLevel a) (← stageLevel b)
  | .param _ => do
      modify fun st => { st with erasedUniversePayload := true }
      pure (.param ())
  | .mvar _ => do
      modify fun st => { st with erasedUniversePayload := true }
      pure (.mvar ())

partial def stageExpr : Lean.Expr → ConvertM SExpr
  | .bvar idx => pure (.bvar idx)
  | .mvar _ => do
      modify fun st => { st with erasedExprMetas := true }
      pure (.mvar ())
  | .sort u => return .sort (← stageLevel u)
  | .const n us =>
      return .const (← internName n) (← us.mapM stageLevel)
  | .app f a =>
      return .app (← stageExpr f) (← stageExpr a)
  | .lam n ty body bi =>
      return .lam (← internName n) (binderInfoToStaged bi) (← stageExpr ty) (← stageExpr body)
  | .forallE n ty body bi =>
      return .forallE (← internName n) (binderInfoToStaged bi) (← stageExpr ty) (← stageExpr body)
  | .letE n ty val body _ =>
      return .letE (← internName n) .default (← stageExpr ty) (← stageExpr val) (← stageExpr body)
  | .lit lit =>
      return .lit (← liftM (stageLiteral lit))
  | .mdata _ body => stageExpr body
  | .fvar fvarId => throw s!"unsupported fvar expression: {fvarId.name}"
  | .proj typeName idx body =>
      throw s!"unsupported proj expression: {typeName}.{idx} in {repr body}"

def stageExprWithState (st : InternState) (e : Lean.Expr) : Except String (SExpr × InternState) :=
  match (stageExpr e).run st with
  | .error err => .error err
  | .ok (expr, st') => .ok (expr, st')

def runMetaAtEnv (env : Lean.Environment) (x : MetaM α) : IO α := do
  let ctxCore : Core.Context := { fileName := "<sky_stage>", fileMap := default }
  let sCore : Core.State := { env := env }
  let (a, _, _) ← x.toIO ctxCore sCore
  pure a

partial def containsProj : Lean.Expr → Bool
  | .proj _ _ body => true || containsProj body
  | .app f a => containsProj f || containsProj a
  | .lam _ ty body _ => containsProj ty || containsProj body
  | .forallE _ ty body _ => containsProj ty || containsProj body
  | .letE _ ty val body _ => containsProj ty || containsProj val || containsProj body
  | .mdata _ body => containsProj body
  | _ => false

private def natLiteralExpr? : Lean.Expr → Option Nat
  | .app (.app (.app (.const ``OfNat.ofNat _) ty) nLit) inst =>
      if ty.isConstOf ``Nat then
        match nLit, inst with
        | .lit (.natVal n), .app (.const ``instOfNatNat _) kLit =>
            match kLit with
            | .lit (.natVal k) =>
                if n == k then some n else none
            | _ => none
        | _, _ => none
      else
        none
  | _ => none

private def isNatLiteralExpr (e : Lean.Expr) : Bool :=
  match natLiteralExpr? e with
  | some _ => true
  | none => false

partial def containsNatLiteralExpr : Lean.Expr → Bool
  | e@(.app f a) => isNatLiteralExpr e || containsNatLiteralExpr f || containsNatLiteralExpr a
  | e@(.lam _ ty body _) => isNatLiteralExpr e || containsNatLiteralExpr ty || containsNatLiteralExpr body
  | e@(.forallE _ ty body _) => isNatLiteralExpr e || containsNatLiteralExpr ty || containsNatLiteralExpr body
  | e@(.letE _ ty val body _) =>
      isNatLiteralExpr e || containsNatLiteralExpr ty || containsNatLiteralExpr val || containsNatLiteralExpr body
  | e@(.mdata _ body) => isNatLiteralExpr e || containsNatLiteralExpr body
  | e@(.proj _ _ body) => isNatLiteralExpr e || containsNatLiteralExpr body
  | e => isNatLiteralExpr e

def lowerProjExpr (env : Lean.Environment) (e : Lean.Expr) : IO (Except String Lean.Expr) := do
  if !(containsProj e || containsNatLiteralExpr e) then
    return Except.ok e
  try
    let lowered ← runMetaAtEnv env <|
      Meta.transform e (pre := fun term => do
        match natLiteralExpr? term with
        | some n =>
            return .visit (.lit (.natVal n))
        | none =>
            match term with
            | .proj structName idx body =>
                match structName with
                | ``PProd =>
                    let bodyType ← Lean.Meta.whnf (← Lean.Meta.inferType body)
                    match bodyType.getAppFn, bodyType.getAppArgs with
                    | .const ``PProd _, #[α, β] =>
                        let motiveBody ←
                          match idx with
                          | 0 => pure α
                          | 1 => pure β
                          | _ => throwError "invalid PProd projection index {idx}"
                        let u ←
                          match ← Lean.Meta.inferType α with
                          | .sort u => pure u
                          | other => throwError "expected a type for PProd first projection domain, got {other}"
                        let v ←
                          match ← Lean.Meta.inferType β with
                          | .sort v => pure v
                          | other => throwError "expected a type for PProd second projection domain, got {other}"
                        let uMotive ←
                          match ← Lean.Meta.inferType motiveBody with
                          | .sort uMotive => pure uMotive
                          | other => throwError "expected a sort-valued PProd projection motive, got {other}"
                        let pairTy := Lean.mkAppN (.const ``PProd [u, v]) #[α, β]
                        Lean.Meta.withLocalDeclD `pair pairTy fun pair => do
                          let motive ← Lean.Meta.mkLambdaFVars #[pair] motiveBody
                          Lean.Meta.withLocalDeclD `fst α fun fst => do
                            Lean.Meta.withLocalDeclD `snd β fun snd => do
                              let branch ←
                                match idx with
                                | 0 => pure fst
                                | 1 => pure snd
                                | _ => throwError "invalid PProd projection index {idx}"
                              let branchLam ← Lean.Meta.mkLambdaFVars #[fst, snd] branch
                              let reduced := Lean.mkAppN (.const ``PProd.casesOn [uMotive, u, v]) #[α, β, motive, body, branchLam]
                              return .visit reduced
                    | _, _ =>
                        throwError "unexpected PProd body type for projection lowering: {bodyType}"
                | ``And =>
                    let bodyType ← Lean.Meta.whnf (← Lean.Meta.inferType body)
                    match bodyType.getAppFn, bodyType.getAppArgs with
                    | .const ``And _, #[α, β] =>
                        let andTy := Lean.mkAppN (← Lean.Meta.mkConstWithFreshMVarLevels ``And) #[α, β]
                        Lean.Meta.withLocalDeclD `pair andTy fun pair => do
                          let motiveBody ←
                            match idx with
                            | 0 => pure α
                            | 1 => pure β
                            | _ => throwError "invalid And projection index {idx}"
                          let motive ← Lean.Meta.mkLambdaFVars #[pair] motiveBody
                          Lean.Meta.withLocalDeclD `left α fun left => do
                            Lean.Meta.withLocalDeclD `right β fun right => do
                              let branch ←
                                match idx with
                                | 0 => pure left
                                | 1 => pure right
                                | _ => throwError "invalid And projection index {idx}"
                              let branchLam ← Lean.Meta.mkLambdaFVars #[left, right] branch
                              let reduced := Lean.mkAppN (← Lean.Meta.mkConstWithFreshMVarLevels ``And.casesOn) #[α, β, motive, body, branchLam]
                              return .visit reduced
                    | _, _ =>
                        throwError "unexpected And body type for projection lowering: {bodyType}"
                | _ =>
                    let some info := Lean.getStructureInfo? (← getEnv) structName
                      | throwError "unknown structure for projection {structName}"
                    let some fieldName := info.fieldNames[idx]?
                      | throwError "invalid projection index {idx} for structure {structName}"
                    let some projFnName := info.getProjFn? idx
                      | throwError "missing projection function for field {fieldName} of {structName}"
                    match (← getEnv).getProjectionFnInfo? projFnName with
                    | some projInfo =>
                        let some (.ctorInfo _) := (← getEnv).find? projInfo.ctorName
                          | throwError "projection constructor {projInfo.ctorName} missing for {projFnName}"
                        let casesOnName := Name.str structName "casesOn"
                        if (← getEnv).find? casesOnName |>.isSome then
                          let bodyType ← Lean.Meta.whnf (← Lean.Meta.inferType body)
                          let ctorConst ← Lean.Meta.mkConstWithFreshMVarLevels projInfo.ctorName
                          let ctorApplied := Lean.mkAppN ctorConst bodyType.getAppArgs
                          let ctorType ← Lean.Meta.inferType ctorApplied
                          Lean.Meta.forallTelescopeReducing ctorType fun fieldFVars _ => do
                            let some selectedField := fieldFVars[idx]?
                              | throwError "constructor telescope too short for projection {projFnName}"
                            let selectedFieldTy ← Lean.Meta.inferType selectedField
                            if fieldFVars.any (fun fv => selectedFieldTy.containsFVar fv.fvarId!) then
                              return .visit (← Lean.Meta.mkProjection body fieldName)
                            let casesOnConst ← Lean.Meta.mkConstWithFreshMVarLevels casesOnName
                            Lean.Meta.withLocalDeclD `self bodyType fun self => do
                              let motive ← Lean.Meta.mkLambdaFVars #[self] selectedFieldTy
                              let branchLam ← Lean.Meta.mkLambdaFVars fieldFVars selectedField
                              let reduced := Lean.mkAppN casesOnConst (bodyType.getAppArgs ++ #[motive, body, branchLam])
                              return .visit reduced
                        else
                          return .visit (← Lean.Meta.mkProjection body fieldName)
                    | none =>
                        return .visit (← Lean.Meta.mkProjection body fieldName)
            | _ =>
                return .continue)
    return Except.ok lowered
  catch ex =>
    return Except.error s!"projection lowering failed: {ex}"

def nodeToJson (n : SKYGraph.Node OracleRef) : Json :=
  match n with
  | .combK => Json.mkObj [("tag", Json.str "K")]
  | .combS => Json.mkObj [("tag", Json.str "S")]
  | .combY => Json.mkObj [("tag", Json.str "Y")]
  | .app f a => Json.mkObj [("tag", Json.str "app"), ("f", toJson f), ("a", toJson a)]
  | .oracle _ => Json.mkObj [("tag", Json.str "oracle")]

def stateToJson (maxNodes fuel : Nat) (s : SKYMachineBounded.State OracleRef) : Json :=
  Json.mkObj
    [ ("maxNodes", toJson maxNodes)
    , ("fuel", toJson fuel)
    , ("nodesUsed", toJson s.nodes.size)
    , ("focus", toJson s.focus)
    , ("stack", toJson s.stack.toArray)
    , ("nodes", Json.arr (s.nodes.map nodeToJson))
    ]

def compileExprToStateJson
    (maxNodes fuel : Nat)
    (staged : SExpr) : Except String Json := do
  match Lean4LeanSKY.Machine.compileExprToState? (maxNodes := maxNodes) staged with
  | some s => pure (stateToJson maxNodes fuel s)
  | none => throw s!"out of heap during staged Expr compilation (maxNodes={maxNodes})"

def compileLeanExprToStateJson
    (env : Lean.Environment)
    (maxNodes fuel : Nat)
    (expr : Lean.Expr) : IO (Except String Json) := do
  let loweredResult ← lowerProjExpr env expr
  match loweredResult with
  | .error err => pure (.error err)
  | .ok lowered =>
      match stageExprWithState {} lowered with
      | .error err => pure (.error err)
      | .ok (staged, _) => pure (compileExprToStateJson maxNodes fuel staged)

end HeytingLean.CLI.SKYStageCore
