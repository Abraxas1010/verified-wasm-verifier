import Lean.Data.Json
import HeytingLean.CLI.SKYStageCore
import HeytingLean.LoF.ICC.Encoder.DeclWalker
import HeytingLean.LoF.LeanKernel.Environment
import HeytingLean.LoF.LeanKernel.Expression
import HeytingLean.LoF.LeanKernel.Infer
import HeytingLean.LoF.LeanKernel.WHNF

namespace HeytingLean
namespace LoF
namespace ICC
namespace Encoder

open Lean
open HeytingLean.CLI.SKYStageCore
open HeytingLean.LoF.LeanKernel

abbrev SEnv := Environment.Env Nat Nat Nat Nat
abbrev SExpr := Expr Nat Nat Nat Nat
abbrev SConstDecl := Environment.ConstDecl Nat Nat Nat Nat
abbrev SCtx := Infer.Ctx Nat Nat Nat Nat
abbrev SConfig := Infer.Config Nat Nat Nat Nat

structure SemanticStageState where
  nextNameId : Nat := 1
  names : Std.HashMap Name Nat := {}
  nextLevelParamId : Nat := 1
  levelParams : Std.HashMap Name Nat := {}
  nextLevelMVarId : Nat := 1
  levelMVars : Std.HashMap String Nat := {}
  nextExprMVarId : Nat := 1
  exprMVars : Std.HashMap String Nat := {}
  erasedUniversePayload : Bool := false
  erasedExprMetas : Bool := false
deriving Inhabited

inductive SemanticGateStatus where
  | success
  | blocked
  | notApplicable
  deriving DecidableEq, Repr

def SemanticGateStatus.code : SemanticGateStatus → String
  | .success => "success"
  | .blocked => "blocked"
  | .notApplicable => "not_applicable"

structure SemanticGateEvidence where
  stagedEnvConstCount : Nat
  closureSize : Nat
  stagedNameTable : Array String := #[]
  declTypeWellTyped : Bool
  declTypeDiagnostic : Option String := none
  inferValueSucceeded : Bool
  inferValueDiagnostic : Option String := none
  checkValue : Bool
  targetTypeStagedNodes : Nat
  targetValueStagedNodes : Nat
  whnfTypeStagedNodes : Nat
  whnfValueStagedNodes : Nat
  inferredTypeStagedNodes : Option Nat := none
  inferredTypeWhnfStagedNodes : Option Nat := none
  erasedUniversePayload : Bool
  erasedExprMetas : Bool
  fuel : Nat
  maxConsts : Nat
  deriving Repr

structure SemanticGateAttempt where
  status : SemanticGateStatus
  reason : String
  detail : String
  evidence? : Option SemanticGateEvidence := none
  trustAssumptions : List String := []
  deriving Repr

private def natConstName : Name := `Nat
private def stringConstName : Name := `String

private abbrev StageM := StateT SemanticStageState (Except String)

private def stageLiteral : Lean.Literal → Except String LeanKernel.Literal
  | .natVal n => .ok (.natVal n)
  | .strVal s => .ok (.strVal s)

private def internName (n : Name) : StageM Nat := do
  let st ← get
  match st.names.get? n with
  | some id => pure id
  | none =>
      let id := st.nextNameId
      set { st with nextNameId := id + 1, names := st.names.insert n id }
      pure id

private def internLevelParam (n : Name) : StageM Nat := do
  let st ← get
  match st.levelParams.get? n with
  | some id => pure id
  | none =>
      let id := st.nextLevelParamId
      set { st with nextLevelParamId := id + 1, levelParams := st.levelParams.insert n id }
      pure id

private def internLevelMVar (key : String) : StageM Nat := do
  let st ← get
  match st.levelMVars.get? key with
  | some id => pure id
  | none =>
      let id := st.nextLevelMVarId
      set { st with nextLevelMVarId := id + 1, levelMVars := st.levelMVars.insert key id }
      pure id

private def internExprMVar (key : String) : StageM Nat := do
  let st ← get
  match st.exprMVars.get? key with
  | some id => pure id
  | none =>
      let id := st.nextExprMVarId
      set { st with nextExprMVarId := id + 1, exprMVars := st.exprMVars.insert key id }
      pure id

private partial def stageLevel : Lean.Level → StageM (LeanKernel.ULevel Nat Nat)
  | .zero => pure .zero
  | .succ u => return .succ (← stageLevel u)
  | .max a b => return .max (← stageLevel a) (← stageLevel b)
  | .imax a b => return .imax (← stageLevel a) (← stageLevel b)
  | .param n => return .param (← internLevelParam n)
  | .mvar m => return .mvar (← internLevelMVar (reprStr m))

private def binderInfoToStaged : Lean.BinderInfo → LeanKernel.BinderInfo
  | .default => .default
  | .implicit => .implicit
  | .strictImplicit => .strictImplicit
  | .instImplicit => .instImplicit

private partial def stageExpr : Lean.Expr → StageM SExpr
  | .bvar idx => pure (.bvar idx)
  | .mvar m => return .mvar (← internExprMVar (reprStr m))
  | .sort u => return .sort (← stageLevel u)
  | .const n us => return .const (← internName n) (← us.mapM stageLevel)
  | .app f a => return .app (← stageExpr f) (← stageExpr a)
  | .lam n ty body bi =>
      return .lam (← internName n) (binderInfoToStaged bi) (← stageExpr ty) (← stageExpr body)
  | .forallE n ty body bi =>
      return .forallE (← internName n) (binderInfoToStaged bi) (← stageExpr ty) (← stageExpr body)
  | .letE n ty val body _ =>
      return .letE (← internName n) .default (← stageExpr ty) (← stageExpr val) (← stageExpr body)
  | .lit lit => return .lit (← liftM (stageLiteral lit))
  | .mdata _ body => stageExpr body
  | .fvar fvarId => throw s!"unsupported fvar expression: {fvarId.name}"
  | .proj typeName idx body =>
      throw s!"unsupported proj expression: {typeName}.{idx} in {repr body}"

private def stageWithState
    (st : SemanticStageState)
    (expr : Lean.Expr) : Except String (SExpr × SemanticStageState) :=
  match (stageExpr expr).run st with
  | .error err => .error err
  | .ok (expr', st') => .ok (expr', st')

private def internLevelParamsWithState
    (st : SemanticStageState)
    (params : List Name) : Except String (List Nat × SemanticStageState) :=
  match (params.mapM internLevelParam).run st with
  | .error err => .error err
  | .ok (ids, st') => .ok (ids, st')

private def lookupLevelAssignment
    (assignments : List (Nat × LeanKernel.ULevel Nat Nat))
    (paramId : Nat) : Option (LeanKernel.ULevel Nat Nat) :=
  assignments.findSome? fun (id, u) =>
    if id == paramId then some u else none

private partial def instantiateLevelParams
    (assignments : List (Nat × LeanKernel.ULevel Nat Nat)) :
    LeanKernel.ULevel Nat Nat → LeanKernel.ULevel Nat Nat
  | .zero => .zero
  | .succ u => .succ (instantiateLevelParams assignments u)
  | .max a b => .max (instantiateLevelParams assignments a) (instantiateLevelParams assignments b)
  | .imax a b => .imax (instantiateLevelParams assignments a) (instantiateLevelParams assignments b)
  | .param p => (lookupLevelAssignment assignments p).getD (.param p)
  | .mvar m => .mvar m

private partial def instantiateExprLevelParams
    (assignments : List (Nat × LeanKernel.ULevel Nat Nat)) :
    SExpr → SExpr
  | .bvar i => .bvar i
  | .mvar m => .mvar m
  | .sort u => .sort (instantiateLevelParams assignments u)
  | .const c us => .const c (us.map (instantiateLevelParams assignments))
  | .app f a => .app (instantiateExprLevelParams assignments f) (instantiateExprLevelParams assignments a)
  | .lam n bi ty body =>
      .lam n bi (instantiateExprLevelParams assignments ty) (instantiateExprLevelParams assignments body)
  | .forallE n bi ty body =>
      .forallE n bi (instantiateExprLevelParams assignments ty) (instantiateExprLevelParams assignments body)
  | .letE n bi ty val body =>
      .letE n bi
        (instantiateExprLevelParams assignments ty)
        (instantiateExprLevelParams assignments val)
        (instantiateExprLevelParams assignments body)
  | .lit l => .lit l

private def internConstName
    (st : SemanticStageState)
    (name : Name) : Except String (Nat × SemanticStageState) := do
  let (expr, st') ← stageWithState st (.const name [])
  match expr with
  | .const id _ => pure (id, st')
  | _ => throw s!"internal semantic-gate error while interning {name}"

private def recursorCasesOnSpec?
    (env : Environment)
    (name : Name) : Option (Name × Nat × Nat × List (Name × Nat × Nat × List Nat)) := do
  let rec binderTypesOf (type : Lean.Expr) : List Lean.Expr :=
    let rec binderGo : Lean.Expr → List Lean.Expr
      | .forallE _ ty body _ => ty :: binderGo body
      | _ => []
    binderGo type
  let casesOnRecName? : Name → Option Name
    | .str pre "casesOn" => some (Name.str pre "rec")
    | _ => none
  let currentConst ← env.find? name
  let (r, firstMinorIdx, majorIdx, recursorBinderTypes) ←
    match currentConst with
    | .recInfo r =>
        some (r, r.getFirstMinorIdx, r.getMajorIdx, binderTypesOf r.type)
    | _ =>
        let recName ← casesOnRecName? name
        let some (.recInfo r) := env.find? recName | none
        some (r, r.getFirstMinorIdx + 1, r.getFirstMinorIdx, binderTypesOf currentConst.type)
  let some (.inductInfo ind) := env.find? r.getMajorInduct | none
  let rec minorBinderCount : Lean.Expr → Nat
    | .forallE _ _ body _ => minorBinderCount body + 1
    | _ => 0
  let rec headConstName? : Lean.Expr → Option Name
    | .const n _ => some n
    | .app f _ => headConstName? f
    | _ => none
  let ctorFieldTypes (ctor : ConstructorVal) : List Lean.Expr :=
    let rec fieldGo : Nat → Lean.Expr → List Lean.Expr
      | 0, _ => []
      | n + 1, .forallE _ ty body _ => ty :: fieldGo n body
      | _, _ => []
    fieldGo (ctor.numParams + ctor.numFields) ctor.type |>.drop ctor.numParams
  let indexedCtors := List.zip (List.range ind.ctors.length) ind.ctors
  let ctors ←
    indexedCtors.mapM fun (idx, ctorName) => do
      let some (.ctorInfo ctor) := env.find? ctorName | none
      let fieldTypes := ctorFieldTypes ctor
      let recursiveFieldPositions :=
        (List.zip (List.range fieldTypes.length) fieldTypes).filterMap fun (fieldIdx, fieldTy) =>
          match headConstName? fieldTy with
          | some head => if head == ctor.induct then some fieldIdx else none
          | none => none
      let minorArgCount :=
        match recursorBinderTypes[r.getFirstMinorIdx + idx]? with
        | some ty => minorBinderCount ty
        | none => ctor.numFields
      let recursiveHyps :=
        if minorArgCount == ctor.numFields + recursiveFieldPositions.length then
          recursiveFieldPositions
        else
          []
      some (ctorName, ctor.numParams, ctor.numFields, recursiveHyps)
  some (name, firstMinorIdx, majorIdx, ctors)

private def semanticCasesOnSpecs
    (env : Environment)
    (seeds : Array Name)
    (st : SemanticStageState) : Except String (List (Inductive.CasesOnSpec Nat) × SemanticStageState) := do
  let recSpecs :=
    seeds.foldl (init := ([] : List (Name × Nat × Nat × List (Name × Nat × Nat × List Nat)))) fun acc name =>
      match recursorCasesOnSpec? env name with
      | some spec => if acc.contains spec then acc else spec :: acc
      | none => acc
  recSpecs.foldlM
    (init := (([] : List (Inductive.CasesOnSpec Nat)), st))
    fun (acc : List (Inductive.CasesOnSpec Nat) × SemanticStageState) (spec : Name × Nat × Nat × List (Name × Nat × Nat × List Nat)) => do
      let (out, currState) := acc
      let (recName, firstMinorIdx, majorIdx, ctors) := spec
      let (recId, st1) ← internConstName currState recName
      let ((ctorSpecsRev, stFinal)) ←
        ctors.foldlM
          (init := (([] : List (Inductive.CtorSpec Nat)), st1))
          fun (acc2 : List (Inductive.CtorSpec Nat) × SemanticStageState) (entry : Name × Nat × Nat × List Nat) => do
            let (ctorAcc, ctorState) := acc2
            let (ctorName, ctorParams, numFields, recursiveFields) := entry
            let (ctorId, nextState) ← internConstName ctorState ctorName
            pure ({ name := ctorId, numParams := ctorParams, numFields := numFields, recursiveFieldPositions := recursiveFields } :: ctorAcc, nextState)
      let built : Inductive.CasesOnSpec Nat :=
        { recursor := recId
          firstMinorIdx := firstMinorIdx
          majorIdx := majorIdx
          ctors := ctorSpecsRev.reverse }
      pure (built :: out, stFinal)

private def pushUnique (xs : Array Name) (name : Name) : Array Name :=
  if xs.contains name then xs else xs.push name

private def semanticConstValueExpr? : ConstantInfo → Option Lean.Expr
  | .defnInfo info => some info.value
  | .opaqueInfo _ => none
  | .thmInfo _ => none
  | _ => none

private def loweredConstPayload
    (env : Environment)
    (name : Name)
    (ci : ConstantInfo)
    (targetName : Name) : IO (Except String (Lean.Expr × Option Lean.Expr)) := do
  let scopedLevelParam (param : Name) : Name :=
    Name.str name s!"level_{param}"
  let scopedLevels := ci.levelParams.map (fun param => Lean.Level.param (scopedLevelParam param))
  let scopedType := ci.type.instantiateLevelParams ci.levelParams scopedLevels
  let typeResult ← lowerProjExpr env scopedType
  match typeResult with
  | .error err => pure (.error s!"while lowering {name}: {err}")
  | .ok loweredType =>
      if name == targetName then
        pure (.ok (loweredType, none))
      else
        match semanticConstValueExpr? ci with
        | none => pure (.ok (loweredType, none))
        | some value =>
            let scopedValue := value.instantiateLevelParams ci.levelParams scopedLevels
            let valueResult ← lowerProjExpr env scopedValue
            match valueResult with
            | .error err => pure (.error s!"while lowering {name}: {err}")
            | .ok loweredValue => pure (.ok (loweredType, some loweredValue))

private def buildSemanticEnv
    (env : Environment)
    (summary : DeclSummary)
    (ci : ConstantInfo) : IO (Except String (SEnv × SExpr × SExpr × SemanticStageState)) := do
  let some value := constantValueExpr? ci
    | pure (.error s!"{summary.declName} has no visible value/proof body for staged semantic checking")
  let loweredTypeResult ← lowerProjExpr env ci.type
  let loweredValueResult ← lowerProjExpr env value
  match loweredTypeResult, loweredValueResult with
  | .error err, _ => pure (.error err)
  | _, .error err => pure (.error err)
  | .ok loweredType, .ok loweredValue =>
      let mut normalizedDecls : Array (Name × List Name × Lean.Expr × Option Lean.Expr) := #[]
      let targetRefs :=
        (collectConstRefs loweredValue (collectConstRefs loweredType {})).toList
      let mut seen : Std.HashSet Name := {}
      let mut queue : List Name := summary.declName :: targetRefs
      while !queue.isEmpty do
        match queue with
        | [] => pure ()
        | name :: rest =>
            queue := rest
            if seen.contains name then
              pure ()
            else
              seen := seen.insert name
              match env.find? name with
              | none => pure ()
              | some depCi =>
                  let scopedLevelParams := depCi.levelParams.map (fun param => Name.str name s!"level_{param}")
                  match ← loweredConstPayload env name depCi summary.declName with
                  | .error err => return .error err
                  | .ok payload =>
                      let (depType, depValue?) := payload
                      normalizedDecls := normalizedDecls.push (name, scopedLevelParams, depType, depValue?)
                      let loweredRefs :=
                        match depValue? with
                        | some depValue =>
                            collectConstRefs depValue (collectConstRefs depType {})
                        | none =>
                            collectConstRefs depType {}
                      for dep in loweredRefs.toList do
                        if !seen.contains dep then
                          queue := dep :: queue
      let seeds :=
        normalizedDecls.foldl (init := #[natConstName, stringConstName]) fun acc entry =>
          pushUnique acc entry.1
      let convert : Except String (SEnv × SExpr × SExpr × SemanticStageState) := do
        let (targetType', st1) ← stageWithState {} loweredType
        let (targetValue', st2) ← stageWithState st1 loweredValue
        let (natId, st3) ← internConstName st2 natConstName
        let (stringId, st4) ← internConstName st3 stringConstName
        let (casesOnSpecs, st5) ← semanticCasesOnSpecs env seeds st4
        let litTypeFn := fun lit =>
          match lit with
          | LeanKernel.Literal.natVal _ => some (.const natId [])
          | LeanKernel.Literal.strVal _ => some (.const stringId [])
        let initEnv : SEnv :=
          { beqName := fun a b => a == b
            consts := []
            casesOnSpecs := casesOnSpecs
            mvarType? := fun _ => none
            litType? := litTypeFn
          }
        let (senv, stFinal) ←
          normalizedDecls.foldlM
            (init := (initEnv, st5))
            fun (acc : SEnv × SemanticStageState) (entry : Name × List Name × Lean.Expr × Option Lean.Expr) => do
              let (currEnv, currState) := acc
              let (name, levelParams, depType, depValue?) := entry
              let (levelParamIds, stParams) ← internLevelParamsWithState currState levelParams
              let (stagedName, stName) ← internConstName stParams name
              let (stagedType, stType) ← stageWithState stName depType
              let (stagedValue?, stValue) ←
                match depValue? with
                | none => pure (none, stType)
                | some depValue =>
                    let (stagedValue, st') ← stageWithState stType depValue
                    pure (some stagedValue, st')
              let instantiateWith (us : List (LeanKernel.ULevel Nat Nat)) (expr : SExpr) : SExpr :=
                instantiateExprLevelParams (levelParamIds.zip us) expr
              let decl : SConstDecl :=
                match stagedValue? with
                | some stagedValue =>
                    { name := stagedName
                      type := fun us => instantiateWith us stagedType
                      value? := some (fun us => instantiateWith us stagedValue) }
                | none =>
                    { name := stagedName
                      type := fun us => instantiateWith us stagedType
                      value? := none }
              pure (currEnv.addConst decl, stValue)
        pure (senv, targetType', targetValue', stFinal)
      pure convert

private def semanticGateTrustAssumptions
    (summary : DeclSummary)
    (st : SemanticStageState) : List String :=
  let base := ["direct_decl_body_staging", "staged_kernel_infer_check_whnf"]
  let base :=
    if st.erasedUniversePayload then
      "universe_payload_erased" :: base
    else
      base
  let base :=
    if st.erasedExprMetas then
      "expr_metas_erased" :: base
    else
      base
  let base :=
    if summary.closureOverflow then
      "closure_truncated" :: base
    else
      base
  let base :=
    if summary.missingDeps.isEmpty then
      base
    else
      "missing_dependency" :: base
  base.reverse.eraseDups

private def stagedNameTable (st : SemanticStageState) : Array String :=
  (st.names.toList.toArray.qsort (fun a b => a.2 < b.2)).map (fun (name, id) => s!"{id}:{name}")

private def exprTag : SExpr → String
  | .bvar _ => "bvar"
  | .mvar _ => "mvar"
  | .sort _ => "sort"
  | .const _ _ => "const"
  | .app _ _ => "app"
  | .lam _ _ _ _ => "lam"
  | .forallE _ _ _ _ => "forallE"
  | .letE _ _ _ _ _ => "letE"
  | .lit _ => "lit"

private def truncateDiagnostic (s : String) (limit : Nat := 2000) : String :=
  if s.length <= limit then s else s.take limit ++ "..."

private def exprBrief (e : SExpr) (limit : Nat := 2000) : String :=
  truncateDiagnostic s!"{exprTag e}:{reprStr e}" limit

mutual
  private def defEqDiagnostic
      (cfg : SConfig) :
      Nat → SExpr → SExpr → String
    | 0, e1, e2 =>
        s!"defeq_fuel_exhausted[lhs={exprBrief e1 400}, rhs={exprBrief e2 400}]"
    | fuel + 1, e1, e2 =>
        if DefEq.isDefEqWithDelta cfg.constValue? cfg.iotaRules (fuel + 1) e1 e2 then
          "defeq_ok"
        else
          let w1 := WHNF.whnfWithDelta cfg.constValue? cfg.iotaRules (fuel + 1) e1
          let w2 := WHNF.whnfWithDelta cfg.constValue? cfg.iotaRules (fuel + 1) e2
          match w1, w2 with
          | .app f a, .app g b =>
              if !(DefEq.isDefEqWithDelta cfg.constValue? cfg.iotaRules (fuel + 1) f g) then
                s!"defeq_fn[{defEqDiagnostic cfg fuel f g}]"
              else
                s!"defeq_arg[{defEqDiagnostic cfg fuel a b}]"
          | .lam _ _ ty body, .lam _ _ ty' body' =>
              if !(DefEq.isDefEqWithDelta cfg.constValue? cfg.iotaRules (fuel + 1) ty ty') then
                s!"defeq_lam_type[{defEqDiagnostic cfg fuel ty ty'}]"
              else
                s!"defeq_lam_body[{defEqDiagnostic cfg fuel body body'}]"
          | .forallE _ _ ty body, .forallE _ _ ty' body' =>
              if !(DefEq.isDefEqWithDelta cfg.constValue? cfg.iotaRules (fuel + 1) ty ty') then
                s!"defeq_forall_type[{defEqDiagnostic cfg fuel ty ty'}]"
              else
                s!"defeq_forall_body[{defEqDiagnostic cfg fuel body body'}]"
          | .const c us, .const d vs =>
              s!"defeq_const_mismatch[lhs={c}:{reprStr us}, rhs={d}:{reprStr vs}]"
          | .sort u, .sort v =>
              s!"defeq_sort_mismatch[lhs={reprStr u}, rhs={reprStr v}]"
          | _, _ =>
              s!"defeq_shape_mismatch[lhs={exprBrief w1 600}, rhs={exprBrief w2 600}]"

  private def inferDiagnostic
      (cfg : SConfig) :
      Nat → SCtx → SExpr → Except String SExpr
    | 0, _, _ => .error "fuel_exhausted"
    | fuel + 1, ctx, e =>
        match e with
        | .bvar i =>
            match ctx.bvarType? i with
            | some ty => .ok ty
            | none => .error s!"bvar_out_of_scope[{i}]"
        | .mvar m =>
            match cfg.mvarType? m with
            | some ty => .ok ty
            | none => .error s!"mvar_type_missing[{m}]"
        | .lit l =>
            match cfg.litType? l with
            | some ty => .ok ty
            | none => .error s!"literal_type_missing[{repr l}]"
        | .sort u => .ok (.sort (.succ u))
        | .const c us =>
            match cfg.constType? c us with
            | some ty => .ok ty
            | none => .error s!"const_type_missing[{c}]"
        | .app f a => do
            let tf ← (inferDiagnostic cfg fuel ctx f)
              |>.mapError (fun err => s!"app_fn({exprTag f},size={Expr.size f}): {err}")
            let tfWhnf := WHNF.whnfWithDelta cfg.constValue? cfg.iotaRules (fuel + 1) tf
            match tfWhnf with
            | .forallE _ _ dom body =>
                let ta ← (inferDiagnostic cfg fuel ctx a)
                  |>.mapError (fun err => s!"app_arg({exprTag a},size={Expr.size a}): {err}")
                if DefEq.isDefEqWithDelta cfg.constValue? cfg.iotaRules (fuel + 1) ta dom then
                  .ok (Expr.instantiate1 a body)
                else
                  let taWhnf := WHNF.whnfWithDelta cfg.constValue? cfg.iotaRules (fuel + 1) ta
                  let domWhnf := WHNF.whnfWithDelta cfg.constValue? cfg.iotaRules (fuel + 1) dom
                  let defeqDiag := defEqDiagnostic cfg fuel ta dom
                  .error s!"app_arg_type_mismatch[arg={exprTag a}/size={Expr.size a}, inferred={exprBrief ta 2000}/size={Expr.size ta}, expected={exprBrief dom 2000}/size={Expr.size dom}, inferred_whnf={exprBrief taWhnf 2000}/size={Expr.size taWhnf}, expected_whnf={exprBrief domWhnf 2000}/size={Expr.size domWhnf}, defeq={defeqDiag}]"
            | other =>
                .error s!"app_fn_not_pi[whnf={exprTag other},size={Expr.size other}]"
        | .lam _ _ ty body => do
            let _ ← (inferSortDiagnostic cfg fuel ctx ty)
              |>.mapError (fun err => s!"lam_binder_type(size={Expr.size ty}): {err}")
            let bodyTy ← (inferDiagnostic cfg fuel (ctx.extend ty) body)
              |>.mapError (fun err => s!"lam_body(size={Expr.size body}): {err}")
            .ok (.forallE 0 .default ty bodyTy)
        | .forallE _ _ ty body => do
            let u ← (inferSortDiagnostic cfg fuel ctx ty)
              |>.mapError (fun err => s!"forall_binder_type(size={Expr.size ty}): {err}")
            let v ← (inferSortDiagnostic cfg fuel (ctx.extend ty) body)
              |>.mapError (fun err => s!"forall_body(size={Expr.size body}): {err}")
            .ok (.sort (.imax u v))
        | .letE _ _ ty val body => do
            let _ ← (inferSortDiagnostic cfg fuel ctx ty)
              |>.mapError (fun err => s!"let_type(size={Expr.size ty}): {err}")
            let tVal ← (inferDiagnostic cfg fuel ctx val)
              |>.mapError (fun err => s!"let_value(size={Expr.size val}): {err}")
            if DefEq.isDefEqWithDelta cfg.constValue? cfg.iotaRules (fuel + 1) tVal ty then
              let bodyTy ← (inferDiagnostic cfg fuel (ctx.extend ty) body)
                |>.mapError (fun err => s!"let_body(size={Expr.size body}): {err}")
              .ok (Expr.instantiate1 val bodyTy)
            else
              let tValWhnf := WHNF.whnfWithDelta cfg.constValue? cfg.iotaRules (fuel + 1) tVal
              let tyWhnf := WHNF.whnfWithDelta cfg.constValue? cfg.iotaRules (fuel + 1) ty
              .error s!"let_value_type_mismatch[inferred={exprBrief tVal 2000}/size={Expr.size tVal}, expected={exprBrief ty 2000}/size={Expr.size ty}, inferred_whnf={exprBrief tValWhnf 2000}/size={Expr.size tValWhnf}, expected_whnf={exprBrief tyWhnf 2000}/size={Expr.size tyWhnf}]"

  private def inferSortDiagnostic
      (cfg : SConfig) :
      Nat → SCtx → SExpr → Except String (LeanKernel.ULevel Nat Nat)
    | 0, _, _ => .error "fuel_exhausted"
    | fuel + 1, ctx, e =>
        match inferDiagnostic cfg fuel ctx e with
        | .ok (.sort u) => .ok u
        | .ok other => .error s!"not_a_sort[got={exprTag other},size={Expr.size other}]"
        | .error err => .error err
end

def semanticGateAttempt
    (env : Environment)
    (summary : DeclSummary)
    (ci : ConstantInfo)
    (maxConsts : Nat := 8192)
    (fuel : Nat := 16384) : IO SemanticGateAttempt := do
  match summary.declKind with
  | "theorem" | "definition" | "opaque" =>
      if summary.closureOverflow then
        pure
          { status := .blocked
            reason := "semantic_gate_closure_overflow"
            detail := s!"{summary.declName} cannot yet claim staged-kernel semantic executability because its dependency closure overflowed the current cap."
            trustAssumptions := ["closure_truncated"] }
      else if !summary.missingDeps.isEmpty then
        pure
          { status := .blocked
            reason := "semantic_gate_missing_dependencies"
            detail := s!"{summary.declName} cannot yet claim staged-kernel semantic executability because required dependencies are missing from the imported environment."
            trustAssumptions := ["missing_dependency"] }
      else
        IO.eprintln s!"[semanticGateAttempt] buildSemanticEnv {summary.declName}"
        match ← buildSemanticEnv env summary ci with
        | .error err =>
            pure
              { status := .blocked
                reason := "semantic_gate_staging_failed"
                detail := s!"{summary.declName} did not build a coherent staged semantic environment: {err}" }
        | .ok (senv, targetType, targetValue, st) =>
            IO.eprintln s!"[semanticGateAttempt] whnf {summary.declName}"
            let cfg : SConfig := senv.toInferConfig
            let ctx : SCtx := Infer.Ctx.empty
            let typeWhnf := WHNF.whnfWithDelta cfg.constValue? cfg.iotaRules fuel targetType
            let valueWhnf := WHNF.whnfWithDelta cfg.constValue? cfg.iotaRules fuel targetValue
            IO.eprintln s!"[semanticGateAttempt] infer {summary.declName}"
            let inferredType? := Infer.infer? cfg fuel ctx targetValue
            let inferredTypeWhnf? := inferredType?.map (WHNF.whnfWithDelta cfg.constValue? cfg.iotaRules fuel)
            let declTypeWellTyped := (Infer.infer? cfg fuel ctx targetType).isSome
            let declTypeDiagnostic :=
              if declTypeWellTyped then
                none
              else
                match inferDiagnostic cfg fuel ctx targetType with
                | .ok _ => some "decl_type_infer_failed_without_local_diagnostic"
                | .error err => some err
            let inferValueDiagnostic :=
              if inferredType?.isSome then
                none
              else
                match inferDiagnostic cfg fuel ctx targetValue with
                | .ok _ => some "value_infer_failed_without_local_diagnostic"
                | .error err => some err
            IO.eprintln s!"[semanticGateAttempt] check {summary.declName}"
            let checkValue := Infer.check cfg fuel ctx targetValue targetType
            let evidence : SemanticGateEvidence :=
              { stagedEnvConstCount := senv.consts.length
                closureSize := summary.closure.size
                stagedNameTable := stagedNameTable st
                declTypeWellTyped := declTypeWellTyped
                declTypeDiagnostic := declTypeDiagnostic
                inferValueSucceeded := inferredType?.isSome
                inferValueDiagnostic := inferValueDiagnostic
                checkValue := checkValue
                targetTypeStagedNodes := Expr.size targetType
                targetValueStagedNodes := Expr.size targetValue
                whnfTypeStagedNodes := Expr.size typeWhnf
                whnfValueStagedNodes := Expr.size valueWhnf
                inferredTypeStagedNodes := inferredType?.map Expr.size
                inferredTypeWhnfStagedNodes := inferredTypeWhnf?.map Expr.size
                erasedUniversePayload := st.erasedUniversePayload
                erasedExprMetas := st.erasedExprMetas
                fuel := fuel
                maxConsts := maxConsts }
            let trustAssumptions := semanticGateTrustAssumptions summary st
            if declTypeWellTyped && checkValue then
              pure
                { status := .success
                  reason := "staged_kernel_semantic_exec"
                  detail := s!"{summary.declName} directly stages into the repo's executable Lean-kernel surface, its declaration type is itself well-typed there, and the staged value/proof body checks against the staged declaration type."
                  evidence? := some evidence
                  trustAssumptions := trustAssumptions }
            else
              let reasons :=
                [ if !declTypeWellTyped then some "decl_type_not_well_typed" else none
                , if inferredType?.isNone then some "infer_value_failed" else none
                , if !checkValue then some "check_value_failed" else none
                ].filterMap id
              pure
                { status := .blocked
                  reason := String.intercalate "+" reasons
                  detail := s!"{summary.declName} stages successfully, but the current staged kernel semantics did not validate the declaration type/value pair."
                  evidence? := some evidence
                  trustAssumptions := trustAssumptions }
  | _ =>
      pure
        { status := .notApplicable
          reason := "semantic_gate_decl_kind_boundary"
          detail := s!"{summary.declName} has declaration kind {summary.declKind}; staged semantic execution is currently targeted at theorem/definition/opaque bodies." }

def semanticGateEvidenceJson (evidence : SemanticGateEvidence) : Json :=
  Json.mkObj
    [ ("staged_env_const_count", toJson evidence.stagedEnvConstCount)
    , ("closure_size", toJson evidence.closureSize)
    , ("staged_name_table", Json.arr <| evidence.stagedNameTable.map Json.str)
    , ("decl_type_well_typed", Json.bool evidence.declTypeWellTyped)
    , ("decl_type_diagnostic", evidence.declTypeDiagnostic.map Json.str |>.getD Json.null)
    , ("infer_value_succeeded", Json.bool evidence.inferValueSucceeded)
    , ("infer_value_diagnostic", evidence.inferValueDiagnostic.map Json.str |>.getD Json.null)
    , ("check_value", Json.bool evidence.checkValue)
    , ("target_type_staged_nodes", toJson evidence.targetTypeStagedNodes)
    , ("target_value_staged_nodes", toJson evidence.targetValueStagedNodes)
    , ("whnf_type_staged_nodes", toJson evidence.whnfTypeStagedNodes)
    , ("whnf_value_staged_nodes", toJson evidence.whnfValueStagedNodes)
    , ("inferred_type_staged_nodes", evidence.inferredTypeStagedNodes.map toJson |>.getD Json.null)
    , ("inferred_type_whnf_staged_nodes", evidence.inferredTypeWhnfStagedNodes.map toJson |>.getD Json.null)
    , ("erased_universe_payload", Json.bool evidence.erasedUniversePayload)
    , ("erased_expr_metas", Json.bool evidence.erasedExprMetas)
    , ("fuel", toJson evidence.fuel)
    , ("max_consts", toJson evidence.maxConsts)
    ]

def semanticGateAttemptJson (attempt : SemanticGateAttempt) : Json :=
  Json.mkObj
    [ ("status", Json.str attempt.status.code)
    , ("reason", Json.str attempt.reason)
    , ("detail", Json.str attempt.detail)
    , ("trust_assumptions", Json.arr <| attempt.trustAssumptions.map Json.str |> List.toArray)
    , ("evidence", attempt.evidence?.map semanticGateEvidenceJson |>.getD Json.null)
    ]

namespace Debug

/-- Diagnostic hook: expose the staged semantic bundle for a declaration so local
debug scripts can inspect the exact environment, target type, and target value
used by `semanticGateAttempt` without duplicating its private construction logic. -/
def buildSemanticBundle
    (env : Environment)
    (summary : DeclSummary)
    (ci : ConstantInfo) :
    IO (Except String (SEnv × SExpr × SExpr × SemanticStageState)) :=
  buildSemanticEnv env summary ci

def inferDiagnostic
    (cfg : SConfig)
    (fuel : Nat)
    (ctx : SCtx)
    (e : SExpr) : Except String SExpr :=
  Encoder.inferDiagnostic cfg fuel ctx e

def defEqDiagnostic
    (cfg : SConfig)
    (fuel : Nat)
    (lhs rhs : SExpr) : String :=
  Encoder.defEqDiagnostic cfg fuel lhs rhs

end Debug

end Encoder
end ICC
end LoF
end HeytingLean
