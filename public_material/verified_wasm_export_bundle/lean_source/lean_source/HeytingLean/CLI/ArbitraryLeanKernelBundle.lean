import Lean
import Lean.Data.Json
import HeytingLean.CLI.Args
import HeytingLean.CLI.EnvBootstrap
import HeytingLean.CLI.SKYStageCore
import HeytingLean.LoF.ICC.Encoder.DeclWalker
import HeytingLean.LoF.LeanKernel.BundleSchema

open Lean
open System

namespace HeytingLean.CLI.ArbitraryLeanKernelBundle

open HeytingLean.LoF.ICC.Encoder
open HeytingLean.LoF.LeanKernel

private def natConstName : Name := `Nat
private def stringConstName : Name := `String

structure Args where
  modules : List String := []
  decls : List String := []
  since? : Option String := none
  output : Option FilePath := none
  limit? : Option Nat := none
  maxConsts : Nat := 8192
  deriving Inhabited

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

private abbrev StageM := StateT SemanticStageState (Except String)

def parseArg (xs : List String) (flag : String) : Option String :=
  match xs with
  | [] => none
  | x :: y :: rest => if x == flag then some y else parseArg (y :: rest) flag
  | _ => none

def parseArgsMany (args : List String) (flag : String) : List String :=
  match args with
  | [] => []
  | x :: y :: rest =>
      if x = flag then
        y :: parseArgsMany rest flag
      else
        parseArgsMany (y :: rest) flag
  | _ => []

def parseArgs (argv : List String) : Args :=
  let argv := HeytingLean.CLI.stripLakeArgs argv
  let modules := parseArgsMany argv "--module"
  let decls := parseArgsMany argv "--decl"
  let since? := parseArg argv "--since"
  let output := (parseArg argv "--output").map FilePath.mk
  let limit? := (parseArg argv "--limit").bind String.toNat?
  let maxConsts := (parseArg argv "--max-consts").bind String.toNat? |>.getD 8192
  { modules, decls, since?, output, limit?, maxConsts }

def usage : String :=
  String.intercalate "\n"
    [ "arbitrary_lean_kernel_bundle"
    , ""
    , "Export staged kernel-complete bundles for Lean declarations."
    , ""
    , "Usage:"
    , "  lake env lean --run HeytingLean/CLI/ArbitraryLeanKernelBundle.lean -- --decl HeytingLean.CLI.VerifierProofCorpus.applyId_eq_7"
    , "  lake env lean --run HeytingLean/CLI/ArbitraryLeanKernelBundle.lean -- --module HeytingLean.CLI.VerifierProofCorpus --limit 8"
    , "  lake env lean --run HeytingLean/CLI/ArbitraryLeanKernelBundle.lean -- --since origin/master"
    ]

def modulesFromGitSince (gitRef : String) : IO (Except String (List String)) := do
  let out ← IO.Process.output {
    cmd := "git"
    args := #["diff", "--name-only", s!"{gitRef}..HEAD", "--", "lean"]
  }
  if out.exitCode ≠ 0 then
    return .error s!"git diff failed for --since {gitRef}: {out.stderr.trim}"
  let modules :=
    out.stdout.splitOn "\n"
      |>.map String.trim
      |>.filter (fun line => line.endsWith ".lean" && line.startsWith "lean/")
      |>.map (fun path =>
        let noPrefix := path.drop 5
        let noSuffix := noPrefix.dropRight 5
        noSuffix.replace "/" ".")
      |>.filter (· ≠ "")
      |>.eraseDups
  pure (.ok modules)

def importEnv (modules : List String) : IO Environment := do
  HeytingLean.CLI.EnvBootstrap.bootstrapSearchPath
  let imports :=
    ([`Init] ++ modules.map HeytingLean.CLI.EnvBootstrap.moduleNameFromString).eraseDups
      |>.map (fun moduleName => { module := moduleName })
      |>.toArray
  importModules imports {}

def dedupNames (names : List Name) : List Name :=
  let rec go (seen : Std.HashSet Name) (acc : List Name) : List Name → List Name
    | [] => acc.reverse
    | x :: xs =>
        if seen.contains x then
          go seen acc xs
        else
          go (seen.insert x) (x :: acc) xs
  go {} [] names

def declModuleText? (declText : String) : Option String :=
  let parts := declText.splitOn "."
  match parts.reverse with
  | [] => none
  | [_] => none
  | _declName :: revModuleParts =>
      some <| ".".intercalate revModuleParts.reverse

def moduleTargetDecls (env : Environment) (moduleText : String) : List Name :=
  let moduleName := HeytingLean.CLI.EnvBootstrap.moduleNameFromString moduleText
  (moduleDecls env moduleName).foldl (init := []) fun acc (declName, ci) =>
    if isSurfaceDecl env declName ci then
      declName :: acc
    else
      acc
  |>.reverse

def resolveDecls (env : Environment) (args : Args) (moduleTexts : List String) : List Name :=
  let fromDecls := args.decls.map HeytingLean.CLI.EnvBootstrap.moduleNameFromString
  let resolved :=
    if !fromDecls.isEmpty then
      dedupNames fromDecls
    else
      let fromModules := moduleTexts.foldl (init := []) fun acc moduleText =>
        acc ++ moduleTargetDecls env moduleText
      dedupNames fromModules
  match args.limit? with
  | some limit => resolved.take limit
  | none => resolved

private def stageLiteral : Lean.Literal → Except String HeytingLean.LoF.LeanKernel.Literal
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

private partial def stageLevel : Lean.Level → StageM (ULevel Nat Nat)
  | .zero => pure .zero
  | .succ u => return .succ (← stageLevel u)
  | .max a b => return .max (← stageLevel a) (← stageLevel b)
  | .imax a b => return .imax (← stageLevel a) (← stageLevel b)
  | .param n => return .param (← internLevelParam n)
  | .mvar m => return .mvar (← internLevelMVar (reprStr m))

private def binderInfoToStaged : Lean.BinderInfo → HeytingLean.LoF.LeanKernel.BinderInfo
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
    (assignments : List (Nat × ULevel Nat Nat))
    (paramId : Nat) : Option (ULevel Nat Nat) :=
  assignments.findSome? fun (id, u) =>
    if id == paramId then some u else none

private partial def instantiateLevelParams
    (assignments : List (Nat × ULevel Nat Nat)) :
    ULevel Nat Nat → ULevel Nat Nat
  | .zero => .zero
  | .succ u => .succ (instantiateLevelParams assignments u)
  | .max a b => .max (instantiateLevelParams assignments a) (instantiateLevelParams assignments b)
  | .imax a b => .imax (instantiateLevelParams assignments a) (instantiateLevelParams assignments b)
  | .param p => (lookupLevelAssignment assignments p).getD (.param p)
  | .mvar m => .mvar m

private partial def instantiateExprLevelParams
    (assignments : List (Nat × ULevel Nat Nat)) :
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
  | _ => throw s!"internal kernel-bundle error while interning {name}"

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
    (st : SemanticStageState) :
    Except String (List BundleRecursor × SemanticStageState) := do
  let recSpecs :=
    seeds.foldl (init := ([] : List (Name × Nat × Nat × List (Name × Nat × Nat × List Nat)))) fun acc name =>
      match recursorCasesOnSpec? env name with
      | some spec => if acc.contains spec then acc else spec :: acc
      | none => acc
  recSpecs.foldlM
    (init := (([] : List BundleRecursor), st))
    fun (acc : List BundleRecursor × SemanticStageState) (spec : Name × Nat × Nat × List (Name × Nat × Nat × List Nat)) => do
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
      let built : BundleRecursor :=
        { recursorId := recId
          displayName := recName.toString
          firstMinorIdx := firstMinorIdx
          majorIdx := majorIdx
          ctors := ctorSpecsRev.reverse }
      pure (built :: out, stFinal)

private def pushUnique (xs : Array Name) (name : Name) : Array Name :=
  if xs.contains name then xs else xs.push name

private def dependencyConstValueExpr? : ConstantInfo → Option Lean.Expr
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
  let typeResult ← HeytingLean.CLI.SKYStageCore.lowerProjExpr env scopedType
  match typeResult with
  | .error err => pure (.error s!"while lowering {name}: {err}")
  | .ok loweredType =>
      if name == targetName then
        pure (.ok (loweredType, none))
      else
        match dependencyConstValueExpr? ci with
        | none => pure (.ok (loweredType, none))
        | some value =>
            let scopedValue := value.instantiateLevelParams ci.levelParams scopedLevels
            let valueResult ← HeytingLean.CLI.SKYStageCore.lowerProjExpr env scopedValue
            match valueResult with
            | .error err => pure (.error s!"while lowering {name}: {err}")
            | .ok loweredValue => pure (.ok (loweredType, some loweredValue))

private def stagedNameTable (st : SemanticStageState) : Array String :=
  (st.names.toList.toArray.qsort (fun a b => a.2 < b.2)).map (fun (name, id) => s!"{id}:{name}")

private def stagedLevelParamTable (st : SemanticStageState) : Array String :=
  (st.levelParams.toList.toArray.qsort (fun a b => a.2 < b.2)).map (fun (name, id) => s!"{id}:{name}")

private def stagedLevelMVarTable (st : SemanticStageState) : Array String :=
  (st.levelMVars.toList.toArray.qsort (fun a b => a.2 < b.2)).map (fun (name, id) => s!"{id}:{name}")

private def stagedExprMVarTable (st : SemanticStageState) : Array String :=
  (st.exprMVars.toList.toArray.qsort (fun a b => a.2 < b.2)).map (fun (name, id) => s!"{id}:{name}")

private def baseObligations (targetType : SExpr) (targetValue? : Option SExpr) : List KernelObligation :=
  let typeObligations :=
    [ { label := "target_type_infer_sort", kind := .inferSort, expr := targetType }
    , { label := "target_type_whnf", kind := .whnf, expr := targetType }
    ]
  match targetValue? with
  | none => typeObligations
  | some targetValue =>
      typeObligations ++
        [ { label := "target_value_infer", kind := .infer, expr := targetValue }
        , { label := "target_value_check", kind := .check, expr := targetValue, expr2? := some targetType }
        , { label := "target_value_whnf", kind := .whnf, expr := targetValue }
        ]

def exportKernelBundle
    (env : Environment)
    (summary : DeclSummary)
    (ci : ConstantInfo)
    (maxConsts : Nat := 8192) : IO (Except String ArbitraryLeanKernelBundle) := do
  let some value := constantValueExpr? ci
    | pure (.error s!"{summary.declName} has no visible value/proof body for bundle export")
  let loweredTypeResult ← HeytingLean.CLI.SKYStageCore.lowerProjExpr env ci.type
  let loweredValueResult ← HeytingLean.CLI.SKYStageCore.lowerProjExpr env value
  match loweredTypeResult, loweredValueResult with
  | .error err, _ => pure (.error err)
  | _, .error err => pure (.error err)
  | .ok loweredType, .ok loweredValue =>
      let mut normalizedDecls : Array (Name × List Name × Lean.Expr × Option Lean.Expr) := #[]
      let targetRefs := (collectConstRefs loweredValue (collectConstRefs loweredType {})).toList
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
                        | some depValue => collectConstRefs depValue (collectConstRefs depType {})
                        | none => collectConstRefs depType {}
                      for dep in loweredRefs.toList do
                        if !seen.contains dep then
                          queue := dep :: queue
      let seeds :=
        normalizedDecls.foldl (init := #[natConstName, stringConstName]) fun acc entry =>
          pushUnique acc entry.1
      let convert : Except String ArbitraryLeanKernelBundle := do
        let (targetType', st1) ← stageWithState {} loweredType
        let (targetValue', st2) ← stageWithState st1 loweredValue
        let (natId, st3) ← internConstName st2 natConstName
        let (stringId, st4) ← internConstName st3 stringConstName
        let (recursors, st5) ← semanticCasesOnSpecs env seeds st4
        let ((bundleConstsRev, stFinal)) ←
          normalizedDecls.foldlM
            (init := (([] : List BundleConst), st5))
            fun (acc : List BundleConst × SemanticStageState) (entry : Name × List Name × Lean.Expr × Option Lean.Expr) => do
              let (out, currState) := acc
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
              let built : BundleConst :=
                { nameId := stagedName
                  displayName := name.toString
                  levelParamIds := levelParamIds
                  typeExpr := stagedType
                  valueExpr? := stagedValue? }
              pure (built :: out, stValue)
        pure
          { declName := summary.declName.toString
            moduleName := summary.moduleName.toString
            declKind := summary.declKind
            targetType := targetType'
            targetValue? := some targetValue'
            localContext := []
            envConsts := bundleConstsRev.reverse
            recursors := recursors.reverse
            obligations := baseObligations targetType' (some targetValue')
            stagedNameTable := stagedNameTable stFinal
            stagedLevelParamTable := stagedLevelParamTable stFinal
            stagedLevelMVarTable := stagedLevelMVarTable stFinal
            stagedExprMVarTable := stagedExprMVarTable stFinal
            natConstId := natId
            stringConstId := stringId
            erasedUniversePayload := stFinal.erasedUniversePayload
            erasedExprMetas := stFinal.erasedExprMetas
            closureOverflow := summary.closureOverflow
            missingDeps := summary.missingDeps.map Name.toString
            maxConsts := maxConsts }
      pure convert

def exportKernelBundleForDecl
    (env : Environment)
    (declName : Name)
    (maxConsts : Nat := 8192) : IO (Except String ArbitraryLeanKernelBundle) := do
  match env.find? declName with
  | none => pure (.error s!"declaration not found: {declName}")
  | some ci =>
      let summary := summarizeDecl env declName ci maxConsts
      exportKernelBundle env summary ci maxConsts

private def exportRowJson
    (declName : Name)
    (result : Except String ArbitraryLeanKernelBundle) : Json :=
  match result with
  | .ok bundle =>
      Json.mkObj
        [ ("decl_name", Json.str bundle.declName)
        , ("module_name", Json.str bundle.moduleName)
        , ("decl_kind", Json.str bundle.declKind)
        , ("status", Json.str "exported")
        , ("bundle", bundleToJson bundle)
        ]
  | .error err =>
      Json.mkObj
        [ ("decl_name", Json.str declName.toString)
        , ("status", Json.str "error")
        , ("error", Json.str err)
        ]

private def summaryJson (rows : Array Json) : Json :=
  let exported :=
    rows.foldl (init := 0) fun acc row =>
      match row.getObjValAs? String "status" with
      | .ok "exported" => acc + 1
      | _ => acc
  Json.mkObj
    [ ("row_count", toJson rows.size)
    , ("exported_count", toJson exported)
    , ("error_count", toJson (rows.size - exported))
    ]

private def writeOutput (args : Args) (payload : Json) : IO Unit := do
  let text := payload.pretty
  match args.output with
  | some path =>
      IO.FS.writeFile path (text ++ "\n")
      IO.eprintln s!"[arbitrary_lean_kernel_bundle] wrote {path}"
  | none =>
      IO.println text

def run (argv : List String) : IO UInt32 := do
  let args := parseArgs argv
  if args.modules.isEmpty && args.decls.isEmpty && args.since?.isNone then
    IO.eprintln usage
    return 1
  let sinceModules ←
    match args.since? with
    | some gitRef =>
        match ← modulesFromGitSince gitRef with
        | .ok modules => pure modules
        | .error err => IO.eprintln err; return 1
    | none => pure []
  let moduleTexts :=
    if !args.modules.isEmpty then
      (args.modules ++ sinceModules).eraseDups
    else
      let declModules :=
        if args.decls.isEmpty then
          []
        else
          args.decls.foldr (init := []) fun declText acc =>
            match declModuleText? declText with
            | some moduleText => moduleText :: acc
            | none => acc
      (args.modules ++ declModules ++ sinceModules).eraseDups
  if moduleTexts.isEmpty then
    IO.eprintln usage
    return 1
  let env ← importEnv moduleTexts
  let mut rows : Array Json := #[]
  for declName in resolveDecls env args moduleTexts do
    IO.eprintln s!"[arbitrary_lean_kernel_bundle] exporting {declName}"
    let result ← exportKernelBundleForDecl env declName args.maxConsts
    rows := rows.push (exportRowJson declName result)
  let payload :=
    Json.mkObj
      [ ("tool", Json.str "arbitrary_lean_kernel_bundle")
      , ("summary", summaryJson rows)
      , ("rows", Json.arr rows)
      ]
  writeOutput args payload
  pure 0

end HeytingLean.CLI.ArbitraryLeanKernelBundle
