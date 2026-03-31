import Lean
import Lean.Data.Json
import HeytingLean.CLI.EnvBootstrap
import HeytingLean.CLI.SKYTraceJson
import HeytingLean.LoF.Combinators.BracketAbstraction
import HeytingLean.LoF.Combinators.SKYExec
import HeytingLean.LoF.Combinators.SKYMachineBounded
import HeytingLean.LoF.LeanKernel.Environment
import HeytingLean.LoF.LeanKernel.EnvironmentSKY
import HeytingLean.LoF.LeanKernel.FullKernelSKY
import HeytingLean.LoF.LeanKernel.Lean4LeanSKY
import HeytingLean.LoF.LeanKernel.VerifierObligationJson
import HeytingLean.LoF.LeanKernel.WHNFSKY
import HeytingLean.Util.ModuleOwner

open Lean
open Lean.Meta
open System

open HeytingLean.LoF
open HeytingLean.LoF.Combinators
open HeytingLean.LoF.LeanKernel

namespace HeytingLean.CLI.VerifiedCheck

abbrev OracleRef := Unit
abbrev SLevel := ULevel Unit Unit
abbrev SExpr := Expr Nat Unit Unit Unit
abbrev SEnv := HeytingLean.LoF.LeanKernel.Environment.Env Nat Unit Unit Unit
abbrev SConstDecl := HeytingLean.LoF.LeanKernel.Environment.ConstDecl Nat Unit Unit Unit

inductive TraceGrain where
  | step
  | whnf
  deriving DecidableEq, Repr

instance : ToString TraceGrain where
  toString
    | .step => "step"
    | .whnf => "whnf"

inductive OpKind where
  | whnfType
  | whnfValue
  | inferTypeSort
  | inferValueShape
  | inferValue
  | defEqInferredDeclared
  | checkValue
  deriving DecidableEq, Repr

instance : ToString OpKind where
  toString
    | .whnfType => "whnf_type"
    | .whnfValue => "whnf_value"
    | .inferTypeSort => "infer_type_sort"
    | .inferValueShape => "infer_value_shape"
    | .inferValue => "infer_value"
    | .defEqInferredDeclared => "defeq_inferred_declared"
    | .checkValue => "check_value"

structure Cfg where
  moduleName : Name
  output : Option FilePath := none
  exportSky : Option FilePath := none
  phaseTrace : Option FilePath := none
  bracketMode : Bracket.BracketMode := .classic
  listOnly : Bool := false
  machineExportOnly : Bool := false
  traceGrain? : Option TraceGrain := none
  fuelWhnf : Nat := 20
  fuelDefEq : Nat := 20
  fuelInfer : Nat := 20
  fuelReduce : Nat := 400000
  maxNodes : Nat := 200000
  maxDecls : Option Nat := none
  maxEnvConsts : Nat := 512
  traceMaxSteps : Nat := 256
  includeDecls : Array Name := #[]
  onlyOpKinds : Array OpKind := #[]

instance : Repr Bracket.BracketMode where
  reprPrec m _ :=
    match m with
    | .classic => "Bracket.BracketMode.classic"
    | .bulk => "Bracket.BracketMode.bulk"

instance : Repr Cfg where
  reprPrec cfg _ :=
    let fields : List String :=
      [ s!"moduleName := {reprStr cfg.moduleName}"
      , s!"output := {reprStr cfg.output}"
      , s!"exportSky := {reprStr cfg.exportSky}"
      , s!"phaseTrace := {reprStr cfg.phaseTrace}"
      , s!"bracketMode := {reprStr cfg.bracketMode}"
      , s!"listOnly := {reprStr cfg.listOnly}"
      , s!"machineExportOnly := {reprStr cfg.machineExportOnly}"
      , s!"traceGrain? := {reprStr cfg.traceGrain?}"
      , s!"fuelWhnf := {reprStr cfg.fuelWhnf}"
      , s!"fuelDefEq := {reprStr cfg.fuelDefEq}"
      , s!"fuelInfer := {reprStr cfg.fuelInfer}"
      , s!"fuelReduce := {reprStr cfg.fuelReduce}"
      , s!"maxNodes := {reprStr cfg.maxNodes}"
      , s!"maxDecls := {reprStr cfg.maxDecls}"
      , s!"maxEnvConsts := {reprStr cfg.maxEnvConsts}"
      , s!"traceMaxSteps := {reprStr cfg.traceMaxSteps}"
      , s!"includeDecls := {reprStr cfg.includeDecls}"
      , s!"onlyOpKinds := {reprStr cfg.onlyOpKinds}"
      ]
    "{" ++ String.intercalate ", " fields ++ "}"

structure InternState where
  nextId : Nat := 1
  names : Std.HashMap Name Nat := {}
  erasedUniversePayload : Bool := false
  erasedExprMetas : Bool := false
deriving Inhabited

abbrev ConvertM := StateT InternState (Except String)

structure NativeDirect where
  loweredType : Lean.Expr
  loweredValue : Lean.Expr
  loweredWhnfType : Lean.Expr
  loweredWhnfValue : Lean.Expr
  loweredInferSort : Lean.Expr
  loweredInferType : Lean.Expr
  defeqInferredDeclared : Bool
  checkValue : Bool
  whnfTypeMs : Nat
  whnfValueMs : Nat
  inferTypeMs : Nat
  inferValueMs : Nat
  defeqMs : Nat
  checkMs : Nat

structure WhnfLeafDirect where
  inputExpr : Lean.Expr
  loweredDeclType : Lean.Expr
  loweredInput : Lean.Expr
  loweredOutput : Lean.Expr
  nativeMs : Nat
  lowerDeclTypeMs : Nat
  lowerInputMs : Nat
  lowerOutputMs : Nat

structure DefEqLeafDirect where
  declTypeWhnf : Lean.Expr
  inferTypeWhnf : Lean.Expr
  loweredDeclType : Lean.Expr
  loweredInferType : Lean.Expr
  inferMs : Nat
  whnfDeclTypeMs : Nat
  whnfInferTypeMs : Nat
  defeqMs : Nat
  nativeBool : Bool
  lowerDeclTypeMs : Nat
  lowerInferTypeMs : Nat

structure EqPayload where
  typeExpr : Lean.Expr
  lhsExpr : Lean.Expr
  rhsExpr : Lean.Expr

structure ProducerTiming where
  lowerDeclTypeMs : Nat := 0
  lowerInputMs : Nat := 0
  nativeMs : Nat := 0
  lowerOutputMs : Nat := 0
  closureMs : Nat := 0
  stageMs : Nat := 0
  compileMs : Nat := 0
  machineExportMs : Nat := 0

private def producerTimingJson (timing : ProducerTiming) : Json :=
  Json.mkObj
    [ ("lower_decl_type", toJson timing.lowerDeclTypeMs)
    , ("lower_input", toJson timing.lowerInputMs)
    , ("native", toJson timing.nativeMs)
    , ("lower_output", toJson timing.lowerOutputMs)
    , ("closure", toJson timing.closureMs)
    , ("stage", toJson timing.stageMs)
    , ("compile", toJson timing.compileMs)
    , ("machine_export", toJson timing.machineExportMs)
    ]

private def appendPhaseTrace
    (cfg : Cfg)
    (declName : Name)
    (phase : String)
    (payload : List (String × Json) := []) : IO Unit := do
  match cfg.phaseTrace with
  | none => pure ()
  | some path =>
      let nowMs ← IO.monoMsNow
      let line := Json.mkObj <|
        [ ("timestamp_ms", toJson nowMs)
        , ("decl_name", Json.str declName.toString)
        , ("phase", Json.str phase)
        ] ++ payload
      IO.FS.withFile path .append fun h => do
        h.putStrLn line.compress

private def usage : String :=
  String.intercalate "\n"
    [ "Usage: verified_check <Module.Name> [--output FILE] [--export-sky FILE] [--phase-trace FILE] [--list-only] [--machine-export-only] [--trace-grain <step|whnf>] [--trace-whnf] [--trace-max-steps N] [--bracket-mode <classic|bulk>] [--fuel-whnf N] [--fuel-defeq N] [--fuel-infer N] [--fuel-reduce N] [--max-nodes N] [--max-decls N] [--max-env-consts N] [--only-op <name[,name...]>]"
    , ""
    , "Default mode: export native Lean declaration checks as SKY boolean obligations for CUDA parity verification."
    , "Trace mode (--trace-grain step|whnf): record native WHNF traces at step or coarser WHNF-call grain."
    , "--trace-whnf is retained as a backward-compatible alias for --trace-grain step."
    , "--export-sky writes a portable sky-v1 artifact for exported verifier obligations."
    ]

private def parseNatFlag (flag value : String) : Except String Nat :=
  match value.toNat? with
  | some n => .ok n
  | none => .error s!"invalid {flag} value: {value}"

private def parseTraceGrain (value : String) : Except String TraceGrain :=
  match value.trim.toLower with
  | "step" => .ok .step
  | "whnf" => .ok .whnf
  | _ => .error s!"invalid --trace-grain value: {value}"

private def parseBracketMode (value : String) : Except String Bracket.BracketMode :=
  match value.trim.toLower with
  | "classic" => .ok .classic
  | "bulk" => .ok .bulk
  | _ => .error s!"invalid --bracket-mode value: {value}"

private def bracketModeString (mode : Bracket.BracketMode) : String :=
  match mode with
  | .classic => "classic"
  | .bulk => "bulk"

private def parseOpKind (value : String) : Except String OpKind :=
  match value.trim.toLower with
  | "whnf_type" => .ok .whnfType
  | "whnf_value" => .ok .whnfValue
  | "infer_type_sort" => .ok .inferTypeSort
  | "infer_value_shape" => .ok .inferValueShape
  | "infer_value" => .ok .inferValue
  | "defeq_inferred_declared" => .ok .defEqInferredDeclared
  | "check_value" => .ok .checkValue
  | _ => .error s!"invalid --only-op entry: {value}"

private def parseOpKinds (value : String) : Except String (Array OpKind) := do
  value.splitOn "," |>.foldlM (init := #[]) fun acc piece =>
    let piece := piece.trim
    if piece.isEmpty then
      pure acc
    else
      return acc.push (← parseOpKind piece)

private def opEnabled (cfg : Cfg) (kind : OpKind) : Bool :=
  cfg.onlyOpKinds.isEmpty || cfg.onlyOpKinds.contains kind

private def parseArgs (argv : List String) : Except String Cfg := do
  match argv with
  | [] => throw usage
  | moduleText :: rest =>
      let moduleName := HeytingLean.CLI.EnvBootstrap.moduleNameFromString moduleText
      let rec go (cfg : Cfg) : List String → Except String Cfg
        | [] => .ok cfg
        | "--output" :: path :: xs => go { cfg with output := some path } xs
        | "--export-sky" :: path :: xs => go { cfg with exportSky := some path } xs
        | "--phase-trace" :: path :: xs => go { cfg with phaseTrace := some path } xs
        | "--list-only" :: xs => go { cfg with listOnly := true } xs
        | "--machine-export-only" :: xs => go { cfg with machineExportOnly := true } xs
        | "--trace-whnf" :: xs => go { cfg with traceGrain? := some .step } xs
        | "--trace-grain" :: grain :: xs => do
            let traceGrain ← parseTraceGrain grain
            go { cfg with traceGrain? := some traceGrain } xs
        | "--bracket-mode" :: mode :: xs => do
            let bracketMode ← parseBracketMode mode
            go { cfg with bracketMode := bracketMode } xs
        | "--fuel-whnf" :: n :: xs => do
            let fuelWhnf ← parseNatFlag "--fuel-whnf" n
            go { cfg with fuelWhnf := fuelWhnf } xs
        | "--fuel-defeq" :: n :: xs => do
            let fuelDefEq ← parseNatFlag "--fuel-defeq" n
            go { cfg with fuelDefEq := fuelDefEq } xs
        | "--fuel-infer" :: n :: xs => do
            let fuelInfer ← parseNatFlag "--fuel-infer" n
            go { cfg with fuelInfer := fuelInfer } xs
        | "--fuel-reduce" :: n :: xs => do
            let fuelReduce ← parseNatFlag "--fuel-reduce" n
            go { cfg with fuelReduce := fuelReduce } xs
        | "--max-nodes" :: n :: xs => do
            let maxNodes ← parseNatFlag "--max-nodes" n
            go { cfg with maxNodes := maxNodes } xs
        | "--max-decls" :: n :: xs => do
            let maxDecls ← parseNatFlag "--max-decls" n
            go { cfg with maxDecls := some maxDecls } xs
        | "--max-env-consts" :: n :: xs => do
            let maxEnvConsts ← parseNatFlag "--max-env-consts" n
            go { cfg with maxEnvConsts := maxEnvConsts } xs
        | "--trace-max-steps" :: n :: xs => do
            let traceMaxSteps ← parseNatFlag "--trace-max-steps" n
            go { cfg with traceMaxSteps := traceMaxSteps } xs
        | "--include" :: names :: xs =>
            let includeDecls :=
              names.splitOn "," |>.foldl (init := cfg.includeDecls) fun acc piece =>
                let piece := piece.trim
                if piece.isEmpty then acc
                else acc.push (HeytingLean.CLI.EnvBootstrap.moduleNameFromString piece)
            go { cfg with includeDecls := includeDecls } xs
        | "--only-op" :: names :: xs => do
            let onlyOpKinds ← parseOpKinds names
            go { cfg with onlyOpKinds := onlyOpKinds } xs
        | "--help" :: _ => throw usage
        | x :: _ => throw s!"unexpected argument: {x}\n\n{usage}"
      go { moduleName := moduleName } rest

private def binderInfoToStaged : Lean.BinderInfo → LeanKernel.BinderInfo
  | .default => .default
  | .implicit => .implicit
  | .strictImplicit => .strictImplicit
  | .instImplicit => .instImplicit

private def canonicalBinderName : Name := `_skyBinder
private def canonicalLetName : Name := `_skyLet

private def internName (n : Name) : ConvertM Nat := do
  let st ← get
  match st.names.get? n with
  | some id => pure id
  | none =>
      let id := st.nextId
      set { st with nextId := id + 1, names := st.names.insert n id }
      pure id

private partial def stageLevel : Lean.Level → ConvertM SLevel
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

private def stageLiteral : Lean.Literal → Except String LeanKernel.Literal
  | .natVal n => .ok (.natVal n)
  | .strVal s => .ok (.strVal s)

private partial def stageExpr : Lean.Expr → ConvertM SExpr
  | .bvar idx => pure (.bvar idx)
  | .mvar _ => do
      modify fun st => { st with erasedExprMetas := true }
      pure (.mvar ())
  | .sort u => return .sort (← stageLevel u)
  | .const n us =>
      return .const (← internName n) (← us.mapM stageLevel)
  | .app f a =>
      return .app (← stageExpr f) (← stageExpr a)
  | .lam _ ty body bi =>
      return .lam (← internName canonicalBinderName) (binderInfoToStaged bi) (← stageExpr ty) (← stageExpr body)
  | .forallE _ ty body bi =>
      return .forallE (← internName canonicalBinderName) (binderInfoToStaged bi) (← stageExpr ty) (← stageExpr body)
  | .letE _ ty val body _ =>
      return .letE (← internName canonicalLetName) .default (← stageExpr ty) (← stageExpr val) (← stageExpr body)
  | .lit lit =>
      return .lit (← liftM (stageLiteral lit))
  | .mdata _ body => stageExpr body
  | .fvar fvarId => throw s!"unsupported fvar expression: {fvarId.name}"
  | .proj typeName idx body =>
      throw s!"unsupported proj expression: {typeName}.{idx} in {repr body}"

private def stageExprWithState (st : InternState) (e : Lean.Expr) : Except String (SExpr × InternState) :=
  match (stageExpr e).run st with
  | .error err => .error err
  | .ok (expr, st') => .ok (expr, st')

private partial def collectConstRefs (e : Lean.Expr) (acc : Std.HashSet Name := {}) : Std.HashSet Name :=
  match e with
  | .const n _ => acc.insert n
  | .app f a => collectConstRefs a (collectConstRefs f acc)
  | .lam _ ty body _ => collectConstRefs body (collectConstRefs ty acc)
  | .forallE _ ty body _ => collectConstRefs body (collectConstRefs ty acc)
  | .letE _ ty val body _ => collectConstRefs body (collectConstRefs val (collectConstRefs ty acc))
  | .mdata _ body => collectConstRefs body acc
  | .proj _ _ body => collectConstRefs body acc
  | _ => acc

private def constKind (ci : ConstantInfo) : String :=
  match ci with
  | .thmInfo _ => "theorem"
  | .axiomInfo _ => "axiom_decl"
  | .defnInfo _ => "def"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "recursor"

private def constantValueExpr? : ConstantInfo → Option Lean.Expr
  | .defnInfo info => some info.value
  | .opaqueInfo info => some info.value
  | .thmInfo info => some info.value
  | _ => none

private def isCheckableDecl (ci : ConstantInfo) : Bool :=
  match ci with
  | .defnInfo _ | .opaqueInfo _ | .thmInfo _ => true
  | _ => false

private def envConstInfo? (env : Lean.Environment) (n : Name) : Option ConstantInfo :=
  env.constants.find? n

private partial def containsProj : Lean.Expr → Bool
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

private partial def containsNatLiteralExpr : Lean.Expr → Bool
  | e@(.app f a) => isNatLiteralExpr e || containsNatLiteralExpr f || containsNatLiteralExpr a
  | e@(.lam _ ty body _) => isNatLiteralExpr e || containsNatLiteralExpr ty || containsNatLiteralExpr body
  | e@(.forallE _ ty body _) => isNatLiteralExpr e || containsNatLiteralExpr ty || containsNatLiteralExpr body
  | e@(.letE _ ty val body _) =>
      isNatLiteralExpr e || containsNatLiteralExpr ty || containsNatLiteralExpr val || containsNatLiteralExpr body
  | e@(.mdata _ body) => isNatLiteralExpr e || containsNatLiteralExpr body
  | e@(.proj _ _ body) => isNatLiteralExpr e || containsNatLiteralExpr body
  | e => isNatLiteralExpr e

private def runMetaAtEnv (env : Lean.Environment) (x : MetaM α) : IO α := do
  let ctxCore : Core.Context := { fileName := "<verified_check>", fileMap := default }
  let sCore : Core.State := { env := env }
  let (a, _, _) ← x.toIO ctxCore sCore
  pure a

private def lowerProjExpr (env : Lean.Environment) (e : Lean.Expr) : IO (Except String Lean.Expr) := do
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
                let some info := Lean.getStructureInfo? (← getEnv) structName
                  | throwError "unknown structure for projection {structName}"
                let some fieldName := info.fieldNames[idx]?
                  | throwError "invalid projection index {idx} for structure {structName}"
                return .visit (← Lean.Meta.mkProjection body fieldName)
            | _ =>
                return .continue)
    return Except.ok lowered
  catch ex =>
    return Except.error s!"projection lowering failed: {ex}"

private def internConstName
    (st : InternState)
    (name : Name) : Except String (Nat × InternState) := do
  let (expr, st') ← stageExprWithState st (.const name [])
  match expr with
  | .const id _ => pure (id, st')
  | _ => throw s!"internal verified-check error while interning {name}"

private def recursorCasesOnSpec?
    (env : Lean.Environment)
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
    (env : Lean.Environment)
    (seeds : Array Name)
    (st : InternState) :
    Except String (List (Inductive.CasesOnSpec Nat) × InternState) := do
  let recSpecs :=
    seeds.foldl (init := ([] : List (Name × Nat × Nat × List (Name × Nat × Nat × List Nat)))) fun acc name =>
      match recursorCasesOnSpec? env name with
      | some spec => if acc.contains spec then acc else spec :: acc
      | none => acc
  recSpecs.foldlM
    (init := (([] : List (Inductive.CasesOnSpec Nat)), st))
    fun (acc : List (Inductive.CasesOnSpec Nat) × InternState) (spec : Name × Nat × Nat × List (Name × Nat × Nat × List Nat)) => do
      let (out, currState) := acc
      let (recName, firstMinorIdx, majorIdx, ctors) := spec
      let (recId, st1) ← internConstName currState recName
      let ((ctorSpecsRev, stFinal)) ←
        ctors.foldlM
          (init := (([] : List (Inductive.CtorSpec Nat)), st1))
          fun (acc2 : List (Inductive.CtorSpec Nat) × InternState) (entry : Name × Nat × Nat × List Nat) => do
            let (ctorAcc, ctorState) := acc2
            let (ctorName, ctorParams, numFields, recursiveFields) := entry
            let (ctorId, nextState) ← internConstName ctorState ctorName
            let built : Inductive.CtorSpec Nat :=
              { name := ctorId
                numParams := ctorParams
                numFields := numFields
                recursiveFieldPositions := recursiveFields }
            pure (built :: ctorAcc, nextState)
      let built : Inductive.CasesOnSpec Nat :=
        { recursor := recId
          firstMinorIdx := firstMinorIdx
          majorIdx := majorIdx
          ctors := ctorSpecsRev.reverse }
      pure (built :: out, stFinal)

private def loweredConstPayload
    (env : Lean.Environment)
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
        match constantValueExpr? ci with
        | none => pure (.ok (loweredType, none))
        | some value => do
            let scopedValue := value.instantiateLevelParams ci.levelParams scopedLevels
            let valueResult ← lowerProjExpr env scopedValue
            match valueResult with
            | .error err => pure (.error s!"while lowering {name}: {err}")
            | .ok loweredValue => pure (.ok (loweredType, some loweredValue))

private abbrev LevelInstMap := Std.HashMap Name (List Lean.Level)

private def registerConstLevelInst
    (insts : LevelInstMap)
    (name : Name)
    (us : List Lean.Level) : Except String LevelInstMap :=
  match insts.get? name with
  | none => pure (insts.insert name us)
  | some prev =>
      if prev == us then
        pure insts
      else if prev.isEmpty then
        pure (insts.insert name us)
      else if us.isEmpty then
        pure insts
      else
        throw s!"multiple universe instantiations for {name}: saw {reprStr prev} and {reprStr us}"

private partial def collectConstLevelInsts
    (e : Lean.Expr)
    (insts : LevelInstMap := {}) : Except String LevelInstMap :=
  match e with
  | .const n us => registerConstLevelInst insts n us
  | .app f a => do
      let insts' ← collectConstLevelInsts f insts
      collectConstLevelInsts a insts'
  | .lam _ ty body _ => do
      let insts' ← collectConstLevelInsts ty insts
      collectConstLevelInsts body insts'
  | .forallE _ ty body _ => do
      let insts' ← collectConstLevelInsts ty insts
      collectConstLevelInsts body insts'
  | .letE _ ty val body _ => do
      let insts' ← collectConstLevelInsts ty insts
      let insts'' ← collectConstLevelInsts val insts'
      collectConstLevelInsts body insts''
  | .mdata _ body => collectConstLevelInsts body insts
  | .proj _ _ body => collectConstLevelInsts body insts
  | _ => pure insts

private partial def eraseConstLevelInsts : Lean.Expr → Lean.Expr
  | .bvar idx => .bvar idx
  | .fvar fvarId => .fvar fvarId
  | .mvar m => .mvar m
  | .sort u => .sort u
  | .const n _ => .const n []
  | .app f a => .app (eraseConstLevelInsts f) (eraseConstLevelInsts a)
  | .lam n ty body bi => .lam n (eraseConstLevelInsts ty) (eraseConstLevelInsts body) bi
  | .forallE n ty body bi => .forallE n (eraseConstLevelInsts ty) (eraseConstLevelInsts body) bi
  | .letE n ty val body nonDep =>
      .letE n (eraseConstLevelInsts ty) (eraseConstLevelInsts val) (eraseConstLevelInsts body) nonDep
  | .lit lit => .lit lit
  | .mdata md body => .mdata md (eraseConstLevelInsts body)
  | .proj s idx body => .proj s idx (eraseConstLevelInsts body)

private def loweredConstPayloadWithInsts
    (env : Lean.Environment)
    (insts : LevelInstMap)
    (name : Name)
    (ci : ConstantInfo)
    (targetName : Name) : IO (Except String (Lean.Expr × Option Lean.Expr)) := do
  let chosenLevels :=
    match insts.get? name with
    | some us =>
        if us.isEmpty && !ci.levelParams.isEmpty then
          List.replicate ci.levelParams.length Lean.Level.zero
        else
          us
    | none => List.replicate ci.levelParams.length Lean.Level.zero
  if chosenLevels.length != ci.levelParams.length then
    return .error s!"while lowering {name}: expected {ci.levelParams.length} universe levels, got {chosenLevels.length}"
  let scopedType := ci.type.instantiateLevelParams ci.levelParams chosenLevels
  let typeResult ← lowerProjExpr env scopedType
  match typeResult with
  | .error err => pure (.error s!"while lowering {name}: {err}")
  | .ok loweredType =>
      let loweredType := eraseConstLevelInsts loweredType
      if name == targetName then
        pure (.ok (loweredType, none))
      else
        match constantValueExpr? ci with
        | none => pure (.ok (loweredType, none))
        | some value => do
            let scopedValue := value.instantiateLevelParams ci.levelParams chosenLevels
            let valueResult ← lowerProjExpr env scopedValue
            match valueResult with
            | .error err => pure (.error s!"while lowering {name}: {err}")
            | .ok loweredValue =>
                pure (.ok (loweredType, some (eraseConstLevelInsts loweredValue)))

private partial def closureNames
    (env : Lean.Environment)
    (targetName : Name)
    (seed : List Name)
    (maxConsts : Nat) : IO (Except String (Array Name)) := do
  let rec loop (queue : List Name) (seen : Std.HashSet Name) (acc : Array Name) : IO (Except String (Array Name)) := do
    match queue with
    | [] => pure (Except.ok acc)
    | name :: rest =>
        if seen.contains name then
          loop rest seen acc
        else if acc.size >= maxConsts then
          pure <| Except.error s!"environment closure exceeded --max-env-consts={maxConsts} while expanding {targetName}"
        else
          let seen' := seen.insert name
          match envConstInfo? env name with
          | none => loop rest seen' acc
          | some ci =>
              let normTypeResult ← lowerProjExpr env ci.type
              match normTypeResult with
              | .error err => pure (Except.error s!"while lowering dependency {name}: {err}")
              | .ok normType =>
                  let refs0 := collectConstRefs normType
                  let refsResult ←
                    match constantValueExpr? ci with
                    | some value => do
                        let normValueResult ← lowerProjExpr env value
                        match normValueResult with
                        | .error err => pure (Except.error s!"while lowering dependency {name}: {err}")
                        | .ok normValue =>
                            pure (Except.ok (collectConstRefs normValue refs0))
                    | none =>
                        pure (Except.ok refs0)
                  match refsResult with
                  | .error err => pure (Except.error err)
                  | .ok refs =>
                      loop (refs.toList ++ rest) seen' (acc.push name)
  loop seed {} #[]

private def natConstName : Name := `Nat
private def stringConstName : Name := `String
private def ofNatConstName : Name := ``OfNat.ofNat
private def instOfNatNatConstName : Name := `instOfNatNat

private def buildStagedEnv
    (env : Lean.Environment)
    (targetName : Name)
    (closure : Array Name)
    (targetType targetValue : Lean.Expr) : IO (Except String (SEnv × SExpr × SExpr × InternState)) := do
  let seeds :=
    closure.foldl (init := #[targetName, natConstName, stringConstName, ofNatConstName, instOfNatNatConstName]) fun acc name =>
      if acc.contains name then acc else acc.push name
  let normTargetTypeResult ← lowerProjExpr env targetType
  let normTargetValueResult ← lowerProjExpr env targetValue
  match normTargetTypeResult, normTargetValueResult with
  | .error err, _ => pure (Except.error err)
  | _, .error err => pure (Except.error err)
  | .ok normTargetType, .ok normTargetValue => do
      let targetInstsResult := do
        let insts0 ← collectConstLevelInsts normTargetType
        collectConstLevelInsts normTargetValue insts0
      match targetInstsResult with
      | .error err => pure (Except.error err)
      | .ok targetInsts => do
        let mut insts := targetInsts
        let mut failed : Option String := none
        for _ in [:seeds.size.succ] do
          if failed.isSome then
            pure ()
          else
            let startSize := insts.size
            for name in seeds do
              if failed.isSome then
                pure ()
              else
                match envConstInfo? env name with
                | none => pure ()
                | some ci =>
                    match ← loweredConstPayloadWithInsts env insts name ci targetName with
                    | .error err =>
                        failed := some err
                    | .ok (normType, normValue?) =>
                        match collectConstLevelInsts normType insts with
                        | .error err =>
                            failed := some err
                        | .ok next =>
                            insts := next
                        match normValue? with
                        | none => pure ()
                        | some normValue =>
                            match collectConstLevelInsts normValue insts with
                            | .error err =>
                                failed := some err
                            | .ok next =>
                                insts := next
            if failed.isNone && insts.size == startSize then
              break
        match failed with
        | some err => pure (Except.error err)
        | none => do
            let normTargetType := eraseConstLevelInsts normTargetType
            let normTargetValue := eraseConstLevelInsts normTargetValue
            let mut normalizedDecls : Array (Name × Lean.Expr × Option Lean.Expr) := #[]
            for name in seeds do
              match envConstInfo? env name with
              | none => pure ()
              | some ci =>
                  let payloadResult ← loweredConstPayloadWithInsts env insts name ci targetName
                  match payloadResult with
                  | .error err => return Except.error err
                  | .ok (normType, normValue?) =>
                      normalizedDecls := normalizedDecls.push (name, normType, normValue?)
            let convert : ConvertM (SEnv × SExpr × SExpr) := do
              let targetType' ← stageExpr normTargetType
              let targetValue' ← stageExpr normTargetValue
              let natId ← internName natConstName
              let stringId ← internName stringConstName
              let stBeforeSpecs ← get
              let (casesOnSpecs, stAfterSpecs) ←
                match semanticCasesOnSpecs env seeds stBeforeSpecs with
                | .ok result => pure result
                | .error err => throw err
              set stAfterSpecs
              let litTypeFn := fun lit =>
                match lit with
                | LeanKernel.Literal.natVal _ => some (.const natId [])
                | LeanKernel.Literal.strVal _ => some (.const stringId [])
              let mut senv : SEnv :=
                { beqName := fun a b => a == b
                  consts := []
                  casesOnSpecs := casesOnSpecs
                  mvarType? := fun _ => none
                  litType? := litTypeFn
                }
              for (name, normType, normValue?) in normalizedDecls do
                let stagedName ← internName name
                let stagedType ← stageExpr normType
                let stagedValue? <-
                  if name == targetName then
                    pure none
                  else
                    match normValue? with
                    | some normValue => do
                        let value' ← stageExpr normValue
                        pure (some value')
                    | none => pure none
                let decl : SConstDecl :=
                  match stagedValue? with
                  | some value => Environment.ConstDecl.ofDef stagedName stagedType value
                  | none => Environment.ConstDecl.ofType stagedName stagedType
                senv := senv.addConst decl
              pure (senv, targetType', targetValue')
            pure <|
              match convert.run {} with
              | .error err => Except.error err
              | .ok ((senv, targetType', targetValue'), st) => Except.ok (senv, targetType', targetValue', st)

private def buildStagedEnvSingle
    (env : Lean.Environment)
    (targetName : Name)
    (closure : Array Name)
    (targetDeclType targetExpr : Lean.Expr) : IO (Except String (SEnv × SExpr × InternState)) := do
  let seeds :=
    closure.foldl (init := #[targetName, natConstName, stringConstName, ofNatConstName, instOfNatNatConstName]) fun acc name =>
      if acc.contains name then acc else acc.push name
  let mut normalizedDecls : Array (Name × Lean.Expr × Option Lean.Expr) := #[]
  for name in seeds do
    match envConstInfo? env name with
    | none => pure ()
    | some ci =>
        let payloadResult ← loweredConstPayload env name ci targetName
        match payloadResult with
        | .error err => return Except.error err
        | .ok (normType, normValue?) =>
            normalizedDecls := normalizedDecls.push (name, normType, normValue?)
  let convert : ConvertM (SEnv × SExpr) := do
    let targetExpr' ← stageExpr targetExpr
    let natId ← internName natConstName
    let stringId ← internName stringConstName
    let stBeforeSpecs ← get
    let (casesOnSpecs, stAfterSpecs) ←
      match semanticCasesOnSpecs env seeds stBeforeSpecs with
      | .ok result => pure result
      | .error err => throw err
    set stAfterSpecs
    let litTypeFn := fun lit =>
      match lit with
      | LeanKernel.Literal.natVal _ => some (.const natId [])
      | LeanKernel.Literal.strVal _ => some (.const stringId [])
    let mut senv : SEnv :=
      { beqName := fun a b => a == b
        consts := []
        casesOnSpecs := casesOnSpecs
        mvarType? := fun _ => none
        litType? := litTypeFn
      }
    for (name, normType, normValue?) in normalizedDecls do
      let stagedName ← internName name
      let stagedType <-
        if name == targetName then
          stageExpr targetDeclType
        else
          stageExpr normType
      let stagedValue? <-
        if name == targetName then
          pure none
        else
          match normValue? with
          | some normValue => do
              let value' ← stageExpr normValue
              pure (some value')
          | none => pure none
      let decl : SConstDecl :=
        match stagedValue? with
        | some value => Environment.ConstDecl.ofDef stagedName stagedType value
        | none => Environment.ConstDecl.ofType stagedName stagedType
      senv := senv.addConst decl
    pure (senv, targetExpr')
  pure <|
              match convert.run {} with
              | .error err => Except.error err
              | .ok ((senv, targetExpr'), st) => Except.ok (senv, targetExpr', st)

private def buildStagedEnvSingleWithInsts
    (env : Lean.Environment)
    (targetName : Name)
    (closure : Array Name)
    (targetExpr : Lean.Expr) : IO (Except String (SEnv × SExpr × InternState)) := do
  let seeds :=
    closure.foldl (init := #[targetName, natConstName, stringConstName, ofNatConstName, instOfNatNatConstName]) fun acc name =>
      if acc.contains name then acc else acc.push name
  let normTargetExprResult ← lowerProjExpr env targetExpr
  match normTargetExprResult with
  | .error err => pure (.error err)
  | .ok normTargetExpr => do
      let targetInstsResult := collectConstLevelInsts normTargetExpr
      match targetInstsResult with
      | .error err => pure (.error err)
      | .ok targetInsts => do
          let mut insts := targetInsts
          let mut failed : Option String := none
          for _ in [:seeds.size.succ] do
            if failed.isSome then
              pure ()
            else
              let startSize := insts.size
              for name in seeds do
                if failed.isSome then
                  pure ()
                else
                  match envConstInfo? env name with
                  | none => pure ()
                  | some ci =>
                      match ← loweredConstPayloadWithInsts env insts name ci targetName with
                      | .error err =>
                          failed := some err
                      | .ok (normType, normValue?) =>
                          match collectConstLevelInsts normType insts with
                          | .error err =>
                              failed := some err
                          | .ok next =>
                              insts := next
                          match normValue? with
                          | none => pure ()
                          | some normValue =>
                              match collectConstLevelInsts normValue insts with
                              | .error err =>
                                  failed := some err
                              | .ok next =>
                                  insts := next
              if failed.isNone && insts.size == startSize then
                break
          match failed with
          | some err => pure (.error err)
          | none => do
              let normTargetExpr := eraseConstLevelInsts normTargetExpr
              let mut normalizedDecls : Array (Name × Lean.Expr × Option Lean.Expr) := #[]
              for name in seeds do
                match envConstInfo? env name with
                | none => pure ()
                | some ci =>
                    let payloadResult ← loweredConstPayloadWithInsts env insts name ci targetName
                    match payloadResult with
                    | .error err => return Except.error err
                    | .ok (normType, normValue?) =>
                        normalizedDecls := normalizedDecls.push (name, normType, normValue?)
              let convert : ConvertM (SEnv × SExpr) := do
                let targetExpr' ← stageExpr normTargetExpr
                let natId ← internName natConstName
                let stringId ← internName stringConstName
                let stBeforeSpecs ← get
                let (casesOnSpecs, stAfterSpecs) ←
                  match semanticCasesOnSpecs env seeds stBeforeSpecs with
                  | .ok result => pure result
                  | .error err => throw err
                set stAfterSpecs
                let litTypeFn := fun lit =>
                  match lit with
                  | LeanKernel.Literal.natVal _ => some (.const natId [])
                  | LeanKernel.Literal.strVal _ => some (.const stringId [])
                let mut senv : SEnv :=
                  { beqName := fun a b => a == b
                    consts := []
                    casesOnSpecs := casesOnSpecs
                    mvarType? := fun _ => none
                    litType? := litTypeFn
                  }
                for (name, normType, normValue?) in normalizedDecls do
                  let stagedName ← internName name
                  let stagedType ← stageExpr normType
                  let stagedValue? <-
                    if name == targetName then
                      pure none
                    else
                      match normValue? with
                      | some normValue => do
                          let value' ← stageExpr normValue
                          pure (some value')
                      | none => pure none
                  let decl : SConstDecl :=
                    match stagedValue? with
                    | some value => Environment.ConstDecl.ofDef stagedName stagedType value
                    | none => Environment.ConstDecl.ofType stagedName stagedType
                  senv := senv.addConst decl
                pure (senv, targetExpr')
              pure <|
                match convert.run {} with
                | .error err => Except.error err
                | .ok ((senv, targetExpr'), st) => Except.ok (senv, targetExpr', st)

private def nodeToJson (n : SKYGraph.Node OracleRef) : Json :=
  match n with
  | .combK => Json.mkObj [("tag", Json.str "K")]
  | .combS => Json.mkObj [("tag", Json.str "S")]
  | .combY => Json.mkObj [("tag", Json.str "Y")]
  | .app f a => Json.mkObj [("tag", Json.str "app"), ("f", toJson f), ("a", toJson a)]
  | .oracle _ => Json.mkObj [("tag", Json.str "oracle")]

private partial def collectReachableStateIds
    (s : SKYMachineBounded.State OracleRef)
    (todo : List Nat)
    (seen : Std.HashSet Nat := {}) : Std.HashSet Nat :=
  match todo with
  | [] => seen
  | id :: rest =>
      if seen.contains id then
        collectReachableStateIds s rest seen
      else
        let seen := seen.insert id
        match s.node? id with
        | some (.app f a) => collectReachableStateIds s (f :: a :: rest) seen
        | some _ => collectReachableStateIds s rest seen
        | none => collectReachableStateIds s rest seen

private def compactState (s : SKYMachineBounded.State OracleRef) : SKYMachineBounded.State OracleRef :=
  let reachable :=
    collectReachableStateIds s (s.focus :: s.stack)
      |>.toArray
      |>.qsort (fun a b => a < b)
  let idMap :=
    reachable.foldl (init := ({} : Std.HashMap Nat Nat)) fun acc oldId =>
      acc.insert oldId acc.size
  let nodes :=
    reachable.map fun oldId =>
      match s.node? oldId with
      | some (.app f a) =>
          let f' := (idMap.get? f).getD 0
          let a' := (idMap.get? a).getD 0
          SKYGraph.Node.app f' a'
      | some .combK => SKYGraph.Node.combK
      | some .combS => SKYGraph.Node.combS
      | some .combY => SKYGraph.Node.combY
      | some (.oracle r) => SKYGraph.Node.oracle r
      | none => SKYGraph.Node.combK
  let focus := (idMap.get? s.focus).getD 0
  let stack := s.stack.map (fun oldId => (idMap.get? oldId).getD 0)
  { nodes := nodes, focus := focus, stack := stack }

private def stateToJson (maxNodes fuel : Nat) (s : SKYMachineBounded.State OracleRef) : Json :=
  let compact := compactState s
  Json.mkObj
    [ ("maxNodes", toJson maxNodes)
    , ("fuel", toJson fuel)
    , ("rawNodesUsed", toJson s.nodes.size)
    , ("nodesUsed", toJson compact.nodes.size)
    , ("focus", toJson compact.focus)
    , ("stack", toJson compact.stack.toArray)
    , ("nodes", Json.arr (compact.nodes.map nodeToJson))
    ]

private def oracleEvalFalse : OracleRef → Bool := fun _ => false

private def matchesCombAt (s : SKYMachineBounded.State OracleRef) (id : Nat) : Comb → Bool
  | .K =>
      match s.node? id with
      | some .combK => true
      | _ => false
  | .S =>
      match s.node? id with
      | some .combS => true
      | _ => false
  | .Y =>
      match s.node? id with
      | some .combY => true
      | _ => false
  | .I => matchesCombAt s id (Comb.app Comb.K Comb.K)
  | .app f a =>
      match s.node? id with
      | some (.app fId aId) => matchesCombAt s fId f && matchesCombAt s aId a
      | _ => false

private def combHeadArgsRev : Comb → Comb × List Comb
  | .app f a =>
      let (h, args) := combHeadArgsRev f
      (h, a :: args)
  | t => (t, [])

private def all2 (p : Nat → Comb → Bool) : List Nat → List Comb → Bool
  | [], [] => true
  | i :: is, t :: ts => p i t && all2 p is ts
  | _, _ => false

private def matchesCombSpine (s : SKYMachineBounded.State OracleRef) (focus : Nat) (stack : List Nat) (t : Comb) : Bool :=
  let (head, argsRev) := combHeadArgsRev t
  let args := argsRev.reverse
  matchesCombAt s focus head && all2 (fun i a => matchesCombAt s i a) stack args

private def compileExpectedState (cfg : Cfg) (expectedTerm : Comb) : Except String (SKYMachineBounded.State OracleRef) := do
  -- Keep the expected side on the same weak-head surface as the bounded machine.
  -- `Meta.whnf` gives a Lean weak-head result, and the bounded machine implements
  -- leftmost-outermost weak-head reduction, so comparing against a fully normalized
  -- `SKYExec.reduceFuel` term can introduce false mismatches inside unreduced payloads.
  let rec runExpected (fuel : Nat) (s : SKYMachineBounded.State OracleRef) : Except String (SKYMachineBounded.State OracleRef) :=
    match fuel with
    | 0 => pure s
    | Nat.succ n =>
        match SKYMachineBounded.State.step (OracleRef := OracleRef) oracleEvalFalse cfg.maxNodes s with
        | .progress s' => runExpected n s'
        | .halted s' => pure s'
        | .outOfHeap _ =>
            throw s!"expected-state machine ran out of heap during reduction (maxNodes={cfg.maxNodes})"
  match SKYMachineBounded.State.compileComb? (OracleRef := OracleRef) cfg.maxNodes expectedTerm with
  | some s => runExpected cfg.fuelReduce s
  | none => throw s!"out of heap while compiling expected term; increase --max-nodes (currently {cfg.maxNodes})"

private def reduceStateWhnf
    (cfg : Cfg)
    (s : SKYMachineBounded.State OracleRef) : Except String (SKYMachineBounded.State OracleRef) := do
  let rec go (fuel : Nat) (s : SKYMachineBounded.State OracleRef) : Except String (SKYMachineBounded.State OracleRef) :=
    match fuel with
    | 0 => pure s
    | Nat.succ n =>
        match SKYMachineBounded.State.step (OracleRef := OracleRef) oracleEvalFalse cfg.maxNodes s with
        | .progress s' => go n s'
        | .halted s' => pure s'
        | .outOfHeap _ =>
            throw s!"machine ran out of heap during reduction (maxNodes={cfg.maxNodes})"
  go cfg.fuelReduce s

private partial def stateHeadArgsRev
    (s : SKYMachineBounded.State OracleRef)
    (focus : Nat)
    (argsRev : List Nat := []) : Nat × List Nat :=
  match s.node? focus with
  | some (.app f a) => stateHeadArgsRev s f (a :: argsRev)
  | _ => (focus, argsRev)

private partial def matchesStateAt
    (lhs rhs : SKYMachineBounded.State OracleRef)
    (lid rid : Nat) : Bool :=
  match lhs.node? lid, rhs.node? rid with
  | some .combK, some .combK => true
  | some .combS, some .combS => true
  | some .combY, some .combY => true
  | some (.oracle _), some (.oracle _) => true
  | some (.app lf la), some (.app rf ra) =>
      matchesStateAt lhs rhs lf rf && matchesStateAt lhs rhs la ra
  | _, _ => false

private def all2State
    (lhs rhs : SKYMachineBounded.State OracleRef)
    : List Nat → List Nat → Bool
  | [], [] => true
  | l :: ls, r :: rs => matchesStateAt lhs rhs l r && all2State lhs rhs ls rs
  | _, _ => false

private def matchesStateSpine
    (lhs : SKYMachineBounded.State OracleRef)
    (lfocus : Nat)
    (lstack : List Nat)
    (rhs : SKYMachineBounded.State OracleRef)
    (rfocus : Nat)
    (rstack : List Nat) : Bool :=
  let (lhead, largsRev) := stateHeadArgsRev lhs lfocus lstack
  let (rhead, rargsRev) := stateHeadArgsRev rhs rfocus rstack
  let largs := largsRev.reverse
  let rargs := rargsRev.reverse
  matchesStateAt lhs rhs lhead rhead && all2State lhs rhs largs rargs

private partial def matchesStateSpineObservational
    (cfg : Cfg)
    (lhs : SKYMachineBounded.State OracleRef)
    (lfocus : Nat)
    (lstack : List Nat)
    (rhs : SKYMachineBounded.State OracleRef)
    (rfocus : Nat)
    (rstack : List Nat) : Except String Bool := do
  let lhsWhnf ← reduceStateWhnf cfg { lhs with focus := lfocus, stack := lstack }
  let rhsWhnf ← reduceStateWhnf cfg { rhs with focus := rfocus, stack := rstack }
  let (lhead, largsRev) := stateHeadArgsRev lhsWhnf lhsWhnf.focus lhsWhnf.stack
  let (rhead, rargsRev) := stateHeadArgsRev rhsWhnf rhsWhnf.focus rhsWhnf.stack
  let largs := largsRev.reverse
  let rargs := rargsRev.reverse
  let sameHead :=
    match lhsWhnf.node? lhead, rhsWhnf.node? rhead with
    | some .combK, some .combK => true
    | some .combS, some .combS => true
    | some .combY, some .combY => true
    | some (.oracle _), some (.oracle _) => true
    | _ , _ => false
  if !sameHead then
    pure false
  else
    let rec all2Obs : List Nat → List Nat → Except String Bool
      | [], [] => pure true
      | l :: ls, r :: rs => do
          let same ← matchesStateSpineObservational cfg lhsWhnf l [] rhsWhnf r []
          if same then
            all2Obs ls rs
          else
            pure false
      | _, _ => pure false
    all2Obs largs rargs

private def runMachineExport
    (cfg : Cfg)
    (decodeTerm expectedTerm : Comb) : Except String (Json × Json × Json × Json × Nat × Nat × Nat × Bool) := do
  let s0 <-
    match SKYMachineBounded.State.compileComb? (OracleRef := OracleRef) cfg.maxNodes decodeTerm with
    | some s => pure s
    | none => throw s!"out of heap during compilation; increase --max-nodes (currently {cfg.maxNodes})"
  let expectedState ← compileExpectedState cfg expectedTerm
  let expectedJson := stateToJson cfg.maxNodes cfg.fuelReduce expectedState
  if cfg.machineExportOnly then
    let machineJson := stateToJson cfg.maxNodes cfg.fuelReduce s0
    pure (machineJson, expectedJson, Json.null, Json.arr #[], 0, s0.stack.length, s0.nodes.size, true)
  else

    let traceEnabled := cfg.phaseTrace.isSome
    let rec runWithStats (fuel : Nat) (s : SKYMachineBounded.State OracleRef)
        (stepsTaken maxStack maxNodesUsed : Nat) (traceRev : List Json) :
        Nat × Nat × Nat × List Json × SKYMachineBounded.State.StepResult OracleRef :=
      let traceRev :=
        if traceEnabled then
          HeytingLean.CLI.SKYTraceJson.traceSampleToJson stepsTaken s :: traceRev
        else
          traceRev
      match fuel with
      | 0 => (stepsTaken, maxStack, maxNodesUsed, traceRev, .halted s)
      | Nat.succ n =>
          match SKYMachineBounded.State.step (OracleRef := OracleRef) oracleEvalFalse cfg.maxNodes s with
          | .progress s' =>
              let maxStack' := Nat.max maxStack s'.stack.length
              let maxNodesUsed' := Nat.max maxNodesUsed s'.nodes.size
              runWithStats n s' (stepsTaken + 1) maxStack' maxNodesUsed' traceRev
          | .halted s' => (stepsTaken, maxStack, maxNodesUsed, traceRev, .halted s')
          | .outOfHeap s' => (stepsTaken, maxStack, maxNodesUsed, traceRev, .outOfHeap s')

    let (stepsTaken, maxStack, maxNodesUsed, traceRev, out) :=
      runWithStats cfg.fuelReduce s0 0 s0.stack.length s0.nodes.size []

    let finalState :=
      match out with
      | .progress s => s
      | .halted s => s
      | .outOfHeap s => s

    match out with
    | .outOfHeap _ =>
        throw s!"machine ran out of heap during reduction (maxNodes={cfg.maxNodes})"
    | _ => pure ()

    let matchesExpected :=
      matchesStateSpine
        finalState
        finalState.focus
        finalState.stack
        expectedState
        expectedState.focus
        expectedState.stack
    let machineJson := stateToJson cfg.maxNodes cfg.fuelReduce s0
    let observedJson := stateToJson cfg.maxNodes cfg.fuelReduce finalState
    let finalJson := expectedJson
    let traceJson := Json.arr traceRev.reverse.toArray
    pure (machineJson, finalJson, observedJson, traceJson, stepsTaken, maxStack, maxNodesUsed, matchesExpected)

private def runMachineExportObservational
    (cfg : Cfg)
    (decodeTerm expectedTerm : Comb) : Except String (Json × Json × Json × Json × Nat × Nat × Nat × Bool) := do
  let s0 <-
    match SKYMachineBounded.State.compileComb? (OracleRef := OracleRef) cfg.maxNodes decodeTerm with
    | some s => pure s
    | none => throw s!"out of heap during compilation; increase --max-nodes (currently {cfg.maxNodes})"
  let expectedState ← compileExpectedState cfg expectedTerm
  let expectedJson := stateToJson cfg.maxNodes cfg.fuelReduce expectedState
  if cfg.machineExportOnly then
    let machineJson := stateToJson cfg.maxNodes cfg.fuelReduce s0
    pure (machineJson, expectedJson, Json.null, Json.arr #[], 0, s0.stack.length, s0.nodes.size, true)
  else

    let traceEnabled := cfg.phaseTrace.isSome
    let rec runWithStats (fuel : Nat) (s : SKYMachineBounded.State OracleRef)
        (stepsTaken maxStack maxNodesUsed : Nat) (traceRev : List Json) :
        Nat × Nat × Nat × List Json × SKYMachineBounded.State.StepResult OracleRef :=
      let traceRev :=
        if traceEnabled then
          HeytingLean.CLI.SKYTraceJson.traceSampleToJson stepsTaken s :: traceRev
        else
          traceRev
      match fuel with
      | 0 => (stepsTaken, maxStack, maxNodesUsed, traceRev, .halted s)
      | Nat.succ n =>
          match SKYMachineBounded.State.step (OracleRef := OracleRef) oracleEvalFalse cfg.maxNodes s with
          | .progress s' =>
              let maxStack' := Nat.max maxStack s'.stack.length
              let maxNodesUsed' := Nat.max maxNodesUsed s'.nodes.size
              runWithStats n s' (stepsTaken + 1) maxStack' maxNodesUsed' traceRev
          | .halted s' => (stepsTaken, maxStack, maxNodesUsed, traceRev, .halted s')
          | .outOfHeap s' => (stepsTaken, maxStack, maxNodesUsed, traceRev, .outOfHeap s')

    let (stepsTaken, maxStack, maxNodesUsed, traceRev, out) :=
      runWithStats cfg.fuelReduce s0 0 s0.stack.length s0.nodes.size []

    let finalState :=
      match out with
      | .progress s => s
      | .halted s => s
      | .outOfHeap s => s

    match out with
    | .outOfHeap _ =>
        throw s!"machine ran out of heap during reduction (maxNodes={cfg.maxNodes})"
    | _ => pure ()

    let matchesExpected ←
      matchesStateSpineObservational
        cfg
        finalState
        finalState.focus
        finalState.stack
        expectedState
        expectedState.focus
        expectedState.stack
    let machineJson := stateToJson cfg.maxNodes cfg.fuelReduce s0
    let observedJson := stateToJson cfg.maxNodes cfg.fuelReduce finalState
    let finalJson := expectedJson
    let traceJson := Json.arr traceRev.reverse.toArray
    pure (machineJson, finalJson, observedJson, traceJson, stepsTaken, maxStack, maxNodesUsed, matchesExpected)

private def boolTagTerm (b : Bool) : Comb :=
  if b then SKYExec.bTrue else SKYExec.bFalse

private def declJsonBase (moduleName : Name) (declName : Name) (kind : String) : List (String × Json) :=
  [ ("module", Json.str moduleName.toString)
  , ("decl_name", Json.str declName.toString)
  , ("decl_kind", Json.str kind)
  ]

private def skipDeclJson
    (moduleName : Name)
    (declName : Name)
    (kind : String)
    (reason : String) : Json :=
  Json.mkObj <| declJsonBase moduleName declName kind ++
    [ ("eligible", Json.bool false)
    , ("skip_reason", Json.str reason)
    , ("operations", Json.arr #[])
    ]

private def listDeclJson
    (moduleName : Name)
    (declName : Name)
    (kind : String) : Json :=
  Json.mkObj <| declJsonBase moduleName declName kind ++
    [ ("listed_only", Json.bool true) ]

private def ownerModuleOf (env : Lean.Environment) (name : Name) : Name :=
  HeytingLean.Util.moduleOwnerOf env name

private def declSelectionPriority (env : Lean.Environment) (declName : Name) : Nat :=
  if declName.isInternal || declName.isInternalDetail || Lean.isPrivateName declName then
    2
  else if env.isProjectionFn declName then
    1
  else
    0

private def moduleDecls (env : Lean.Environment) (moduleName : Name) : Array (Name × ConstantInfo) :=
  let raw := env.constants.fold (init := #[]) fun acc name info =>
    if ownerModuleOf env name == moduleName then
      acc.push (name, info)
    else
      acc
  raw.qsort (fun a b =>
    let pa := declSelectionPriority env a.1
    let pb := declSelectionPriority env b.1
    if pa == pb then
      a.1.toString < b.1.toString
    else
      pa < pb)

private def includedDecls (env : Lean.Environment) (moduleName : Name) (includeDecls : Array Name) :
    Array (Name × ConstantInfo) :=
  includeDecls.foldl (init := #[]) fun acc declName =>
    match env.constants.find? declName with
    | some ci =>
        let owner := ownerModuleOf env declName
        if owner == moduleName then
          acc.push (declName, ci)
        else
          acc
    | none => acc

private def writeOutput (cfg : Cfg) (payload : Json) : IO Unit := do
  let text := payload.pretty
  match cfg.output with
  | some path =>
      IO.FS.writeFile path (text ++ "\n")
      IO.eprintln s!"[verified_check] wrote {path}"
  | none =>
      IO.println text

private def jsonNatD (j : Json) (field : String) : Nat :=
  match j.getObjValAs? Nat field with
  | .ok n => n
  | .error _ => 0

private def jsonBoolD (j : Json) (field : String) : Bool :=
  match j.getObjValAs? Bool field with
  | .ok b => b
  | .error _ => false

private def jsonStrD (j : Json) (field : String) : String :=
  match j.getObjValAs? String field with
  | .ok s => s
  | .error _ => ""

private def operationReplayEligible (operation : Json) : Bool :=
  jsonBoolD operation "eligible" && !jsonBoolD operation "semantic_check_skipped"

private def traceCfgForExport (cfg : Cfg) : IO Cfg := do
  pure cfg

private def collectSkyObligations (exports : Array Json) : Array VerifierObligation := Id.run do
  let mut obligations : Array VerifierObligation := #[]
  for decl in exports do
    let declKind := jsonStrD decl "decl_kind"
    let declName := jsonStrD decl "decl_name"
    match decl.getObjVal? "trace_entries" with
    | .ok (.arr entries) =>
        for entry in entries do
          if jsonBoolD entry "gpu_verifiable" && jsonBoolD entry "eligible" then
            match entry.getObjVal? "machine_json", entry.getObjVal? "final_json" with
            | .ok machineJson, .ok finalJson =>
                let declName := jsonStrD entry "decl_name"
                let traceRole := jsonStrD entry "trace_role"
                let ident := s!"{declName}:{traceRole}:whnf"
                obligations := obligations.push
                  { id := ident
                    declName := declName
                    declKind := declKind
                    traceRole := traceRole
                    traceGrain := "whnf"
                    verificationMode := "whnf_call"
                    replayKind := .whnfCall
                    joinGroup := declName
                    deps := #[]
                    projectedBetaZetaSteps := jsonNatD entry "projected_beta_zeta_steps"
                    stepCount := jsonNatD entry "step_count"
                    deltaIotaSteps := jsonNatD entry "delta_iota_steps"
                    nodeCount := jsonNatD entry "node_count"
                    inputExprRepr := jsonStrD entry "input_expr_repr"
                    outputExprRepr := jsonStrD entry "output_expr_repr"
                    nativeWhnfRepr := jsonStrD entry "native_whnf_repr"
                    machineJson := machineJson
                    finalJson := finalJson
                  }
            | _, _ => ()
          else
            ()
    | _ => ()
    match decl.getObjVal? "operations" with
    | .ok (.arr operations) =>
        for operation in operations do
          if operationReplayEligible operation then
            match operation.getObjVal? "machine_json" with
            | .ok machineJson =>
                let opType := jsonStrD operation "op_type"
                let ident := s!"{declName}:{opType}"
                let depRefs :=
                  match operation.getObjVal? "dependency_op_types" with
                  | .ok (.arr deps) =>
                      deps.foldl (init := #[]) fun acc dep =>
                        match dep with
                        | .str depType =>
                            acc.push { id := s!"{declName}:{depType}", edgeKind := "operation_dep" }
                        | _ => acc
                  | _ => #[]
                let finalJson :=
                  match operation.getObjVal? "final_json" with
                  | .ok j => j
                  | .error _ => Json.null
                obligations := obligations.push
                  { id := ident
                    declName := declName
                    declKind := declKind
                    traceRole := "declaration_operation"
                    traceGrain := "machine_export"
                    verificationMode := opType
                    replayKind := .tagCheck
                    joinGroup := declName
                    deps := depRefs
                    projectedBetaZetaSteps := 0
                    stepCount := jsonNatD operation "steps_taken"
                    deltaIotaSteps := 0
                    nodeCount := jsonNatD operation "node_count"
                    inputExprRepr := jsonStrD operation "input_expr_repr"
                    outputExprRepr :=
                      let out := jsonStrD operation "native_output_repr"
                      if out.isEmpty then
                        if jsonBoolD operation "native_output_bool" then "true" else "false"
                      else
                        out
                    nativeWhnfRepr := ""
                    expectedTagTerm := jsonStrD operation "expected_tag_term"
                    machineJson := machineJson
                    finalJson := finalJson
                  }
            | .error _ => ()
          else
            ()
    | _ => ()
  pure obligations

private def buildSkyArtifact (cfg : Cfg) (exports : Array Json) (selectedCount : Nat) (declCount : Nat) : Json :=
  let obligations := collectSkyObligations exports
  let eligibleEntries :=
    exports.foldl (init := 0) fun acc decl =>
      let traceCount :=
        match decl.getObjVal? "trace_entries" with
        | .ok (.arr entries) =>
            entries.foldl (init := 0) fun entryAcc entry =>
              if jsonBoolD entry "gpu_verifiable" then entryAcc + 1 else entryAcc
        | _ => 0
      let operationCount :=
        match decl.getObjVal? "operations" with
        | .ok (.arr operations) =>
            operations.foldl (init := 0) fun opAcc operation =>
              if operationReplayEligible operation then opAcc + 1 else opAcc
        | _ => 0
      acc + traceCount + operationCount
  let hasTraceEntries :=
    exports.any fun decl =>
      match decl.getObjVal? "trace_entries" with
      | .ok (.arr entries) => !entries.isEmpty
      | _ => false
  let hasOperations :=
    exports.any fun decl =>
      match decl.getObjVal? "operations" with
      | .ok (.arr operations) => !operations.isEmpty
      | _ => false
  let artifactTraceGrain :=
    if hasTraceEntries && hasOperations then "mixed"
    else if hasTraceEntries then "whnf"
    else "machine_export"
  let honestAssessment :=
    if hasOperations && !hasTraceEntries then
      "This artifact packages only semantically certified machine-exported declaration operations from verified_check. Machine-export-only rows whose staged semantic check was skipped remain diagnostic in the JSON report but are omitted from the portable SKY obligation artifact."
    else if hasOperations then
      "This artifact mixes semantically certified machine-exported declaration operations with WHNF-grain trace-selected leaves. Operation rows whose staged semantic check was skipped remain diagnostic-only in the JSON report and are omitted from the portable SKY obligation artifact."
    else
      "This artifact packages only WHNF-grain obligations whose projected beta/zeta portion compiled to bounded SKY machine states. Delta and iota remain native-only and do not appear as standalone SKY obligations."
  toJson <|
    ({ moduleName := cfg.moduleName.toString
       traceGrain := artifactTraceGrain
       joinStrategy := "declaration_all_clean"
       selectedDeclarations := selectedCount
       totalDeclarations := declCount
       traceMaxSteps := cfg.traceMaxSteps
       fuelWhnf := cfg.fuelWhnf
       fuelDefEq := cfg.fuelDefEq
       fuelReduce := cfg.fuelReduce
       maxNodes := cfg.maxNodes
       eligibleTraceEntries := eligibleEntries
       obligations := obligations
       honestAssessment := honestAssessment
     } : VerifierArtifact)

private def writeSkyArtifact (cfg : Cfg) (payload : Json) : IO Unit := do
  match cfg.exportSky with
  | none => pure ()
  | some path =>
      IO.FS.writeFile path (payload.pretty ++ "\n")
      IO.eprintln s!"[verified_check] wrote {path}"

private def withElapsedMs (action : IO α) : IO (α × Nat) := do
  let startMs ← IO.monoMsNow
  let value ← action
  let endMs ← IO.monoMsNow
  pure (value, endMs - startMs)

private def nativeWhnf (env : Lean.Environment) (e : Lean.Expr) : IO (Except String (Lean.Expr × Nat)) := do
  try
    let (result, elapsed) ← withElapsedMs <| runMetaAtEnv env do
      let out ← Meta.whnf e
      instantiateMVars out
    pure (.ok (result, elapsed))
  catch ex =>
    pure (.error s!"native whnf failed: {ex}")

private def nativeInfer (env : Lean.Environment) (e : Lean.Expr) : IO (Except String (Lean.Expr × Nat)) := do
  try
    let (result, elapsed) ← withElapsedMs <| runMetaAtEnv env do
      let ty ← Meta.inferType e
      instantiateMVars ty
    pure (.ok (result, elapsed))
  catch ex =>
    pure (.error s!"native inferType failed: {ex}")

private def nativeDefEq (env : Lean.Environment) (lhs rhs : Lean.Expr) : IO (Except String (Bool × Nat)) := do
  try
    let (result, elapsed) ← withElapsedMs <| runMetaAtEnv env do
      Meta.isDefEq lhs rhs
    pure (.ok (result, elapsed))
  catch ex =>
    pure (.error s!"native isDefEq failed: {ex}")

private def nativeCheck (env : Lean.Environment) (value declType : Lean.Expr) : IO (Except String (Bool × Nat)) := do
  try
    let (result, elapsed) ← withElapsedMs <| runMetaAtEnv env do
      let inferredType ← Meta.inferType value
      Meta.isDefEq inferredType declType
    pure (.ok (result, elapsed))
  catch ex =>
    pure (.error s!"native check failed: {ex}")

private def buildNativeDirect
    (env : Lean.Environment)
    (declType declValue : Lean.Expr) : IO (Except String NativeDirect) := do
  let loweredTypeResult ← lowerProjExpr env declType
  let loweredValueResult ← lowerProjExpr env declValue
  match loweredTypeResult, loweredValueResult with
  | .error err, _ => pure (.error err)
  | _, .error err => pure (.error err)
  | .ok loweredType, .ok loweredValue => do
      let whnfTypeResult ← nativeWhnf env declType
      let whnfValueResult ← nativeWhnf env declValue
      let inferTypeResult ← nativeInfer env declType
      let inferValueResult ← nativeInfer env declValue
      match whnfTypeResult, whnfValueResult, inferTypeResult, inferValueResult with
      | .error err, _, _, _ => pure (.error err)
      | _, .error err, _, _ => pure (.error err)
      | _, _, .error err, _ => pure (.error err)
      | _, _, _, .error err => pure (.error err)
      | .ok (whnfType, whnfTypeMs), .ok (whnfValue, whnfValueMs), .ok (inferSort, inferTypeMs), .ok (inferType, inferValueMs) => do
          let loweredWhnfTypeResult ← lowerProjExpr env whnfType
          let loweredWhnfValueResult ← lowerProjExpr env whnfValue
          let loweredInferSortResult ← lowerProjExpr env inferSort
          let loweredInferTypeResult ← lowerProjExpr env inferType
          match loweredWhnfTypeResult, loweredWhnfValueResult, loweredInferSortResult, loweredInferTypeResult with
          | .error err, _, _, _ => pure (.error err)
          | _, .error err, _, _ => pure (.error err)
          | _, _, .error err, _ => pure (.error err)
          | _, _, _, .error err => pure (.error err)
          | .ok loweredWhnfType, .ok loweredWhnfValue, .ok loweredInferSort, .ok loweredInferType => do
              let defeqResult ← nativeDefEq env inferType declType
              let checkResult ← nativeCheck env loweredValue declType
              match defeqResult, checkResult with
              | .error err, _ => pure (.error err)
              | _, .error err => pure (.error err)
              | .ok (defeqValue, defeqMs), .ok (checkValue, checkMs) =>
                  pure <| .ok
                    { loweredType := loweredType
                      loweredValue := loweredValue
                      loweredWhnfType := loweredWhnfType
                      loweredWhnfValue := loweredWhnfValue
                      loweredInferSort := loweredInferSort
                      loweredInferType := loweredInferType
                      defeqInferredDeclared := defeqValue
                      checkValue := checkValue
                      whnfTypeMs := whnfTypeMs
                      whnfValueMs := whnfValueMs
                      inferTypeMs := inferTypeMs
                      inferValueMs := inferValueMs
                      defeqMs := defeqMs
                      checkMs := checkMs }

private def singleWhnfOp? (cfg : Cfg) : Option OpKind :=
  if h : cfg.onlyOpKinds.size = 1 then
    match cfg.onlyOpKinds[0] with
    | .whnfType => some .whnfType
    | .whnfValue => some .whnfValue
    | _ => none
  else
    none

private def singleDefEqOp? (cfg : Cfg) : Bool :=
  if h : cfg.onlyOpKinds.size = 1 then
    cfg.onlyOpKinds[0] = .defEqInferredDeclared
  else
    false

private def singleDirectOp? (cfg : Cfg) : Option OpKind :=
  if h : cfg.onlyOpKinds.size = 1 then
    match cfg.onlyOpKinds[0] with
    | .inferTypeSort => some .inferTypeSort
    | _ => none
  else
    none

private def ensureClassicBracketMode (cfg : Cfg) (what : String) : Except String Unit := do
  match cfg.bracketMode with
  | .classic => pure ()
  | .bulk => throw s!"{what}: bracket mode 'bulk' is not supported on the verified_check executable path"

private def buildWhnfLeafDirect
    (env : Lean.Environment)
    (kind : OpKind)
    (declType declValue : Lean.Expr) : IO (Except String WhnfLeafDirect) := do
  let (loweredDeclTypeResult, lowerDeclTypeMs) ← withElapsedMs <| lowerProjExpr env declType
  match loweredDeclTypeResult with
  | .error err => pure (.error err)
  | .ok loweredDeclType =>
      let inputExpr := match kind with | .whnfType => declType | .whnfValue => declValue | _ => declType
      let (loweredInputResult, lowerInputMs) ← withElapsedMs <| lowerProjExpr env inputExpr
      match loweredInputResult with
      | .error err => pure (.error err)
      | .ok loweredInput => do
          let whnfResult ← nativeWhnf env inputExpr
          match whnfResult with
          | .error err => pure (.error err)
          | .ok (whnfOut, nativeMs) => do
              let (loweredOutputResult, lowerOutputMs) ← withElapsedMs <| lowerProjExpr env whnfOut
              match loweredOutputResult with
              | .error err => pure (.error err)
              | .ok loweredOutput =>
                  pure <| .ok
                    { inputExpr := inputExpr
                      loweredDeclType := loweredDeclType
                      loweredInput := loweredInput
                      loweredOutput := loweredOutput
                      nativeMs := nativeMs
                      lowerDeclTypeMs := lowerDeclTypeMs
                      lowerInputMs := lowerInputMs
                      lowerOutputMs := lowerOutputMs }

private def buildDefEqLeafDirect
    (env : Lean.Environment)
    (declType declValue : Lean.Expr) : IO (Except String DefEqLeafDirect) := do
  let inferResult ← nativeInfer env declValue
  match inferResult with
  | .error err => pure (.error err)
  | .ok (inferType, inferMs) => do
      let declWhnfResult ← nativeWhnf env declType
      let inferWhnfResult ← nativeWhnf env inferType
      match declWhnfResult, inferWhnfResult with
      | .error err, _ => pure (.error err)
      | _, .error err => pure (.error err)
      | .ok (declTypeWhnf, whnfDeclTypeMs), .ok (inferTypeWhnf, whnfInferTypeMs) => do
          let (loweredDeclTypeResult, lowerDeclTypeMs) ← withElapsedMs <| lowerProjExpr env declTypeWhnf
          let (loweredInferTypeResult, lowerInferTypeMs) ← withElapsedMs <| lowerProjExpr env inferTypeWhnf
          match loweredDeclTypeResult, loweredInferTypeResult with
          | .error err, _ => pure (.error err)
          | _, .error err => pure (.error err)
          | .ok loweredDeclType, .ok loweredInferType => do
              let defeqResult ← nativeDefEq env inferType declType
              match defeqResult with
              | .error err => pure (.error err)
              | .ok (nativeBool, defeqMs) =>
                  pure <| .ok
                    { declTypeWhnf := declTypeWhnf
                      inferTypeWhnf := inferTypeWhnf
                      loweredDeclType := loweredDeclType
                      loweredInferType := loweredInferType
                      inferMs := inferMs
                      whnfDeclTypeMs := whnfDeclTypeMs
                      whnfInferTypeMs := whnfInferTypeMs
                      defeqMs := defeqMs
                      nativeBool := nativeBool
                      lowerDeclTypeMs := lowerDeclTypeMs
                      lowerInferTypeMs := lowerInferTypeMs }

private def eqPayload? : Lean.Expr → Option EqPayload
  | .app (.app (.app (.const ``Eq _) typeExpr) lhsExpr) rhsExpr =>
      some { typeExpr := typeExpr, lhsExpr := lhsExpr, rhsExpr := rhsExpr }
  | _ => none

private def reflEqPayloadWitness? (leaf : DefEqLeafDirect) : Option (Lean.Expr × Lean.Expr × Lean.Expr) :=
  match eqPayload? leaf.declTypeWhnf, eqPayload? leaf.inferTypeWhnf with
  | some declEq, some inferEq =>
      if declEq.typeExpr == inferEq.typeExpr &&
         declEq.lhsExpr == inferEq.lhsExpr &&
         inferEq.rhsExpr == inferEq.lhsExpr then
        some (declEq.typeExpr, inferEq.rhsExpr, declEq.rhsExpr)
      else
        none
  | _, _ => none

private def isSortZeroExpr : Lean.Expr → Bool
  | .sort .zero => true
  | _ => false

private abbrev KernelL : Type := WHNFSKY.L

private def lv (s : String) : KernelL := WHNFSKY.L.v s
private def lapp (f a : KernelL) : KernelL := WHNFSKY.L.app f a
private def lapp2 (f a b : KernelL) : KernelL := WHNFSKY.L.app2 f a b
private def lapp3 (f a b c : KernelL) : KernelL := WHNFSKY.L.app3 f a b c
private def lapp4 (f a b c d : KernelL) : KernelL := WHNFSKY.L.app4 f a b c d
private def llam (x : String) (body : KernelL) : KernelL := WHNFSKY.L.lam x body
private def llam2 (x y : String) (body : KernelL) : KernelL := WHNFSKY.L.lam2 x y body
private def llam3 (x y z : String) (body : KernelL) : KernelL := WHNFSKY.L.lam3 x y z body
private def llam4 (a b c d : String) (body : KernelL) : KernelL := WHNFSKY.L.lam4 a b c d body

private def localWhnfStepFullSky : KernelL :=
  llam3 "env" "rules" "e" <|
    WHNFSKY.optCase (lapp2 WHNFIotaSKY.iotaStepSky (lv "rules") (lv "e"))
      (lapp2 WHNFDeltaSKY.whnfStepDeltaSky (lv "env") (lv "e"))
      (llam "e'" (WHNFSKY.optSome (lv "e'")))

private def localWhnfFromEnvRules : KernelL :=
  llam2 "env" "rules" <|
    llam2 "fuel" "e" <|
      lapp4
        (lapp .Y <|
          llam "self" <|
            llam "env" <|
              llam "rules" <|
                llam "fuel" <|
                  llam "e" <|
                    WHNFSKY.natCase (lv "fuel")
                      (lv "e")
                      (llam "n" <|
                        WHNFSKY.optCase (lapp3 localWhnfStepFullSky (lv "env") (lv "rules") (lv "e"))
                          (lv "e")
                          (llam "e'" (lapp4 (lv "self") (lv "env") (lv "rules") (lv "n") (lv "e'")))))
        (lv "env")
        (lv "rules")
        (lv "fuel")
        (lv "e")

private def localConstTypeFromEnv : KernelL :=
  llam3 "env" "c" "us" (lapp2 EnvironmentSKY.constType? (lv "env") (lv "c"))

private def localLitTypeByNameIdsSky (natName stringName : KernelL) : KernelL :=
  let emptyLevels := InferSKY.listNil
  let natTyL := WHNFSKY.exprConst natName emptyLevels
  let stringTyL := WHNFSKY.exprConst stringName emptyLevels
  let natCase := llam "n" <| WHNFSKY.optSome natTyL
  let stringCase := llam "s" <| WHNFSKY.optSome stringTyL
  llam "l" <| lapp2 (lv "l") natCase stringCase

private def localInferFullSkyWithLitTypeIds : KernelL :=
  llam4 "env" "rules" "natName" "stringName" <|
    let whnf := lapp2 localWhnfFromEnvRules (lv "env") (lv "rules")
    let isDefEq := DefEqSKY.isDefEqSkyWith whnf
    let constType? := lapp localConstTypeFromEnv (lv "env")
    let litType? := localLitTypeByNameIdsSky (lv "natName") (lv "stringName")
    InferSKY.inferSkyWith constType? litType? whnf isDefEq

private def localCheckFullSkyWithLitTypeIds : KernelL :=
  llam4 "env" "rules" "natName" "stringName" <|
    let whnf := lapp2 localWhnfFromEnvRules (lv "env") (lv "rules")
    let isDefEq := DefEqSKY.isDefEqSkyWith whnf
    let constType? := lapp localConstTypeFromEnv (lv "env")
    let litType? := localLitTypeByNameIdsSky (lv "natName") (lv "stringName")
    InferSKY.checkSkyWith constType? litType? whnf isDefEq

private def localOptExprIsSomeSky : KernelL :=
  llam "o" <| WHNFSKY.optCase (lv "o") WHNFSKY.fls (llam "e" WHNFSKY.tru)

private def localOptExprIsSomeSortSky : KernelL :=
  let false4 :=
    llam "a" <| llam "b" <| llam "c" <| llam "d" WHNFSKY.fls
  let false5 :=
    llam "a" <| llam "b" <| llam "c" <| llam "d" <| llam "e" WHNFSKY.fls
  llam "o" <|
    WHNFSKY.optCase (lv "o") WHNFSKY.fls <|
      llam "e" <|
        WHNFSKY.exprCase (lv "e")
          (llam "i" WHNFSKY.fls)
          (llam "m" WHNFSKY.fls)
          (llam "u" WHNFSKY.tru)
          (llam "c" <| llam "us" WHNFSKY.fls)
          (llam "f" <| llam "a" WHNFSKY.fls)
          false4
          false4
          false5
          (llam "l" WHNFSKY.fls)

private def localULevelIsZeroSky : KernelL :=
  lapp .Y <|
    llam "self" <|
      let andSky := llam "p" <| llam "q" <| lapp2 (lv "p") (lv "q") WHNFSKY.fls
      llam "u" <|
        DefEqSKY.ulevelCase (lv "u")
          WHNFSKY.tru
          (llam "u1" WHNFSKY.fls)
          (llam "a" <| llam "b" <| lapp2 andSky (lapp (lv "self") (lv "a")) (lapp (lv "self") (lv "b")))
          (llam "a" <| llam "b" <| lapp (lv "self") (lv "b"))
          (llam "p" WHNFSKY.fls)
          (llam "m1" WHNFSKY.fls)

private def localOptExprIsSomeSortZeroSky : KernelL :=
  let false4 :=
    llam "a" <| llam "b" <| llam "c" <| llam "d" WHNFSKY.fls
  let false5 :=
    llam "a" <| llam "b" <| llam "c" <| llam "d" <| llam "e" WHNFSKY.fls
  llam "o" <|
    WHNFSKY.optCase (lv "o") WHNFSKY.fls <|
      llam "e" <|
        WHNFSKY.exprCase (lv "e")
          (llam "i" WHNFSKY.fls)
          (llam "m" WHNFSKY.fls)
          localULevelIsZeroSky
          (llam "c" <| llam "us" WHNFSKY.fls)
          (llam "f" <| llam "a" WHNFSKY.fls)
          false4
          false4
          false5
          (llam "l" WHNFSKY.fls)

private def localExprIsSortZeroSky : KernelL :=
  let false4 :=
    llam "a" <| llam "b" <| llam "c" <| llam "d" WHNFSKY.fls
  let false5 :=
    llam "a" <| llam "b" <| llam "c" <| llam "d" <| llam "e" WHNFSKY.fls
  llam "e" <|
    WHNFSKY.exprCase (lv "e")
      (llam "i" WHNFSKY.fls)
      (llam "m" WHNFSKY.fls)
      localULevelIsZeroSky
      (llam "c" <| llam "us" WHNFSKY.fls)
      (llam "f" <| llam "a" WHNFSKY.fls)
      false4
      false4
      false5
      (llam "l" WHNFSKY.fls)

private def localInferIsSomeSortZeroFullSkyWithLitTypeIds : KernelL :=
  llam4 "env" "rules" "natName" "stringName" <|
    let infer :=
      lapp4
        localInferFullSkyWithLitTypeIds
        (lv "env")
        (lv "rules")
        (lv "natName")
        (lv "stringName")
    llam3 "fuel" "ctx" "e" <|
      WHNFSKY.optCase (lapp3 infer (lv "fuel") (lv "ctx") (lv "e"))
        WHNFSKY.fls
        (llam "out" <| lapp localExprIsSortZeroSky (lv "out"))

private def optSomeWrapperSky : KernelL :=
  llam "x" <| WHNFSKY.optSome (lv "x")

private def compileExprComb (cfg : Cfg) (what : String) (e : SExpr) : Except String Comb := do
  let _ ← ensureClassicBracketMode cfg what
  match Expr.Scott.compileClosed?
      (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit)
      EnvironmentSKY.Enc.nat
      EnvironmentSKY.Enc.unit
      EnvironmentSKY.Enc.unit
      EnvironmentSKY.Enc.unit
      EnvironmentSKY.Enc.string
      e with
  | some v => pure v
  | none => throw s!"failed to compile {what} to Comb"

private def compileOptSomeExprComb (cfg : Cfg) (what : String) (e : SExpr) : Except String Comb := do
  let exprC ← compileExprComb cfg s!"{what} payload" e
  let _ ← ensureClassicBracketMode cfg what
  match Bracket.Lam.compileClosedClassic? optSomeWrapperSky with
  | some wrapC => pure (Comb.app wrapC exprC)
  | none => throw s!"failed to compile {what} option witness wrapper to Comb"

private def stagedConstId (st : InternState) (name : Name) : Except String Nat := do
  match st.names.get? name with
  | some id => pure id
  | none => throw s!"staged environment does not expose constant id for {name}"

private def compileLitAwareInferCheck (cfg : Cfg) : Except String (Comb × Comb) := do
  let _ ← ensureClassicBracketMode cfg "compile lit-aware infer/check kernel"
  match Bracket.Lam.compileClosedClassic? localInferFullSkyWithLitTypeIds,
      Bracket.Lam.compileClosedClassic? localCheckFullSkyWithLitTypeIds with
  | some inferC, some checkC => pure (inferC, checkC)
  | none, _ => throw "failed to compile lit-aware infer kernel to Comb"
  | _, none => throw "failed to compile lit-aware check kernel to Comb"

private def compileLitAwareInferSortZeroKernel (cfg : Cfg) : Except String Comb := do
  let _ ← ensureClassicBracketMode cfg "compile lit-aware infer sort-zero kernel"
  match Bracket.Lam.compileClosedClassic? localInferIsSomeSortZeroFullSkyWithLitTypeIds with
  | some inferC => pure inferC
  | none => throw "failed to compile lit-aware infer sort-zero kernel to Comb"

private def compileIotaRulesComb (cfg : Cfg) (senv : SEnv) : Except String Comb := do
  let _ ← ensureClassicBracketMode cfg "compile staged iota rules"
  let encodableSpecs :=
    senv.casesOnSpecs.filterMap fun spec =>
      if spec.majorIdx == spec.firstMinorIdx + spec.ctors.length then
        some <|
          WHNFIotaSKY.Enc.casesOnSpec
            spec.recursor
            spec.firstMinorIdx
            (spec.ctors.map fun ctor => (ctor.name, ctor.numParams + ctor.numFields))
      else
        none
  match WHNFIotaSKY.compileClosed? (WHNFIotaSKY.Enc.iotaRules encodableSpecs) with
  | some rulesC => pure rulesC
  | none => throw "failed to compile staged iota rules to Comb"

private def encodeFuelComb (cfg : Cfg) (what : String) (n : Nat) : Except String Comb := do
  let _ ← ensureClassicBracketMode cfg what
  match Bracket.Lam.compileClosedClassic? (Expr.Scott.encodeNat n) with
  | some v => pure v
  | none => throw s!"failed to encode {what}"

private def envComb (cfg : Cfg) (senv : SEnv) : Except String Comb := do
  let _ ← ensureClassicBracketMode cfg "compile staged environment"
  match Bracket.Lam.compileClosedClassic? (EnvironmentSKY.envEncode [] senv) with
  | some v => pure v
  | none => throw "failed to compile staged environment to closed SKY terms"

private def optExprIsSomeComb (cfg : Cfg) : Except String Comb := do
  let _ ← ensureClassicBracketMode cfg "compile optExprIsSome helper"
  match Bracket.Lam.compileClosedClassic? localOptExprIsSomeSky with
  | some v => pure v
  | none => throw "failed to compile optExprIsSome helper"

private def optExprIsSomeSortComb (cfg : Cfg) : Except String Comb := do
  let _ ← ensureClassicBracketMode cfg "compile optExprIsSomeSort helper"
  match Bracket.Lam.compileClosedClassic? localOptExprIsSomeSortSky with
  | some v => pure v
  | none => throw "failed to compile optExprIsSomeSort helper"

private def optExprIsSomeSortZeroComb (cfg : Cfg) : Except String Comb := do
  let _ ← ensureClassicBracketMode cfg "compile optExprIsSomeSortZero helper"
  match Bracket.Lam.compileClosedClassic? localOptExprIsSomeSortZeroSky with
  | some v => pure v
  | none => throw "failed to compile optExprIsSomeSortZero helper"

private def exprIsSortZeroComb (cfg : Cfg) : Except String Comb := do
  let _ ← ensureClassicBracketMode cfg "compile exprIsSortZero helper"
  match Bracket.Lam.compileClosedClassic? localExprIsSortZeroSky with
  | some v => pure v
  | none => throw "failed to compile exprIsSortZero helper"

private def boolAndComb (cfg : Cfg) : Except String Comb := do
  let _ ← ensureClassicBracketMode cfg "compile boolean conjunction helper"
  match DefEqSKY.compileClosed? DefEqSKY.boolAnd with
  | some v => pure v
  | none => throw "failed to compile boolean conjunction helper"

private def applyLitAwareInferKernel
    (inferKernelC envC rulesC natIdC stringIdC fuelInferC ctxC exprC : Comb) : Comb :=
  Comb.app
    (Comb.app
      (Comb.app
        (Comb.app
          (Comb.app
            (Comb.app
              (Comb.app inferKernelC envC)
              rulesC)
            natIdC)
          stringIdC)
        fuelInferC)
      ctxC)
    exprC

private def applyLitAwareCheckKernel
    (checkKernelC envC rulesC natIdC stringIdC fuelInferC ctxC valueC typeC : Comb) : Comb :=
  Comb.app
    (Comb.app
      (Comb.app
        (Comb.app
          (Comb.app
            (Comb.app
              (Comb.app
                (Comb.app checkKernelC envC)
                rulesC)
              natIdC)
            stringIdC)
          fuelInferC)
        ctxC)
      valueC)
    typeC

private def compileExportBundleWithMode? (cfg : Cfg) : Option FullKernelSKY.FullCompiled := do
  match cfg.bracketMode with
  | .classic => pure ()
  | .bulk => failure
  let dummy := Comb.K
  match singleWhnfOp? cfg, singleDefEqOp? cfg with
  | some _, _ =>
      let whnf <- FullKernelSKY.whnfFullComb?
      let emptyRules <- FullKernelSKY.emptyRulesComb?
      pure
        { whnf := whnf
          isDefEq := dummy
          infer := dummy
          check := dummy
          emptyCtx := dummy
          emptyEnv := dummy
          emptyRules := emptyRules }
  | none, true =>
      let whnf <- FullKernelSKY.whnfFullComb?
      let isDefEq <- FullKernelSKY.isDefEqFullComb?
      let emptyRules <- FullKernelSKY.emptyRulesComb?
      pure
        { whnf := whnf
          isDefEq := isDefEq
          infer := dummy
          check := dummy
          emptyCtx := dummy
          emptyEnv := dummy
          emptyRules := emptyRules }
  | none, false =>
      FullKernelSKY.compileFull?

private def depOpTypesJson (deps : Array OpKind) : Json :=
  Json.arr <| deps.map (fun kind => Json.str (toString kind))

private def skippedOperationJson
    (kind : OpKind)
    (declName : Name)
    (inputExpr outputExpr : Lean.Expr)
    (nativeMs : Nat)
    (reason : String)
    (dependencyOpTypes : Array OpKind := #[])
    (comparisonMode? : Option String := none) : Json :=
  Json.mkObj <|
    [ ("decl_name", Json.str declName.toString)
    , ("op_type", Json.str (toString kind))
    , ("join_enabled", Json.bool true)
    ] ++
    (match comparisonMode? with
    | some mode => [("comparison_mode", Json.str mode)]
    | none => []) ++
    [ ("dependency_op_types", depOpTypesJson dependencyOpTypes)
    , ("eligible", Json.bool false)
    , ("skip_reason", Json.str reason)
    , ("native_elapsed_ms", toJson nativeMs)
    , ("input_expr_repr", Json.str (reprStr inputExpr))
    , ("native_output_repr", Json.str (reprStr outputExpr))
    ]

private def operationJsonTimed
    (cfg : Cfg)
    (kind : OpKind)
    (declName : Name)
    (inputExpr outputExpr : Lean.Expr)
    (nativeMs : Nat)
    (decodeTerm expectedTerm : Comb) : IO (Json × Nat) := do
  let (exportResult, machineExportMs) ← withElapsedMs <| pure (runMachineExport cfg decodeTerm expectedTerm)
  let payload :=
    match exportResult with
    | .error err =>
        Json.mkObj
          [ ("decl_name", Json.str declName.toString)
          , ("op_type", Json.str (toString kind))
          , ("join_enabled", Json.bool true)
          , ("dependency_op_types", depOpTypesJson #[])
          , ("eligible", Json.bool false)
          , ("skip_reason", Json.str err)
          , ("native_elapsed_ms", toJson nativeMs)
          , ("machine_export_elapsed_ms", toJson machineExportMs)
          , ("input_expr_repr", Json.str (reprStr inputExpr))
          , ("native_output_repr", Json.str (reprStr outputExpr))
          ]
    | .ok (machineJson, finalJson, observedFinalJson, traceJson, stepsTaken, maxStack, maxNodesUsed, matchesExpected) =>
        let nodeCount :=
          match machineJson.getObjValAs? Nat "nodesUsed" with
          | .ok n => n
          | .error _ => 0
        let eligible := if cfg.machineExportOnly then true else matchesExpected
        Json.mkObj
          [ ("decl_name", Json.str declName.toString)
          , ("op_type", Json.str (toString kind))
          , ("join_enabled", Json.bool true)
          , ("dependency_op_types", depOpTypesJson #[])
          , ("eligible", Json.bool eligible)
          , ("semantic_check_skipped", Json.bool cfg.machineExportOnly)
          , ("skip_reason", if cfg.machineExportOnly || eligible then Json.null else Json.str "staged CPU check did not normalize to expected boolean")
          , ("native_elapsed_ms", toJson nativeMs)
          , ("machine_export_elapsed_ms", toJson machineExportMs)
          , ("input_expr_repr", Json.str (reprStr inputExpr))
          , ("native_output_repr", Json.str (reprStr outputExpr))
          , ("expected_tag_term", Json.str (reprStr expectedTerm))
          , ("matches_expected", Json.bool matchesExpected)
          , ("node_count", toJson nodeCount)
          , ("steps_taken", toJson stepsTaken)
          , ("max_stack", toJson maxStack)
          , ("max_nodes_used", toJson maxNodesUsed)
          , ("machine_json", machineJson)
          , ("final_json", finalJson)
          , ("observed_final_json", observedFinalJson)
          , ("trace_json", traceJson)
          ]
  pure (payload, machineExportMs)

private def directStateOperationJsonTimed
    (cfg : Cfg)
    (kind : OpKind)
    (declName : Name)
    (inputExpr outputExpr : Lean.Expr)
    (nativeMs : Nat)
    (decodeTerm expectedTerm : Comb)
    (dependencyOpTypes : Array OpKind := #[])
    (useObservational : Bool := true)
    (comparisonModeOverride : Option String := none) : IO (Json × Nat) := do
  let comparisonMode :=
    match comparisonModeOverride with
    | some mode => mode
    | none =>
        if useObservational then
          "recursive_whnf_spine"
        else
          "focused_term_match"
  let exportFn :=
    if useObservational then
      runMachineExportObservational cfg decodeTerm expectedTerm
    else
      runMachineExport cfg decodeTerm expectedTerm
  let (exportResult, machineExportMs) ← withElapsedMs <| pure exportFn
  let payload :=
    match exportResult with
    | .error err =>
        Json.mkObj
          [ ("decl_name", Json.str declName.toString)
          , ("op_type", Json.str (toString kind))
          , ("join_enabled", Json.bool true)
          , ("comparison_mode", Json.str comparisonMode)
          , ("dependency_op_types", depOpTypesJson dependencyOpTypes)
          , ("eligible", Json.bool false)
          , ("skip_reason", Json.str err)
          , ("native_elapsed_ms", toJson nativeMs)
          , ("machine_export_elapsed_ms", toJson machineExportMs)
          , ("input_expr_repr", Json.str (reprStr inputExpr))
          , ("native_output_repr", Json.str (reprStr outputExpr))
          ]
    | .ok (machineJson, finalJson, observedFinalJson, traceJson, stepsTaken, maxStack, maxNodesUsed, matchesExpected) =>
        let nodeCount :=
          match machineJson.getObjValAs? Nat "nodesUsed" with
          | .ok n => n
          | .error _ => 0
        let eligible := if cfg.machineExportOnly then true else matchesExpected
        Json.mkObj
          [ ("decl_name", Json.str declName.toString)
          , ("op_type", Json.str (toString kind))
          , ("join_enabled", Json.bool true)
          , ("comparison_mode", Json.str comparisonMode)
          , ("dependency_op_types", depOpTypesJson dependencyOpTypes)
          , ("eligible", Json.bool eligible)
          , ("semantic_check_skipped", Json.bool cfg.machineExportOnly)
          , ("skip_reason", if cfg.machineExportOnly || eligible then Json.null else Json.str "staged CPU check did not normalize to the expected output state")
          , ("native_elapsed_ms", toJson nativeMs)
          , ("machine_export_elapsed_ms", toJson machineExportMs)
          , ("input_expr_repr", Json.str (reprStr inputExpr))
          , ("native_output_repr", Json.str (reprStr outputExpr))
          , ("matches_expected", Json.bool matchesExpected)
          , ("node_count", toJson nodeCount)
          , ("steps_taken", toJson stepsTaken)
          , ("max_stack", toJson maxStack)
          , ("max_nodes_used", toJson maxNodesUsed)
          , ("machine_json", machineJson)
          , ("final_json", finalJson)
          , ("observed_final_json", observedFinalJson)
          , ("trace_json", traceJson)
          ]
  pure (payload, machineExportMs)

private def operationJson
    (cfg : Cfg)
    (kind : OpKind)
    (declName : Name)
    (inputExpr outputExpr : Lean.Expr)
    (nativeMs : Nat)
    (decodeTerm expectedTerm : Comb)
    (dependencyOpTypes : Array OpKind := #[])
    (joinEnabled : Bool := true) : Json :=
  match runMachineExport cfg decodeTerm expectedTerm with
  | .error err =>
      Json.mkObj
        [ ("decl_name", Json.str declName.toString)
        , ("op_type", Json.str (toString kind))
        , ("join_enabled", Json.bool joinEnabled)
        , ("dependency_op_types", depOpTypesJson dependencyOpTypes)
        , ("eligible", Json.bool false)
        , ("skip_reason", Json.str err)
        , ("native_elapsed_ms", toJson nativeMs)
        , ("input_expr_repr", Json.str (reprStr inputExpr))
        , ("native_output_repr", Json.str (reprStr outputExpr))
        ]
  | .ok (machineJson, finalJson, observedFinalJson, traceJson, stepsTaken, maxStack, maxNodesUsed, matchesExpected) =>
      let nodeCount :=
        match machineJson.getObjValAs? Nat "nodesUsed" with
        | .ok n => n
        | .error _ => 0
      let eligible := if cfg.machineExportOnly then true else matchesExpected
      Json.mkObj
        [ ("decl_name", Json.str declName.toString)
        , ("op_type", Json.str (toString kind))
        , ("join_enabled", Json.bool joinEnabled)
        , ("dependency_op_types", depOpTypesJson dependencyOpTypes)
        , ("eligible", Json.bool eligible)
        , ("semantic_check_skipped", Json.bool cfg.machineExportOnly)
        , ("skip_reason", if cfg.machineExportOnly || eligible then Json.null else Json.str "staged CPU check did not normalize to expected boolean")
        , ("native_elapsed_ms", toJson nativeMs)
        , ("input_expr_repr", Json.str (reprStr inputExpr))
        , ("native_output_repr", Json.str (reprStr outputExpr))
        , ("expected_tag_term", Json.str (reprStr expectedTerm))
        , ("matches_expected", Json.bool matchesExpected)
        , ("node_count", toJson nodeCount)
        , ("steps_taken", toJson stepsTaken)
        , ("max_stack", toJson maxStack)
        , ("max_nodes_used", toJson maxNodesUsed)
        , ("machine_json", machineJson)
        , ("final_json", finalJson)
        , ("observed_final_json", observedFinalJson)
        , ("trace_json", traceJson)
        ]

private def boolOperationJson
    (cfg : Cfg)
    (kind : OpKind)
    (declName : Name)
    (inputExpr : Lean.Expr)
    (nativeBool : Bool)
    (nativeMs : Nat)
    (decodeTerm : Comb)
    (dependencyOpTypes : Array OpKind := #[])
    (joinEnabled : Bool := true)
    (nativeOutputExpr? : Option Lean.Expr := none) : Json :=
  let decodedBoolTerm := Comb.app (Comb.app decodeTerm Comb.K) Comb.S
  let expectedBoolTerm := if nativeBool then Comb.K else Comb.S
  match runMachineExport cfg decodedBoolTerm expectedBoolTerm with
  | .error err =>
      Json.mkObj <|
        [ ("decl_name", Json.str declName.toString)
        , ("op_type", Json.str (toString kind))
        , ("join_enabled", Json.bool joinEnabled)
        , ("dependency_op_types", depOpTypesJson dependencyOpTypes)
        , ("eligible", Json.bool false)
        , ("skip_reason", Json.str err)
        , ("native_elapsed_ms", toJson nativeMs)
        , ("input_expr_repr", Json.str (reprStr inputExpr))
        , ("native_output_bool", Json.bool nativeBool)
        ] ++
        match nativeOutputExpr? with
        | some outputExpr => [("native_output_repr", Json.str (reprStr outputExpr))]
        | none => []
  | .ok (machineJson, finalJson, observedFinalJson, traceJson, stepsTaken, maxStack, maxNodesUsed, matchesExpected) =>
      let nodeCount :=
        match machineJson.getObjValAs? Nat "nodesUsed" with
        | .ok n => n
        | .error _ => 0
      let eligible := if cfg.machineExportOnly then true else matchesExpected
      Json.mkObj <|
        [ ("decl_name", Json.str declName.toString)
        , ("op_type", Json.str (toString kind))
        , ("join_enabled", Json.bool joinEnabled)
        , ("dependency_op_types", depOpTypesJson dependencyOpTypes)
        , ("eligible", Json.bool eligible)
        , ("semantic_check_skipped", Json.bool cfg.machineExportOnly)
        , ("skip_reason", if cfg.machineExportOnly || eligible then Json.null else Json.str "staged CPU check did not normalize to expected boolean")
        , ("native_elapsed_ms", toJson nativeMs)
        , ("input_expr_repr", Json.str (reprStr inputExpr))
        , ("native_output_bool", Json.bool nativeBool)
        , ("expected_tag_term", Json.str (reprStr (boolTagTerm nativeBool)))
        , ("matches_expected", Json.bool matchesExpected)
        , ("node_count", toJson nodeCount)
        , ("steps_taken", toJson stepsTaken)
        , ("max_stack", toJson maxStack)
        , ("max_nodes_used", toJson maxNodesUsed)
        , ("machine_json", machineJson)
        , ("final_json", finalJson)
        , ("observed_final_json", observedFinalJson)
        , ("trace_json", traceJson)
        ] ++
        match nativeOutputExpr? with
        | some outputExpr => [("native_output_repr", Json.str (reprStr outputExpr))]
        | none => []

private def boolOperationJsonTimed
    (cfg : Cfg)
    (kind : OpKind)
    (declName : Name)
    (inputExpr : Lean.Expr)
    (nativeBool : Bool)
    (nativeMs : Nat)
    (decodeTerm : Comb)
    (dependencyOpTypes : Array OpKind := #[])
    (joinEnabled : Bool := true)
    (nativeOutputExpr? : Option Lean.Expr := none) : IO (Json × Nat) := do
  let hostDecodedBool : Option Bool := none
  let decodedBoolTerm := Comb.app (Comb.app decodeTerm Comb.K) Comb.S
  let expectedBoolTerm := if nativeBool then Comb.K else Comb.S
  let comparisonMode := "recursive_whnf_spine"
  let (exportResult, machineExportMs) ←
    withElapsedMs <| pure (runMachineExportObservational cfg decodedBoolTerm expectedBoolTerm)
  let payload :=
    match exportResult with
    | .error err =>
        Json.mkObj <|
          [ ("decl_name", Json.str declName.toString)
          , ("op_type", Json.str (toString kind))
          , ("join_enabled", Json.bool joinEnabled)
          , ("comparison_mode", Json.str comparisonMode)
          , ("host_decoded_bool", Option.elim hostDecodedBool Json.null Json.bool)
          , ("dependency_op_types", depOpTypesJson dependencyOpTypes)
          , ("eligible", Json.bool false)
          , ("skip_reason", Json.str err)
          , ("native_elapsed_ms", toJson nativeMs)
          , ("machine_export_elapsed_ms", toJson machineExportMs)
          , ("input_expr_repr", Json.str (reprStr inputExpr))
          , ("native_output_bool", Json.bool nativeBool)
          ] ++
          match nativeOutputExpr? with
          | some outputExpr => [("native_output_repr", Json.str (reprStr outputExpr))]
          | none => []
      | .ok (machineJson, finalJson, observedFinalJson, traceJson, stepsTaken, maxStack, maxNodesUsed, matchesExpected) =>
        let nodeCount :=
          match machineJson.getObjValAs? Nat "nodesUsed" with
          | .ok n => n
          | .error _ => 0
        let eligible := if cfg.machineExportOnly then true else matchesExpected
        Json.mkObj <|
          [ ("decl_name", Json.str declName.toString)
          , ("op_type", Json.str (toString kind))
          , ("join_enabled", Json.bool joinEnabled)
          , ("comparison_mode", Json.str comparisonMode)
          , ("host_decoded_bool", Option.elim hostDecodedBool Json.null Json.bool)
          , ("dependency_op_types", depOpTypesJson dependencyOpTypes)
          , ("eligible", Json.bool eligible)
          , ("semantic_check_skipped", Json.bool cfg.machineExportOnly)
          , ("skip_reason", if cfg.machineExportOnly || eligible then Json.null else Json.str "staged CPU check did not normalize to expected boolean")
          , ("native_elapsed_ms", toJson nativeMs)
          , ("machine_export_elapsed_ms", toJson machineExportMs)
          , ("input_expr_repr", Json.str (reprStr inputExpr))
          , ("native_output_bool", Json.bool nativeBool)
          , ("expected_tag_term", Json.str (reprStr (boolTagTerm nativeBool)))
          , ("matches_expected", Json.bool matchesExpected)
          , ("node_count", toJson nodeCount)
          , ("steps_taken", toJson stepsTaken)
          , ("max_stack", toJson maxStack)
          , ("max_nodes_used", toJson maxNodesUsed)
          , ("machine_json", machineJson)
          , ("final_json", finalJson)
          , ("observed_final_json", observedFinalJson)
          , ("trace_json", traceJson)
          ] ++
          match nativeOutputExpr? with
          | some outputExpr => [("native_output_repr", Json.str (reprStr outputExpr))]
          | none => []
  pure (payload, machineExportMs)

private def exportSingleDirectOpDecl
    (env : Lean.Environment)
    (compiled : FullKernelSKY.FullCompiled)
    (cfg : Cfg)
    (moduleName : Name)
    (declName : Name)
    (kind : String)
    (opKind : OpKind)
    (declType declValue : Lean.Expr) : IO Json := do
  if opKind != .inferTypeSort then
    pure <| skipDeclJson moduleName declName kind s!"unsupported single direct op {opKind}"
  else
  appendPhaseTrace cfg declName "single_direct_op_start"
    [("selected_op", Json.str (toString opKind))]
  let (loweredTypeResult, lowerTypeMs) ← withElapsedMs <| lowerProjExpr env declType
  let (loweredValueResult, lowerValueMs) ← withElapsedMs <| lowerProjExpr env declValue
  match loweredTypeResult, loweredValueResult with
  | .error err, _ => pure <| skipDeclJson moduleName declName kind s!"native reference failed: {err}"
  | _, .error err => pure <| skipDeclJson moduleName declName kind s!"native reference failed: {err}"
  | .ok loweredType, .ok loweredValue => do
      let inferTypeSortResult ← nativeInfer env declType
      match inferTypeSortResult with
      | .error err => pure <| skipDeclJson moduleName declName kind s!"native reference failed: {err}"
      | .ok (inferSort, inferTypeSortMs) => do
          let (loweredInferSortResult, lowerInferSortMs) ← withElapsedMs <| lowerProjExpr env inferSort
          match loweredInferSortResult with
          | .error err => pure <| skipDeclJson moduleName declName kind s!"native reference failed: {err}"
          | .ok loweredInferSort => do
              appendPhaseTrace cfg declName "native_reference_done"
                [ ("selected_op", Json.str (toString opKind))
                , ("lower_type_ms", toJson lowerTypeMs)
                , ("lower_value_ms", toJson lowerValueMs)
                , ("infer_type_sort_ms", toJson inferTypeSortMs)
                ]
              let seedRefs :=
                (collectConstRefs loweredType).toList ++
                (collectConstRefs loweredInferSort).toList
              let (closureResult, closureMs) ← withElapsedMs <| closureNames env declName seedRefs cfg.maxEnvConsts
              match closureResult with
              | .error err =>
                  appendPhaseTrace cfg declName "closure_error"
                    [("closure_ms", toJson closureMs), ("error", Json.str err)]
                  pure <| skipDeclJson moduleName declName kind err
              | .ok closure => do
                  appendPhaseTrace cfg declName "closure_done"
                    [("closure_ms", toJson closureMs), ("env_const_count", toJson closure.size)]
                  let (stagedResult, stageMs) ←
                    withElapsedMs <| buildStagedEnvSingleWithInsts env declName closure loweredType
                  match stagedResult with
                  | .error err =>
                      appendPhaseTrace cfg declName "stage_error"
                        [("stage_ms", toJson stageMs), ("error", Json.str err)]
                      pure <| skipDeclJson moduleName declName kind s!"staged conversion failed: {err}"
                  | .ok (senv, targetType, st0) => do
                      appendPhaseTrace cfg declName "stage_done"
                        [ ("stage_ms", toJson stageMs)
                        , ("erased_universe_payload", Json.bool st0.erasedUniversePayload)
                        , ("erased_expr_metas", Json.bool st0.erasedExprMetas)
                        ]
                      let compileStart ← IO.monoMsNow
                      let result : Except String
                          (Comb × Comb × Comb × Comb × Comb × Comb × Comb × Comb × Comb × Comb) := do
                        let envC ← envComb cfg senv
                        let fuelInferC ← encodeFuelComb cfg "infer fuel" cfg.fuelInfer
                        let typeC ← compileExprComb cfg "declared type" targetType
                        let rulesC ← compileIotaRulesComb cfg senv
                        let natIdC ← encodeFuelComb cfg "staged Nat const id" (← stagedConstId st0 natConstName)
                        let stringIdC ← encodeFuelComb cfg "staged String const id" (← stagedConstId st0 stringConstName)
                        let (inferKernelC, _) ← compileLitAwareInferCheck cfg
                        let inferSortZeroKernelC ← compileLitAwareInferSortZeroKernel cfg
                        let (inferSortExpr, _) ←
                          stageExprWithState st0 (eraseConstLevelInsts loweredInferSort)
                        let inferSortC ← compileExprComb cfg "native infer(type) payload" inferSortExpr
                        let inferSortSomeC ← compileOptSomeExprComb cfg "native infer(type)" inferSortExpr
                        pure
                          ( envC
                          , fuelInferC
                          , typeC
                          , rulesC
                          , natIdC
                          , stringIdC
                          , inferKernelC
                          , inferSortZeroKernelC
                          , inferSortC
                          , inferSortSomeC
                          )
                      match result with
                      | .error err =>
                          let endMs ← IO.monoMsNow
                          let compileMs := endMs - compileStart
                          appendPhaseTrace cfg declName "compile_error"
                            [("compile_ms", toJson compileMs), ("error", Json.str err)]
                          pure <| skipDeclJson moduleName declName kind err
                      | .ok (envC, fuelInferC, typeC, rulesC, natIdC, stringIdC, inferKernelC, inferSortZeroKernelC, inferSortC, inferSortSomeC) => do
                          let compileEndMs ← IO.monoMsNow
                          let compileMs := compileEndMs - compileStart
                          appendPhaseTrace cfg declName "compile_done"
                            [("compile_ms", toJson compileMs)]
                          appendPhaseTrace cfg declName "machine_export_start"
                            [("selected_op", Json.str (toString opKind))]
                          let (opJson, machineExportMs) ← do
                            let inferTypeSortOutOpt :=
                              applyLitAwareInferKernel inferKernelC envC rulesC natIdC stringIdC fuelInferC compiled.emptyCtx typeC
                            if isSortZeroExpr loweredInferSort then
                              boolOperationJsonTimed
                                cfg
                                .inferTypeSort
                                declName
                                loweredType
                                true
                                inferTypeSortMs
                                (applyLitAwareInferKernel inferSortZeroKernelC envC rulesC natIdC stringIdC fuelInferC compiled.emptyCtx typeC)
                                #[]
                                true
                                (some loweredInferSort)
                            else
                              directStateOperationJsonTimed
                                cfg
                                .inferTypeSort
                                declName
                                loweredType
                                loweredInferSort
                                inferTypeSortMs
                                inferTypeSortOutOpt
                                inferSortSomeC
                                #[]
                                true
                                (some "option_recursive_whnf_spine")
                          let eligible :=
                            match opJson.getObjValAs? Bool "eligible" with
                            | .ok b => b
                            | .error _ => false
                          let skipReason :=
                            match opJson.getObjValAs? String "skip_reason" with
                            | .ok s => Json.str s
                            | .error _ => Json.null
                          appendPhaseTrace cfg declName "machine_export_done"
                            [ ("machine_export_ms", toJson machineExportMs)
                            , ("eligible", Json.bool eligible)
                            , ("skip_reason", skipReason)
                            ]
                          let operations := #[opJson]
                          let eligibleOps :=
                            operations.foldl (init := 0) fun acc j =>
                              match j.getObjValAs? Bool "eligible" with
                              | .ok true => acc + 1
                              | _ => acc
                          let timing : ProducerTiming :=
                            { lowerDeclTypeMs := lowerTypeMs
                              lowerInputMs := lowerTypeMs
                              nativeMs := inferTypeSortMs
                              lowerOutputMs := lowerInferSortMs
                              closureMs := closureMs
                              stageMs := stageMs
                              compileMs := compileMs
                              machineExportMs := machineExportMs }
                          pure <| Json.mkObj <| declJsonBase moduleName declName kind ++
                            [ ("eligible", Json.bool (eligibleOps = operations.size))
                            , ("skip_reason", if eligibleOps = operations.size then Json.null else Json.str "one or more operations did not normalize to the expected output state")
                            , ("producer_path", Json.str "single_direct_op")
                            , ("selected_op", Json.str (toString opKind))
                            , ("semantic_mode", Json.str "direct_targeted_check")
                            , ("producer_timing_ms", producerTimingJson timing)
                            , ("universe_policy", Json.str "Lean.Level.param/mvar payloads erased to Unit")
                            , ("expr_meta_policy", Json.str "Lean.Expr.mvar payloads erased to Unit")
                            , ("iota_policy", Json.str "staged iota rules")
                            , ("erased_universe_payload", Json.bool st0.erasedUniversePayload)
                            , ("erased_expr_metas", Json.bool st0.erasedExprMetas)
                            , ("env_const_count", toJson closure.size)
                            , ("native_total_ms", toJson inferTypeSortMs)
                            , ("eligible_operations", toJson eligibleOps)
                            , ("machine_infer_payload_some", Json.null)
                            , ("machine_infer_tag", Json.null)
                            , ("operations", Json.arr operations)
                            ]

private def exportSingleWhnfDecl
    (env : Lean.Environment)
    (compiled : FullKernelSKY.FullCompiled)
    (cfg : Cfg)
    (moduleName : Name)
    (declName : Name)
    (kind : String)
    (whnfKind : OpKind)
    (nativeResult : Except String WhnfLeafDirect) : IO Json := do
  match nativeResult with
  | .error err =>
      pure <| skipDeclJson moduleName declName kind s!"native reference failed: {err}"
  | .ok whnf => do
      let seedRefs :=
        (collectConstRefs whnf.loweredInput).toList ++
        (collectConstRefs whnf.loweredOutput).toList
      let (closureResult, closureMs) ← withElapsedMs <| closureNames env declName seedRefs cfg.maxEnvConsts
      match closureResult with
      | .error err => pure <| skipDeclJson moduleName declName kind err
      | .ok closure => do
          let (stagedResult, stageMs) ←
            withElapsedMs <| buildStagedEnvSingle env declName closure whnf.loweredDeclType whnf.loweredInput
          match stagedResult with
          | .error err =>
              pure <| skipDeclJson moduleName declName kind s!"staged conversion failed: {err}"
          | .ok (senv, targetExpr, st0) => do
              let compileStart ← IO.monoMsNow
              let result :=
                match
                  envComb cfg senv,
                  compileIotaRulesComb cfg senv,
                  encodeFuelComb cfg "whnf fuel" cfg.fuelWhnf,
                  compileExprComb cfg "selected whnf input" targetExpr,
                  stageExprWithState st0 whnf.loweredOutput
                with
                | .ok envC, .ok rulesC, .ok fuelWhnfC, .ok inputC, .ok (outputExpr, _) =>
                    match compileExprComb cfg "selected native whnf output" outputExpr with
                    | .ok outputC =>
                        if inputC = outputC then
                          Except.ok (inputC, outputC, envC, true)
                        else
                          let whnfOut :=
                            Comb.app
                              (Comb.app
                                (Comb.app
                                  (Comb.app compiled.whnf envC)
                                  rulesC)
                                fuelWhnfC)
                              inputC
                          Except.ok (whnfOut, outputC, envC, false)
                    | .error err => .error err
                | _, .error err, _, _, _ => .error err
                | _, _, .error err, _, _ => .error err
                | _, _, _, _, .error err => .error err
                | _, _, _, _, _ => .error "failed to compile staged whnf verifier inputs to closed SKY terms"
              let compileMs ← do
                let endMs ← IO.monoMsNow
                pure (endMs - compileStart)
              match result with
              | .error err =>
                  pure <| skipDeclJson moduleName declName kind err
              | .ok (whnfOut, outputC, _, usedFixedPoint) => do
                  let (opJson, machineExportMs) ←
                    directStateOperationJsonTimed cfg whnfKind declName whnf.loweredInput whnf.loweredOutput whnf.nativeMs whnfOut outputC
                  let operations := #[opJson]
                  let eligibleOps :=
                    operations.foldl (init := 0) fun acc j =>
                      match j.getObjValAs? Bool "eligible" with
                      | .ok true => acc + 1
                      | _ => acc
                  let timing : ProducerTiming :=
                    { lowerDeclTypeMs := whnf.lowerDeclTypeMs
                      lowerInputMs := whnf.lowerInputMs
                      nativeMs := whnf.nativeMs
                      lowerOutputMs := whnf.lowerOutputMs
                      closureMs := closureMs
                      stageMs := stageMs
                      compileMs := compileMs
                      machineExportMs := machineExportMs }
                  pure <| Json.mkObj <| declJsonBase moduleName declName kind ++
                    [ ("eligible", Json.bool (eligibleOps = operations.size))
                    , ("skip_reason", if eligibleOps = operations.size then Json.null else Json.str "one or more operations did not normalize to the expected output state")
                    , ("producer_path", Json.str "single_whnf_op")
                    , ("selected_op", Json.str (toString whnfKind))
                    , ("semantic_mode", Json.str (if usedFixedPoint then "native_whnf_fixedpoint_input_state" else "direct_output_state_match"))
                    , ("producer_timing_ms", producerTimingJson timing)
                    , ("universe_policy", Json.str "Lean.Level.param/mvar payloads erased to Unit")
                    , ("expr_meta_policy", Json.str "Lean.Expr.mvar payloads erased to Unit")
                    , ("iota_policy", Json.str "empty iota rules")
                    , ("erased_universe_payload", Json.bool st0.erasedUniversePayload)
                    , ("erased_expr_metas", Json.bool st0.erasedExprMetas)
                    , ("env_const_count", toJson closure.size)
                    , ("native_total_ms", toJson whnf.nativeMs)
                    , ("eligible_operations", toJson eligibleOps)
                    , ("operations", Json.arr operations)
                    ]

private def exportSingleDefEqEqPayloadWhnfDecl
    (env : Lean.Environment)
    (compiled : FullKernelSKY.FullCompiled)
    (cfg : Cfg)
    (moduleName : Name)
    (declName : Name)
    (kind : String)
    (leaf : DefEqLeafDirect)
    (payloadType inferRhs expectedRhs : Lean.Expr) : IO Json := do
  appendPhaseTrace cfg declName "single_defeq_eq_payload_whnf_start"
  let nativeResult ← buildWhnfLeafDirect env .whnfValue payloadType inferRhs
  match nativeResult with
  | .error err =>
      appendPhaseTrace cfg declName "single_defeq_eq_payload_whnf_native_error"
        [("error", Json.str err)]
      pure <| skipDeclJson moduleName declName kind s!"eq-payload rhs whnf reference failed: {err}"
  | .ok whnf => do
      appendPhaseTrace cfg declName "single_defeq_eq_payload_whnf_native_done"
        [ ("native_ms", toJson whnf.nativeMs)
        , ("lower_decl_type_ms", toJson whnf.lowerDeclTypeMs)
        , ("lower_input_ms", toJson whnf.lowerInputMs)
        , ("lower_output_ms", toJson whnf.lowerOutputMs)
        ]
      let expectedResult ← buildWhnfLeafDirect env .whnfValue payloadType expectedRhs
      match expectedResult with
      | .error err =>
          appendPhaseTrace cfg declName "single_defeq_eq_payload_whnf_expected_error"
            [("error", Json.str err)]
          pure <| skipDeclJson moduleName declName kind s!"eq-payload expected rhs whnf reference failed: {err}"
      | .ok expectedWhnf =>
          if expectedWhnf.loweredOutput != whnf.loweredOutput then
            appendPhaseTrace cfg declName "single_defeq_eq_payload_whnf_mismatch"
            pure <| skipDeclJson moduleName declName kind "eq-payload rhs witness did not normalize to declared rhs"
          else
            let seedRefs :=
              (collectConstRefs whnf.loweredInput).toList ++
              (collectConstRefs expectedWhnf.loweredOutput).toList
            let (closureResult, closureMs) ← withElapsedMs <| closureNames env declName seedRefs cfg.maxEnvConsts
            match closureResult with
            | .error err =>
                appendPhaseTrace cfg declName "single_defeq_eq_payload_whnf_closure_error"
                  [("closure_ms", toJson closureMs), ("error", Json.str err)]
                pure <| skipDeclJson moduleName declName kind err
            | .ok closure => do
                appendPhaseTrace cfg declName "single_defeq_eq_payload_whnf_closure_done"
                  [("closure_ms", toJson closureMs), ("env_const_count", toJson closure.size)]
                let (stagedResult, stageMs) ←
                  withElapsedMs <| buildStagedEnvSingle env declName closure whnf.loweredDeclType whnf.loweredInput
                match stagedResult with
                | .error err =>
                    appendPhaseTrace cfg declName "single_defeq_eq_payload_whnf_stage_error"
                      [("stage_ms", toJson stageMs), ("error", Json.str err)]
                    pure <| skipDeclJson moduleName declName kind s!"staged conversion failed: {err}"
                | .ok (senv, targetExpr, st0) => do
                    appendPhaseTrace cfg declName "single_defeq_eq_payload_whnf_stage_done"
                      [ ("stage_ms", toJson stageMs)
                      , ("erased_universe_payload", Json.bool st0.erasedUniversePayload)
                      , ("erased_expr_metas", Json.bool st0.erasedExprMetas)
                      ]
                    let compileStart ← IO.monoMsNow
                    let result :=
                      match
                        envComb cfg senv,
                        compileIotaRulesComb cfg senv,
                        encodeFuelComb cfg "whnf fuel" cfg.fuelWhnf,
                        compileExprComb cfg "selected eq-payload rhs" targetExpr,
                        stageExprWithState st0 expectedWhnf.loweredOutput
                      with
                      | .ok envC, .ok rulesC, .ok fuelWhnfC, .ok inputC, .ok (expectedOutputExpr, _) =>
                          match compileExprComb cfg "selected eq-payload expected rhs" expectedOutputExpr with
                          | .ok outputC =>
                              let whnfOut :=
                                Comb.app
                                  (Comb.app
                                    (Comb.app
                                      (Comb.app compiled.whnf envC)
                                      rulesC)
                                    fuelWhnfC)
                                  inputC
                              Except.ok (whnfOut, outputC)
                          | .error err => .error err
                      | _, .error err, _, _, _ => .error err
                      | _, _, .error err, _, _ => .error err
                      | _, _, _, _, .error err => .error err
                      | _, _, _, _, _ => .error "failed to compile eq-payload rhs witness to closed SKY terms"
                    let compileMs ← do
                      let endMs ← IO.monoMsNow
                      pure (endMs - compileStart)
                    match result with
                    | .error err =>
                        appendPhaseTrace cfg declName "single_defeq_eq_payload_whnf_compile_error"
                          [("compile_ms", toJson compileMs), ("error", Json.str err)]
                        pure <| skipDeclJson moduleName declName kind err
                    | .ok (whnfOut, outputC) => do
                        appendPhaseTrace cfg declName "single_defeq_eq_payload_whnf_compile_done"
                          [("compile_ms", toJson compileMs)]
                        appendPhaseTrace cfg declName "single_defeq_eq_payload_whnf_machine_export_start"
                        let (opJson, machineExportMs) ←
                          directStateOperationJsonTimed cfg .defEqInferredDeclared declName inferRhs expectedRhs whnf.nativeMs whnfOut outputC
                        let operations := #[opJson]
                        let eligibleOps :=
                          operations.foldl (init := 0) fun acc j =>
                            match j.getObjValAs? Bool "eligible" with
                            | .ok true => acc + 1
                            | _ => acc
                        appendPhaseTrace cfg declName "single_defeq_eq_payload_whnf_machine_export_done"
                          [("machine_export_ms", toJson machineExportMs), ("eligible_operations", toJson eligibleOps)]
                        let timing : ProducerTiming :=
                          { lowerDeclTypeMs := leaf.lowerDeclTypeMs
                            lowerInputMs := leaf.lowerInferTypeMs
                            nativeMs := leaf.inferMs + leaf.whnfDeclTypeMs + leaf.whnfInferTypeMs + leaf.defeqMs + whnf.nativeMs
                            lowerOutputMs := whnf.lowerOutputMs
                            closureMs := closureMs
                            stageMs := stageMs
                            compileMs := compileMs
                            machineExportMs := machineExportMs }
                        pure <| Json.mkObj <| declJsonBase moduleName declName kind ++
                          [ ("eligible", Json.bool (eligibleOps = operations.size))
                          , ("skip_reason", if eligibleOps = operations.size then Json.null else Json.str "eq-payload rhs witness did not normalize to the declared rhs")
                          , ("producer_path", Json.str "single_defeq_eq_payload_rhs_whnf")
                          , ("selected_op", Json.str (toString OpKind.defEqInferredDeclared))
                          , ("semantic_mode", Json.str "eq_payload_rhs_whnf")
                          , ("producer_timing_ms", producerTimingJson timing)
                          , ("universe_policy", Json.str "Lean.Level.param/mvar payloads erased to Unit")
                          , ("expr_meta_policy", Json.str "Lean.Expr.mvar payloads erased to Unit")
                          , ("iota_policy", Json.str "empty iota rules")
                          , ("erased_universe_payload", Json.bool st0.erasedUniversePayload)
                          , ("erased_expr_metas", Json.bool st0.erasedExprMetas)
                          , ("env_const_count", toJson closure.size)
                          , ("native_total_ms", toJson (leaf.inferMs + leaf.whnfDeclTypeMs + leaf.whnfInferTypeMs + leaf.defeqMs + whnf.nativeMs))
                          , ("eligible_operations", toJson eligibleOps)
                          , ("operations", Json.arr operations)
                          ]

private def exportDecl
    (env : Lean.Environment)
    (compiled : FullKernelSKY.FullCompiled)
    (cfg : Cfg)
    (moduleName : Name)
    (declName : Name)
    (ci : ConstantInfo) : IO Json := do
  let kind := constKind ci
  if env.isProjectionFn declName then
    pure <| skipDeclJson moduleName declName kind "projection declarations are not lowered yet"
  else
    match singleWhnfOp? cfg with
    | some .whnfType => do
        let nativeResult ← buildWhnfLeafDirect env .whnfType ci.type ci.type
        exportSingleWhnfDecl env compiled cfg moduleName declName kind .whnfType nativeResult
    | some whnfKind => do
        if !isCheckableDecl ci then
          pure <| skipDeclJson moduleName declName kind s!"unsupported declaration kind {kind}"
        else
          match constantValueExpr? ci with
          | none => pure <| skipDeclJson moduleName declName kind "declaration has no executable value"
          | some declValue => do
              let nativeResult ← buildWhnfLeafDirect env whnfKind ci.type declValue
              exportSingleWhnfDecl env compiled cfg moduleName declName kind whnfKind nativeResult
    | none => do
        if !isCheckableDecl ci then
          pure <| skipDeclJson moduleName declName kind s!"unsupported declaration kind {kind}"
        else
          match constantValueExpr? ci with
          | none => pure <| skipDeclJson moduleName declName kind "declaration has no executable value"
          | some declValue => do
            if singleDefEqOp? cfg then
              appendPhaseTrace cfg declName "single_defeq_op_start"
              let nativeResult ← buildDefEqLeafDirect env ci.type declValue
              match nativeResult with
              | .error err =>
                  appendPhaseTrace cfg declName "native_reference_error"
                    [("error", Json.str err)]
                  pure <| skipDeclJson moduleName declName kind s!"native reference failed: {err}"
              | .ok defeqLeaf => do
                  let fallback : IO Json := do
                    appendPhaseTrace cfg declName "native_reference_done"
                      [ ("infer_ms", toJson defeqLeaf.inferMs)
                      , ("whnf_decl_type_ms", toJson defeqLeaf.whnfDeclTypeMs)
                      , ("whnf_infer_type_ms", toJson defeqLeaf.whnfInferTypeMs)
                      , ("defeq_ms", toJson defeqLeaf.defeqMs)
                      , ("lower_decl_type_ms", toJson defeqLeaf.lowerDeclTypeMs)
                      , ("lower_infer_type_ms", toJson defeqLeaf.lowerInferTypeMs)
                      , ("native_bool", Json.bool defeqLeaf.nativeBool)
                      , ("lowered_decl_type_repr", Json.str (reprStr defeqLeaf.loweredDeclType))
                      , ("lowered_infer_type_repr", Json.str (reprStr defeqLeaf.loweredInferType))
                      ]
                    let seedRefs :=
                      (collectConstRefs defeqLeaf.loweredDeclType).toList ++
                      (collectConstRefs defeqLeaf.loweredInferType).toList
                    let (closureResult, closureMs) ← withElapsedMs <| closureNames env declName seedRefs cfg.maxEnvConsts
                    match closureResult with
                    | .error err =>
                        appendPhaseTrace cfg declName "closure_error"
                          [("closure_ms", toJson closureMs), ("error", Json.str err)]
                        pure <| skipDeclJson moduleName declName kind err
                    | .ok closure => do
                        appendPhaseTrace cfg declName "closure_done"
                          [("closure_ms", toJson closureMs), ("env_const_count", toJson closure.size)]
                        let (stagedResult, stageMs) ←
                          withElapsedMs <| buildStagedEnvSingle env declName closure defeqLeaf.loweredDeclType defeqLeaf.loweredInferType
                        match stagedResult with
                        | .error err =>
                            appendPhaseTrace cfg declName "stage_error"
                              [("stage_ms", toJson stageMs), ("error", Json.str err)]
                            pure <| skipDeclJson moduleName declName kind s!"staged conversion failed: {err}"
                        | .ok (senv, targetInferType, st0) => do
                            appendPhaseTrace cfg declName "stage_done"
                              [ ("stage_ms", toJson stageMs)
                              , ("erased_universe_payload", Json.bool st0.erasedUniversePayload)
                              , ("erased_expr_metas", Json.bool st0.erasedExprMetas)
                              ]
                            let compileStart ← IO.monoMsNow
                            let result :=
                              match
                                envComb cfg senv,
                                compileIotaRulesComb cfg senv,
                                encodeFuelComb cfg "defeq fuel" cfg.fuelDefEq,
                                compileExprComb cfg "selected defeq inferred type" targetInferType,
                                stageExprWithState st0 defeqLeaf.loweredDeclType
                              with
                              | .ok envC, .ok rulesC, .ok fuelDefEqC, .ok inferTypeC, .ok (declTypeExpr, _) =>
                                  match compileExprComb cfg "selected declared type" declTypeExpr with
                                  | .ok declTypeC =>
                                      if defeqLeaf.nativeBool && inferTypeC = declTypeC then
                                        Except.ok (boolTagTerm true, true, defeqLeaf.nativeBool)
                                      else
                                        let defeqCheck :=
                                          Comb.app
                                            (Comb.app
                                            (Comb.app
                                              (Comb.app
                                                (Comb.app compiled.isDefEq envC)
                                                  rulesC)
                                                fuelDefEqC)
                                              inferTypeC)
                                            declTypeC
                                        Except.ok (defeqCheck, false, defeqLeaf.nativeBool)
                                  | .error err => .error err
                              | _, .error err, _, _, _ => .error err
                              | _, _, .error err, _, _ => .error err
                              | _, _, _, _, .error err => .error err
                              | _, _, _, _, _ => .error "failed to compile staged defeq verifier inputs to closed SKY terms"
                            let compileMs ← do
                              let endMs ← IO.monoMsNow
                              pure (endMs - compileStart)
                            match result with
                            | .error err =>
                                appendPhaseTrace cfg declName "compile_error"
                                  [("compile_ms", toJson compileMs), ("error", Json.str err)]
                                pure <| skipDeclJson moduleName declName kind err
                            | .ok (defeqCheck, usedFixedPoint, nativeBool) => do
                                appendPhaseTrace cfg declName "compile_done"
                                  [ ("compile_ms", toJson compileMs)
                                  , ("used_fixedpoint", Json.bool usedFixedPoint)
                                  , ("native_bool", Json.bool nativeBool)
                                  ]
                                appendPhaseTrace cfg declName "machine_export_start"
                                let (opJson, machineExportMs) ←
                                  operationJsonTimed cfg .defEqInferredDeclared declName defeqLeaf.loweredInferType defeqLeaf.loweredDeclType defeqLeaf.defeqMs defeqCheck (boolTagTerm nativeBool)
                                let eligible :=
                                  match opJson.getObjValAs? Bool "eligible" with
                                  | .ok b => b
                                  | .error _ => false
                                let skipReason :=
                                  match opJson.getObjValAs? String "skip_reason" with
                                  | .ok s => Json.str s
                                  | .error _ => Json.null
                                appendPhaseTrace cfg declName "machine_export_done"
                                  [ ("machine_export_ms", toJson machineExportMs)
                                  , ("eligible", Json.bool eligible)
                                  , ("skip_reason", skipReason)
                                  ]
                                let operations := #[opJson]
                                let eligibleOps :=
                                  operations.foldl (init := 0) fun acc j =>
                                    match j.getObjValAs? Bool "eligible" with
                                    | .ok true => acc + 1
                                    | _ => acc
                                let timing : ProducerTiming :=
                                  { lowerDeclTypeMs := defeqLeaf.lowerDeclTypeMs
                                    lowerInputMs := defeqLeaf.lowerInferTypeMs
                                    nativeMs := defeqLeaf.inferMs + defeqLeaf.whnfDeclTypeMs + defeqLeaf.whnfInferTypeMs + defeqLeaf.defeqMs
                                    lowerOutputMs := 0
                                    closureMs := closureMs
                                    stageMs := stageMs
                                    compileMs := compileMs
                                    machineExportMs := machineExportMs }
                                pure <| Json.mkObj <| declJsonBase moduleName declName kind ++
                                  [ ("eligible", Json.bool (eligibleOps = operations.size))
                                  , ("skip_reason", if eligibleOps = operations.size then Json.null else Json.str "one or more operations did not normalize to the expected boolean")
                                  , ("producer_path", Json.str "single_defeq_op")
                                  , ("selected_op", Json.str (toString OpKind.defEqInferredDeclared))
                                  , ("semantic_mode", Json.str (if usedFixedPoint then "native_defeq_compiled_fixedpoint" else "direct_bool_tag_check"))
                                  , ("producer_timing_ms", producerTimingJson timing)
                                  , ("universe_policy", Json.str "Lean.Level.param/mvar payloads erased to Unit")
                                  , ("expr_meta_policy", Json.str "Lean.Expr.mvar payloads erased to Unit")
                                  , ("iota_policy", Json.str "empty iota rules")
                                  , ("erased_universe_payload", Json.bool st0.erasedUniversePayload)
                                  , ("erased_expr_metas", Json.bool st0.erasedExprMetas)
                                  , ("env_const_count", toJson closure.size)
                                  , ("native_total_ms", toJson (defeqLeaf.inferMs + defeqLeaf.whnfDeclTypeMs + defeqLeaf.whnfInferTypeMs + defeqLeaf.defeqMs))
                                  , ("eligible_operations", toJson eligibleOps)
                                  , ("operations", Json.arr operations)
                                  ]
                  match reflEqPayloadWitness? defeqLeaf with
                  | some (payloadType, inferRhs, expectedRhs) => do
                      let payloadJson ←
                        exportSingleDefEqEqPayloadWhnfDecl
                          env
                          compiled
                          cfg
                          moduleName
                          declName
                          kind
                          defeqLeaf
                          payloadType
                          inferRhs
                          expectedRhs
                      match payloadJson.getObjValAs? String "producer_path" with
                      | .ok "single_defeq_eq_payload_rhs_whnf" => pure payloadJson
                      | _ => fallback
                  | none => fallback
            else if let some directKind := singleDirectOp? cfg then
              exportSingleDirectOpDecl env compiled cfg moduleName declName kind directKind ci.type declValue
            else do
              let nativeResult ← buildNativeDirect env ci.type declValue
              match nativeResult with
              | .error err =>
                  pure <| skipDeclJson moduleName declName kind s!"native reference failed: {err}"
              | .ok native => do
                  let seedRefs :=
                    (collectConstRefs native.loweredType).toList ++
                    (collectConstRefs native.loweredValue).toList ++
                    (collectConstRefs native.loweredWhnfType).toList ++
                    (collectConstRefs native.loweredWhnfValue).toList ++
                    (collectConstRefs native.loweredInferType).toList
                  let closureResult ← closureNames env declName seedRefs cfg.maxEnvConsts
                  match closureResult with
                  | .error err => pure <| skipDeclJson moduleName declName kind err
                  | .ok closure => do
                      let stagedResult ← buildStagedEnv env declName closure native.loweredType native.loweredValue
                      match stagedResult with
                      | .error err =>
                          pure <| skipDeclJson moduleName declName kind s!"staged conversion failed: {err}"
                      | .ok (senv, targetType, targetValue, st0) =>
                          let compileResult : Except String
                              (Comb × Comb × Comb × Comb × Comb × Comb × Comb × Comb × Comb × Comb × Comb × Comb × Comb × Comb × Comb × Comb × Comb) := do
                            let envC ← envComb cfg senv
                            let fuelWhnfC ← encodeFuelComb cfg "whnf fuel" cfg.fuelWhnf
                            let fuelDefEqC ← encodeFuelComb cfg "defeq fuel" cfg.fuelDefEq
                            let fuelInferC ← encodeFuelComb cfg "infer fuel" cfg.fuelInfer
                            let typeC ← compileExprComb cfg "declared type" targetType
                            let valueC ← compileExprComb cfg "declared value" targetValue
                            let (inferSortExpr, _) ← stageExprWithState st0 (eraseConstLevelInsts native.loweredInferSort)
                            let (whnfTypeExpr, _) ← stageExprWithState st0 (eraseConstLevelInsts native.loweredWhnfType)
                            let (whnfValueExpr, _) ← stageExprWithState st0 (eraseConstLevelInsts native.loweredWhnfValue)
                            let (inferTypeExpr, _) ← stageExprWithState st0 (eraseConstLevelInsts native.loweredInferType)
                            let inferSortC ← compileExprComb cfg "native infer(type)" inferSortExpr
                            let whnfTypeC ← compileExprComb cfg "native whnf(type)" whnfTypeExpr
                            let whnfValueC ← compileExprComb cfg "native whnf(value)" whnfValueExpr
                            let inferTypeC ← compileExprComb cfg "native infer(value)" inferTypeExpr
                            let inferSortZeroKernelC ← compileLitAwareInferSortZeroKernel cfg
                            let inferValueShapeC ← optExprIsSomeComb cfg
                            let natIdC ← encodeFuelComb cfg "staged Nat const id" (← stagedConstId st0 natConstName)
                            let stringIdC ← encodeFuelComb cfg "staged String const id" (← stagedConstId st0 stringConstName)
                            let (inferKernelC, checkKernelC) ← compileLitAwareInferCheck cfg
                            let rulesC ← compileIotaRulesComb cfg senv
                            pure
                              ( envC, fuelWhnfC, fuelDefEqC, fuelInferC
                              , typeC, valueC
                              , inferSortC, whnfTypeC, whnfValueC, inferTypeC
                              , inferSortZeroKernelC, inferValueShapeC, natIdC, stringIdC
                              , inferKernelC, checkKernelC, rulesC)
                          match compileResult with
                          | .ok (envC, fuelWhnfC, fuelDefEqC, fuelInferC, typeC, valueC, inferSortC, whnfTypeC, whnfValueC, inferTypeC, inferSortZeroKernelC, inferValueShapeC, natIdC, stringIdC, inferKernelC, checkKernelC, rulesC) =>
                              let inferTypeSortOutOpt :=
                                applyLitAwareInferKernel inferKernelC envC rulesC natIdC stringIdC fuelInferC compiled.emptyCtx typeC
                              let inferTypeSortDecoded? :=
                                FullKernelSKY.decodeOptExprCombFuel cfg.fuelReduce inferTypeSortOutOpt
                              let whnfTypeOut :=
                                Comb.app
                                  (Comb.app
                                    (Comb.app
                                      (Comb.app compiled.whnf envC)
                                      rulesC)
                                    fuelWhnfC)
                                  typeC
                              let whnfTypeCheck :=
                                Comb.app
                                  (Comb.app
                                    (Comb.app
                                      (Comb.app
                                        (Comb.app compiled.isDefEq envC)
                                        rulesC)
                                      fuelDefEqC)
                                    whnfTypeOut)
                                  whnfTypeC
                              let whnfValueOut :=
                                Comb.app
                                  (Comb.app
                                    (Comb.app
                                      (Comb.app compiled.whnf envC)
                                      rulesC)
                                    fuelWhnfC)
                                  valueC
                              let whnfValueCheck :=
                                Comb.app
                                  (Comb.app
                                    (Comb.app
                                      (Comb.app
                                        (Comb.app compiled.isDefEq envC)
                                        rulesC)
                                      fuelDefEqC)
                                    whnfValueOut)
                                  whnfValueC
                              let inferOutOpt :=
                                applyLitAwareInferKernel inferKernelC envC rulesC natIdC stringIdC fuelInferC compiled.emptyCtx valueC
                              let inferDecodedPayload? :=
                                FullKernelSKY.decodeOptExprCombFuel cfg.fuelReduce inferOutOpt
                              let defeqCheck :=
                                Comb.app
                                  (Comb.app
                                    (Comb.app
                                      (Comb.app
                                        (Comb.app compiled.isDefEq envC)
                                        rulesC)
                                      fuelDefEqC)
                                    inferTypeC)
                                  typeC
                              let checkOut :=
                                applyLitAwareCheckKernel checkKernelC envC rulesC natIdC stringIdC fuelInferC compiled.emptyCtx valueC typeC
                              let mut operations := #[]
                              if opEnabled cfg .inferTypeSort then
                                if isSortZeroExpr native.loweredInferSort then
                                  let (opJson, _) ←
                                    boolOperationJsonTimed
                                      cfg
                                      .inferTypeSort
                                      declName
                                      native.loweredType
                                      true
                                      native.inferTypeMs
                                      (applyLitAwareInferKernel inferSortZeroKernelC envC rulesC natIdC stringIdC fuelInferC compiled.emptyCtx typeC)
                                      #[]
                                      true
                                      (some native.loweredInferSort)
                                  operations := operations.push <|
                                    Json.mergeObj opJson <| Json.mkObj
                                      [ ("semantic_mode", Json.str "option_sort_zero_semantic_check")
                                      , ("comparison_mode", Json.str "opt_expr_is_some_sort_zero")
                                      ]
                                else
                                  match inferTypeSortDecoded? with
                                  | some inferTypeSortDecoded =>
                                      let (opJson, _) ←
                                        directStateOperationJsonTimed
                                          cfg
                                          .inferTypeSort
                                          declName
                                          native.loweredType
                                          native.loweredInferSort
                                          native.inferTypeMs
                                          inferTypeSortDecoded
                                          inferSortC
                                      operations := operations.push opJson
                                  | none =>
                                      operations := operations.push <|
                                        skippedOperationJson
                                          .inferTypeSort
                                          declName
                                          native.loweredType
                                          native.loweredInferSort
                                          native.inferTypeMs
                                          "machine infer(type) output did not decode to Some payload"
                                          #[]
                                          (some "recursive_whnf_spine")
                              if opEnabled cfg .whnfType then
                                operations := operations.push <|
                                  boolOperationJson
                                    cfg
                                    .whnfType
                                    declName
                                    native.loweredType
                                    true
                                    native.whnfTypeMs
                                    whnfTypeCheck
                                    #[]
                                    true
                                    (some native.loweredWhnfType)
                              if opEnabled cfg .whnfValue then
                                operations := operations.push <|
                                  boolOperationJson
                                    cfg
                                    .whnfValue
                                    declName
                                    native.loweredValue
                                    true
                                    native.whnfValueMs
                                    whnfValueCheck
                                    #[]
                                    true
                                    (some native.loweredWhnfValue)
                              if opEnabled cfg .inferValueShape then
                                operations := operations.push <|
                                  boolOperationJson
                                    cfg
                                    .inferValueShape
                                    declName
                                    native.loweredValue
                                    true
                                    native.inferValueMs
                                    (Comb.app inferValueShapeC inferOutOpt)
                                    #[]
                                    true
                                    (some native.loweredInferType)
                              if opEnabled cfg .inferValue then
                                match inferDecodedPayload? with
                                | some inferDecodedPayload =>
                                    let (opJson, _) ←
                                      directStateOperationJsonTimed
                                        cfg
                                        .inferValue
                                        declName
                                        native.loweredValue
                                        native.loweredInferType
                                        native.inferValueMs
                                        inferDecodedPayload
                                        inferTypeC
                                        #[.inferValueShape]
                                    operations := operations.push opJson
                                | none =>
                                    operations := operations.push <|
                                      skippedOperationJson
                                        .inferValue
                                        declName
                                        native.loweredValue
                                        native.loweredInferType
                                        native.inferValueMs
                                        "machine infer output did not decode to Some payload"
                                        #[.inferValueShape]
                                        (some "recursive_whnf_spine")
                              if opEnabled cfg .defEqInferredDeclared then
                                operations := operations.push <|
                                  boolOperationJson cfg .defEqInferredDeclared declName native.loweredInferType native.defeqInferredDeclared native.defeqMs defeqCheck
                              if opEnabled cfg .checkValue then
                                operations := operations.push <|
                                  boolOperationJson cfg .checkValue declName native.loweredValue native.checkValue native.checkMs checkOut #[.inferValueShape, .inferValue, .defEqInferredDeclared] false
                              let eligibleOps :=
                                operations.foldl (init := 0) fun acc j =>
                                  match j.getObjValAs? Bool "eligible" with
                                  | .ok true => acc + 1
                                  | _ => acc
                              pure <| Json.mkObj <| declJsonBase moduleName declName kind ++
                                [ ("eligible", Json.bool (eligibleOps = operations.size))
                                , ("skip_reason", if eligibleOps = operations.size then Json.null else Json.str "one or more operations did not normalize to the expected boolean")
                                , ("universe_policy", Json.str "Lean.Level.param/mvar payloads erased to Unit")
                                , ("expr_meta_policy", Json.str "Lean.Expr.mvar payloads erased to Unit")
                                , ("iota_policy", Json.str "empty iota rules")
                                , ("erased_universe_payload", Json.bool st0.erasedUniversePayload)
                                , ("erased_expr_metas", Json.bool st0.erasedExprMetas)
                                , ("env_const_count", toJson closure.size)
                                , ("native_total_ms", toJson (native.whnfTypeMs + native.whnfValueMs + native.inferTypeMs + native.inferValueMs + native.defeqMs + native.checkMs))
                                , ("eligible_operations", toJson eligibleOps)
                                , ("operations", Json.arr operations)
                                ]
                          | .error err =>
                              pure <| skipDeclJson moduleName declName kind err

private def traceDecl
    (env : Lean.Environment)
    (cfg : Cfg)
    (moduleName : Name)
    (declName : Name)
    (ci : ConstantInfo) : IO Json := do
  let _ := env
  let _ := cfg
  let kind := constKind ci
  pure <| Json.mkObj <| declJsonBase moduleName declName kind ++
    [ ("trace_mode", Json.bool true)
    , ("trace_complete", Json.bool false)
    , ("skip_reason", Json.str "trace mode is unavailable on the verified_check executable path; use `lake env lean --run VerifiedCheckImportDriver.lean ...` for trace diagnostics")
    , ("trace_entries", Json.arr #[])
    ]

def main (argv : List String) : IO UInt32 := do
  match parseArgs argv with
  | .error err =>
      IO.eprintln err
      pure 1
  | .ok cfg => do
      try
        appendPhaseTrace cfg cfg.moduleName "main_parse_done"
          [ ("include_decl_count", toJson cfg.includeDecls.size)
          , ("only_op_count", toJson cfg.onlyOpKinds.size)
          ]
        let cfg ← traceCfgForExport cfg
        appendPhaseTrace cfg cfg.moduleName "bootstrap_start"
        HeytingLean.CLI.EnvBootstrap.bootstrapSearchPath
        appendPhaseTrace cfg cfg.moduleName "bootstrap_done"
        appendPhaseTrace cfg cfg.moduleName "module_import_start"
        let env ← importModules #[HeytingLean.CLI.EnvBootstrap.moduleImportFromString cfg.moduleName.toString] {}
        appendPhaseTrace cfg cfg.moduleName "module_import_done"
        let decls :=
          if cfg.includeDecls.isEmpty then
            moduleDecls env cfg.moduleName
          else
            includedDecls env cfg.moduleName cfg.includeDecls
        let selected :=
          let base :=
            if cfg.includeDecls.isEmpty then
              decls
            else
              includedDecls env cfg.moduleName cfg.includeDecls
          match cfg.maxDecls with
          | some n => base.take n
          | none => base
        appendPhaseTrace cfg cfg.moduleName "decl_selection_done"
          [ ("total_declarations", toJson decls.size)
          , ("selected_declarations", toJson selected.size)
          ]
        match cfg.traceGrain? with
        | some traceGrain =>
          let traceCfg := { cfg with traceGrain? := some traceGrain }
          let exports ←
            if cfg.listOnly then
              pure <| selected.map (fun (declName, ci) => listDeclJson cfg.moduleName declName (constKind ci))
            else
              selected.mapM (fun (declName, ci) => traceDecl env traceCfg cfg.moduleName declName ci)
          let totalTraceEntries :=
            if cfg.listOnly then 0 else
              exports.foldl (init := 0) fun acc j =>
                match j.getObjVal? "trace_entries" with
                | .ok (.arr xs) => acc + xs.size
                | _ => acc
          let totalSteps :=
            if cfg.listOnly then 0 else
              exports.foldl (init := 0) fun acc j => acc + jsonNatD j "step_count"
          let betaZetaSteps :=
            if cfg.listOnly then 0 else
              exports.foldl (init := 0) fun acc j => acc + jsonNatD j "beta_zeta_steps"
          let projectedBetaZetaSteps :=
            if cfg.listOnly then 0 else
              exports.foldl (init := 0) fun acc j => acc + jsonNatD j "projected_beta_zeta_steps"
          let traceCompleteDecls :=
            if cfg.listOnly then 0 else
              exports.foldl (init := 0) fun acc j =>
                if jsonBoolD j "trace_complete" then acc + 1 else acc
          let whnfCallsTotal :=
            if cfg.listOnly || traceGrain != .whnf then 0 else
              exports.foldl (init := 0) fun acc j => acc + jsonNatD j "whnf_call_count"
          let whnfCallsWithBetaZeta :=
            if cfg.listOnly || traceGrain != .whnf then 0 else
              exports.foldl (init := 0) fun acc j => acc + jsonNatD j "whnf_calls_with_beta_zeta"
          let whnfCallsDeltaIotaOnly :=
            if cfg.listOnly || traceGrain != .whnf then 0 else
              exports.foldl (init := 0) fun acc j => acc + jsonNatD j "whnf_calls_delta_iota_only"
          let payload := Json.mkObj
            [ ("tool", Json.str "verified_check")
            , ("mode", Json.str "trace_whnf")
            , ("trace_grain", Json.str (toString traceGrain))
            , ("module", Json.str cfg.moduleName.toString)
            , ("selection_mode", Json.str <|
                if cfg.listOnly then
                  if cfg.includeDecls.isEmpty then "module_scan_list_only" else "explicit_include_list_only"
                else if cfg.includeDecls.isEmpty then
                  "module_scan"
                else
                  "explicit_include")
            , ("list_only", Json.bool cfg.listOnly)
            , ("total_declarations", toJson decls.size)
            , ("selected_declarations", toJson selected.size)
            , ("trace_complete_declarations", toJson traceCompleteDecls)
            , ("total_trace_entries", toJson totalTraceEntries)
            , ("total_steps", toJson totalSteps)
            , ("beta_zeta_steps", toJson betaZetaSteps)
            , ("projected_beta_zeta_steps", toJson projectedBetaZetaSteps)
            , ("whnf_calls_total", toJson whnfCallsTotal)
            , ("whnf_calls_with_beta_zeta", toJson whnfCallsWithBetaZeta)
            , ("whnf_calls_delta_iota_only", toJson whnfCallsDeltaIotaOnly)
            , ("trace_max_steps", toJson cfg.traceMaxSteps)
            , ("fuel_whnf", toJson cfg.fuelWhnf)
            , ("fuel_defeq", toJson cfg.fuelDefEq)
            , ("fuel_reduce", toJson cfg.fuelReduce)
            , ("max_nodes", toJson cfg.maxNodes)
            , ("bracket_mode", Json.str (bracketModeString cfg.bracketMode))
            , ("declarations", Json.arr exports)
            , ("honest_assessment", Json.str <|
                if traceGrain == .step then
                  "This mode records native WHNF small-step traces only. Phase 2 compiles beta/zeta rows into SKY obligations in a separate pass via sky_replay --encode-whnf-steps; delta and iota remain native-only."
                else
                  "This mode records native WHNF calls at coarser grain while projecting only the beta/zeta portion into GPU-verifiable SKY obligations. Delta and iota remain native-only and can still make the projected WHNF output differ from the full native Meta.whnf result.")
            ]
          writeSkyArtifact cfg (buildSkyArtifact cfg exports selected.size decls.size)
          writeOutput cfg payload
        | none =>
          appendPhaseTrace cfg cfg.moduleName "bundle_compile_start"
            [ ("bundle_mode",
                Json.str <|
                  match singleWhnfOp? cfg, singleDefEqOp? cfg with
                  | some _, _ => "single_whnf"
                  | none, true => "single_defeq"
                  | none, false => "full")
            ]
          let compiled? := compileExportBundleWithMode? cfg
          appendPhaseTrace cfg cfg.moduleName "bundle_compile_done"
            [ ("bundle_available", Json.bool compiled?.isSome) ]
          let exports ←
            if cfg.listOnly then
              pure <| selected.map (fun (declName, ci) => listDeclJson cfg.moduleName declName (constKind ci))
            else
              match compiled? with
              | none =>
                  pure <| selected.map (fun (declName, ci) =>
                    skipDeclJson cfg.moduleName declName (constKind ci) "failed to compile FullKernelSKY bundle")
              | some compiled =>
                  selected.mapM (fun (declName, ci) => exportDecl env compiled cfg cfg.moduleName declName ci)
          let eligibleDeclCount :=
            if cfg.listOnly then
              0
            else
              exports.foldl (init := 0) fun acc j =>
                match j.getObjValAs? Bool "eligible" with
                | .ok true => acc + 1
                | _ => acc
          let eligibleOperationCount :=
            if cfg.listOnly then
              0
            else
              exports.foldl (init := 0) fun acc j =>
                match j.getObjValAs? Nat "eligible_operations" with
                | .ok n => acc + n
                | .error _ => acc
          let totalOperationCount :=
            if cfg.listOnly then
              0
            else
              exports.foldl (init := 0) fun acc j =>
                match j.getObjVal? "operations" with
                | Except.ok (.arr ops) => acc + ops.size
                | _ => acc
          let payload := Json.mkObj
            [ ("tool", Json.str "verified_check")
            , ("module", Json.str cfg.moduleName.toString)
            , ("selection_mode", Json.str <|
                if cfg.listOnly then
                  if cfg.includeDecls.isEmpty then "module_scan_list_only" else "explicit_include_list_only"
                else if cfg.includeDecls.isEmpty then
                  "module_scan"
                else
                  "explicit_include")
            , ("list_only", Json.bool cfg.listOnly)
            , ("total_declarations", toJson decls.size)
            , ("selected_declarations", toJson selected.size)
            , ("eligible_declarations", toJson eligibleDeclCount)
            , ("skipped_declarations", toJson (selected.size - eligibleDeclCount))
            , ("total_operations", toJson totalOperationCount)
            , ("eligible_operations", toJson eligibleOperationCount)
            , ("fuel_whnf", toJson cfg.fuelWhnf)
            , ("fuel_defeq", toJson cfg.fuelDefEq)
            , ("fuel_infer", toJson cfg.fuelInfer)
            , ("fuel_reduce", toJson cfg.fuelReduce)
            , ("max_nodes", toJson cfg.maxNodes)
            , ("max_env_consts", toJson cfg.maxEnvConsts)
            , ("machine_export_only", Json.bool cfg.machineExportOnly)
            , ("only_op_kinds", Json.arr <| cfg.onlyOpKinds.map (fun kind => Json.str (toString kind)))
            , ("bracket_mode", Json.str (bracketModeString cfg.bracketMode))
            , ("declarations", Json.arr exports)
            ]
          writeSkyArtifact cfg (buildSkyArtifact cfg exports selected.size decls.size)
          writeOutput cfg payload
        pure 0
      catch e =>
        IO.eprintln s!"[verified_check] FAILED: {e}"
        pure 1

end HeytingLean.CLI.VerifiedCheck

open HeytingLean.CLI.VerifiedCheck in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.VerifiedCheck.main args
