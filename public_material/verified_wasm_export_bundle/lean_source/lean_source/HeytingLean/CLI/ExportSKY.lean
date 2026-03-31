import Lean
import Lean.Data.Json
import HeytingLean.CLI.EnvBootstrap
import HeytingLean.CLI.SKYTraceJson
import HeytingLean.LoF.Combinators.SKYExec
import HeytingLean.LoF.Combinators.SKYMachineBounded
import HeytingLean.LoF.LeanKernel.Environment
import HeytingLean.LoF.LeanKernel.EnvironmentSKY
import HeytingLean.LoF.LeanKernel.FullKernelSKY
import HeytingLean.Util.ModuleOwner

open Lean
open Lean.Meta
open System

open HeytingLean.LoF
open HeytingLean.LoF.Combinators
open HeytingLean.LoF.LeanKernel

namespace HeytingLean.CLI.ExportSKY

abbrev OracleRef := Unit
abbrev SLevel := ULevel Unit Unit
abbrev SExpr := Expr Nat Unit Unit Unit
abbrev SEnv := HeytingLean.LoF.LeanKernel.Environment.Env Nat Unit Unit Unit
abbrev SConstDecl := HeytingLean.LoF.LeanKernel.Environment.ConstDecl Nat Unit Unit Unit

structure Cfg where
  moduleName : Name
  output : Option FilePath := none
  bracketMode : Bracket.BracketMode := .classic
  listOnly : Bool := false
  batchExportOnly : Bool := false
  importValues : Bool := false
  fuelCheck : Nat := 20
  fuelReduce : Nat := 400000
  maxNodes : Nat := 200000
  maxDecls : Option Nat := none
  maxEnvConsts : Nat := 512
  includeDecls : Array Name := #[]
deriving Repr

structure InternState where
  nextId : Nat := 1
  names : Std.HashMap Name Nat := {}
  erasedUniversePayload : Bool := false
  erasedExprMetas : Bool := false
deriving Inhabited

structure PreparedDecl where
  name : Name
  owner : Name
  kind : String
  ci : ConstantInfo
  loweredType : Lean.Expr
  loweredValue? : Option Lean.Expr
  localDeps : Array Name

structure ReplayState where
  intern : InternState
  senv : SEnv
  knownNames : Std.HashSet Name
  importedConstCount : Nat := 0
  acceptedModuleDeclCount : Nat := 0

abbrev ConvertM := StateT InternState (Except String)

private def usage : String :=
  String.intercalate "\n"
    [ "Usage: export_sky <Module.Name> [--output FILE] [--list-only] [--batch-export-only] [--import-values] [--bracket-mode <classic|bulk>] [--fuel-check N] [--fuel-reduce N] [--max-nodes N] [--max-decls N] [--max-env-consts N]"
    , ""
    , "Export real module declarations as staged FullKernel SKY machine checks."
    , "Batch export mode keeps a persistent staged environment across declarations and exports"
    , "initial machine states without reducing them inside Lean."
    ]

private def parseNatFlag (flag value : String) : Except String Nat :=
  match value.toNat? with
  | some n => .ok n
  | none => .error s!"invalid {flag} value: {value}"

private def parseBracketMode (value : String) : Except String Bracket.BracketMode :=
  match value.trim.toLower with
  | "classic" => .ok .classic
  | "bulk" => .ok .bulk
  | _ => .error s!"invalid --bracket-mode value: {value}"

private def bracketModeString (mode : Bracket.BracketMode) : String :=
  match mode with
  | .classic => "classic"
  | .bulk => "bulk"

private def parseArgs (argv : List String) : Except String Cfg := do
  match argv with
  | [] => throw usage
  | moduleText :: rest =>
      let moduleName := HeytingLean.CLI.EnvBootstrap.moduleNameFromString moduleText
      let rec go (cfg : Cfg) : List String → Except String Cfg
        | [] => .ok cfg
        | "--output" :: path :: xs => go { cfg with output := some path } xs
        | "--list-only" :: xs => go { cfg with listOnly := true } xs
        | "--batch-export-only" :: xs => go { cfg with batchExportOnly := true } xs
        | "--import-values" :: xs => go { cfg with importValues := true } xs
        | "--bracket-mode" :: mode :: xs => do
            let bracketMode ← parseBracketMode mode
            go { cfg with bracketMode := bracketMode } xs
        | "--fuel-check" :: n :: xs => do
            let fuelCheck ← parseNatFlag "--fuel-check" n
            go { cfg with fuelCheck := fuelCheck } xs
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
        | "--include" :: names :: xs =>
            let includeDecls :=
              names.splitOn "," |>.foldl (init := cfg.includeDecls) fun acc piece =>
                let piece := piece.trim
                if piece.isEmpty then acc
                else acc.push (HeytingLean.CLI.EnvBootstrap.moduleNameFromString piece)
            go { cfg with includeDecls := includeDecls } xs
        | "--help" :: _ => throw usage
        | x :: _ => throw s!"unexpected argument: {x}\n\n{usage}"
      go { moduleName := moduleName } rest

private def binderInfoToStaged : Lean.BinderInfo → LeanKernel.BinderInfo
  | .default => .default
  | .implicit => .implicit
  | .strictImplicit => .strictImplicit
  | .instImplicit => .instImplicit

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
  | .thmInfo _ => none
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

private def runMetaAtEnv (env : Lean.Environment) (x : MetaM α) : IO α := do
  let ctxCore : Core.Context := { fileName := "<export_sky>", fileMap := default }
  let sCore : Core.State := { env := env }
  let (a, _, _) ← x.toIO ctxCore sCore
  pure a

private def lowerProjExpr (env : Lean.Environment) (e : Lean.Expr) : IO (Except String Lean.Expr) := do
  if !containsProj e then
    return Except.ok e
  try
    let lowered ← runMetaAtEnv env <|
      Meta.transform e (pre := fun term => do
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

private def buildStagedEnv
    (env : Lean.Environment)
    (targetName : Name)
    (closure : Array Name)
    (targetType targetValue : Lean.Expr) : IO (Except String (SEnv × SExpr × SExpr × InternState)) := do
  let seeds :=
    closure.foldl (init := #[targetName, natConstName, stringConstName]) fun acc name =>
      if acc.contains name then acc else acc.push name
  let normTargetTypeResult ← lowerProjExpr env targetType
  let normTargetValueResult ← lowerProjExpr env targetValue
  match normTargetTypeResult, normTargetValueResult with
  | .error err, _ => pure (Except.error err)
  | _, .error err => pure (Except.error err)
  | .ok normTargetType, .ok normTargetValue => do
      let mut normalizedDecls : Array (Name × Lean.Expr × Option Lean.Expr) := #[]
      for name in seeds do
        match envConstInfo? env name with
        | none => pure ()
        | some ci =>
            let normTypeResult ← lowerProjExpr env ci.type
            match normTypeResult with
            | .error err => return Except.error s!"while lowering {name}: {err}"
            | .ok normType =>
                let normValue? ←
                  if name == targetName then
                    pure none
                  else
                    match constantValueExpr? ci with
                    | none => pure none
                    | some value => do
                        let normValueResult ← lowerProjExpr env value
                        match normValueResult with
                        | .error err => return Except.error s!"while lowering {name}: {err}"
                        | .ok lowered => pure (some lowered)
                normalizedDecls := normalizedDecls.push (name, normType, normValue?)
      let convert : ConvertM (SEnv × SExpr × SExpr) := do
        let targetType' ← stageExpr normTargetType
        let targetValue' ← stageExpr normTargetValue
        let natId ← internName natConstName
        let stringId ← internName stringConstName
        let litTypeFn := fun lit =>
          match lit with
          | LeanKernel.Literal.natVal _ => some (.const natId [])
          | LeanKernel.Literal.strVal _ => some (.const stringId [])
        let mut senv : SEnv :=
          { beqName := fun a b => a == b
            consts := []
            casesOnSpecs := []
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

private def nodeToJson (n : SKYGraph.Node OracleRef) : Json :=
  match n with
  | .combK => Json.mkObj [("tag", Json.str "K")]
  | .combS => Json.mkObj [("tag", Json.str "S")]
  | .combY => Json.mkObj [("tag", Json.str "Y")]
  | .app f a => Json.mkObj [("tag", Json.str "app"), ("f", toJson f), ("a", toJson a)]
  | .oracle _ => Json.mkObj [("tag", Json.str "oracle")]

private def stateToJson (maxNodes fuel : Nat) (s : SKYMachineBounded.State OracleRef) : Json :=
  Json.mkObj
    [ ("maxNodes", toJson maxNodes)
    , ("fuel", toJson fuel)
    , ("nodesUsed", toJson s.nodes.size)
    , ("focus", toJson s.focus)
    , ("stack", toJson s.stack.toArray)
    , ("nodes", Json.arr (s.nodes.map nodeToJson))
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
  | .I => false
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

private def runMachineExport
    (cfg : Cfg)
    (decodeTerm expectedTagTerm : Comb) : Except String (Json × Json × Json × Nat × Nat × Nat × Bool) := do
  let s0 <-
    match SKYMachineBounded.State.compileComb? (OracleRef := OracleRef) cfg.maxNodes decodeTerm with
    | some s => pure s
    | none => throw s!"out of heap during compilation; increase --max-nodes (currently {cfg.maxNodes})"

  let rec runWithStats (fuel : Nat) (s : SKYMachineBounded.State OracleRef)
      (stepsTaken maxStack maxNodesUsed : Nat) (traceRev : List Json) :
      Nat × Nat × Nat × List Json × SKYMachineBounded.State.StepResult OracleRef :=
    let traceRev := HeytingLean.CLI.SKYTraceJson.traceSampleToJson stepsTaken s :: traceRev
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

  let matchesExpected := matchesCombSpine finalState finalState.focus finalState.stack expectedTagTerm
  let machineJson := stateToJson cfg.maxNodes cfg.fuelReduce s0
  let finalJson := stateToJson cfg.maxNodes cfg.fuelReduce finalState
  let traceJson := Json.arr traceRev.reverse.toArray
  pure (machineJson, finalJson, traceJson, stepsTaken, maxStack, maxNodesUsed, matchesExpected)

private def expectedTrueTag : Comb := SKYExec.bTrue

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
    ]

private def listDeclJson
    (moduleName : Name)
    (declName : Name)
    (kind : String)
    (hasExecutableValue : Bool) : Json :=
  Json.mkObj <| declJsonBase moduleName declName kind ++
    [ ("listed_only", Json.bool true)
    , ("has_executable_value", Json.bool hasExecutableValue)
    ]

private def declSelectionPriority (env : Lean.Environment) (declName : Name) : Nat :=
  if declName.isInternal || declName.isInternalDetail || Lean.isPrivateName declName then
    2
  else if env.isProjectionFn declName then
    1
  else
    0

private def exportDecl
    (env : Lean.Environment)
    (cfg : Cfg)
    (moduleName : Name)
    (declName : Name)
    (ci : ConstantInfo) : IO Json := do
  let kind := constKind ci
  if !isCheckableDecl ci then
    pure <| skipDeclJson moduleName declName kind s!"unsupported declaration kind {kind}"
  else if env.isProjectionFn declName then
    pure <| skipDeclJson moduleName declName kind "projection declarations are not lowered yet"
  else
    match constantValueExpr? ci with
    | none => pure <| skipDeclJson moduleName declName kind "declaration has no executable value"
    | some declValue => do
        let seedRefs := (collectConstRefs ci.type).toList ++ (collectConstRefs declValue).toList
        let closureResult ← closureNames env declName seedRefs cfg.maxEnvConsts
        match closureResult with
        | .error err => pure <| skipDeclJson moduleName declName kind err
        | .ok closure => do
            let stagedResult ← buildStagedEnv env declName closure ci.type declValue
            match stagedResult with
            | .error err =>
                pure <| skipDeclJson moduleName declName kind s!"staged conversion failed: {err}"
            | .ok (senv, targetType, targetValue, st) =>
                match FullKernelSKY.compileFullWithMode? cfg.bracketMode with
                | none => pure <| skipDeclJson moduleName declName kind "failed to compile FullKernelSKY bundle"
                | some compiled =>
                    match
                      EnvironmentSKY.envCombWithMode? cfg.bracketMode [] senv,
                      FullKernelSKY.encodeNatCombWithMode? cfg.bracketMode cfg.fuelCheck,
                      FullKernelSKY.compileExprNatUnitWithMode? cfg.bracketMode targetValue,
                      FullKernelSKY.compileExprNatUnitWithMode? cfg.bracketMode targetType
                    with
                    | some envC, some fuelC, some valueC, some typeC =>
                        let decodeTerm :=
                          Comb.app
                            (Comb.app
                              (Comb.app
                                (Comb.app
                                  (Comb.app (Comb.app compiled.check envC) compiled.emptyRules)
                                  fuelC)
                                compiled.emptyCtx)
                              valueC)
                            typeC
                        match runMachineExport cfg decodeTerm expectedTrueTag with
                        | .error err =>
                            pure <| skipDeclJson moduleName declName kind s!"machine export failed: {err}"
                        | .ok (machineJson, finalJson, traceJson, stepsTaken, maxStack, maxNodesUsed, matchesExpected) =>
                            let nodeCount :=
                              match machineJson.getObjValAs? Nat "nodesUsed" with
                              | .ok n => n
                              | .error _ => 0
                            pure <| Json.mkObj <| declJsonBase moduleName declName kind ++
                              [ ("eligible", Json.bool matchesExpected)
                              , ("skip_reason", if matchesExpected then Json.null else Json.str "staged CPU check did not normalize to true")
                              , ("universe_policy", Json.str "Lean.Level.param/mvar payloads erased to Unit")
                              , ("expr_meta_policy", Json.str "Lean.Expr.mvar payloads erased to Unit")
                              , ("iota_policy", Json.str "empty iota rules")
                              , ("erased_universe_payload", Json.bool st.erasedUniversePayload)
                              , ("erased_expr_metas", Json.bool st.erasedExprMetas)
                              , ("env_const_count", toJson closure.size)
                              , ("node_count", toJson nodeCount)
                              , ("steps_taken", toJson stepsTaken)
                              , ("max_stack", toJson maxStack)
                              , ("max_nodes_used", toJson maxNodesUsed)
                              , ("expected_tag_term", Json.str (reprStr expectedTrueTag))
                              , ("machine_json", machineJson)
                              , ("final_json", finalJson)
                              , ("trace_json", traceJson)
                              ]
                    | _, _, _, _ =>
                        pure <| skipDeclJson moduleName declName kind "failed to compile staged check inputs to closed SKY terms"

private def ownerModuleOf (env : Lean.Environment) (name : Name) : Name :=
  HeytingLean.Util.moduleOwnerOf env name

private def rawLocalDeps
    (localNames : Std.HashSet Name)
    (declName : Name)
    (ci : ConstantInfo) : Array Name :=
  let refs0 := collectConstRefs ci.type
  let refs :=
    match constantValueExpr? ci with
    | some value => collectConstRefs value refs0
    | none => refs0
  refs.toList.foldl (init := #[]) fun acc ref =>
    if ref != declName && localNames.contains ref && !acc.contains ref then acc.push ref else acc

private partial def expandSelectedClosure
    (localDepsMap : Std.HashMap Name (Array Name))
    (queue : List Name)
    (seen : Std.HashSet Name := {}) : Std.HashSet Name :=
  match queue with
  | [] => seen
  | name :: rest =>
      if seen.contains name then
        expandSelectedClosure localDepsMap rest seen
      else
        let next :=
          match localDepsMap.get? name with
          | some deps => deps.toList ++ rest
          | none => rest
        expandSelectedClosure localDepsMap next (seen.insert name)

private def lowerConstantValue? (env : Lean.Environment) (ci : ConstantInfo) :
    IO (Except String (Option Lean.Expr)) := do
  match constantValueExpr? ci with
  | none => pure (.ok none)
  | some value =>
      let result ← lowerProjExpr env value
      match result with
      | .ok lowered => pure (.ok (some lowered))
      | .error err => pure (.error err)

private def prepareDecl
    (env : Lean.Environment)
    (localNames : Std.HashSet Name)
    (declName : Name)
    (ci : ConstantInfo) : IO (Except String PreparedDecl) := do
  let owner := ownerModuleOf env declName
  let loweredTypeResult ← lowerProjExpr env ci.type
  let loweredValueResult ← lowerConstantValue? env ci
  match loweredTypeResult, loweredValueResult with
  | .error err, _ => pure (.error s!"while lowering {declName}: {err}")
  | _, .error err => pure (.error s!"while lowering {declName}: {err}")
  | .ok loweredType, .ok loweredValue? =>
      let refs0 := collectConstRefs loweredType
      let refs :=
        match loweredValue? with
        | some loweredValue => collectConstRefs loweredValue refs0
        | none => refs0
      let localDeps :=
        refs.toList.foldl (init := #[]) fun acc ref =>
          if ref != declName && localNames.contains ref && !acc.contains ref then acc.push ref else acc
      pure <| .ok
        { name := declName
          owner := owner
          kind := constKind ci
          ci := ci
          loweredType := loweredType
          loweredValue? := loweredValue?
          localDeps := localDeps }

private partial def topoVisit
    (prepared : Std.HashMap Name PreparedDecl)
    (name : Name)
    (temporary : Std.HashSet Name)
    (permanent : Std.HashSet Name)
    (order : Array Name) :
    Std.HashSet Name × Std.HashSet Name × Array Name :=
  if permanent.contains name then
    (temporary, permanent, order)
  else if temporary.contains name then
    (temporary, permanent.insert name, order.push name)
  else
    let temporary := temporary.insert name
    match prepared.get? name with
    | none => (temporary.erase name, permanent.insert name, order.push name)
    | some info =>
        let (temporary, permanent, order) :=
          info.localDeps.foldl
            (init := (temporary, permanent, order))
            (fun (temporary, permanent, order) dep =>
              topoVisit prepared dep temporary permanent order)
        (temporary.erase name, permanent.insert name, order.push name)

private def topologicalOrder (decls : Array PreparedDecl) : Array PreparedDecl :=
  let preparedMap :=
    decls.foldl (init := ({} : Std.HashMap Name PreparedDecl)) fun acc info =>
      acc.insert info.name info
  let (_, _, names) :=
    decls.foldl
      (init := ({}, {}, #[]))
      (fun (temporary, permanent, order) info =>
        topoVisit preparedMap info.name temporary permanent order)
  names.foldl (init := #[]) fun acc name =>
    match preparedMap.get? name with
    | some info =>
        if acc.any (fun existing => existing.name == name) then acc else acc.push info
    | none => acc

private def mkEmptySEnv (natId stringId : Nat) : SEnv :=
  let litTypeFn := fun lit =>
    match lit with
    | LeanKernel.Literal.natVal _ => some (.const natId [])
    | LeanKernel.Literal.strVal _ => some (.const stringId [])
  { beqName := fun a b => a == b
    consts := []
    casesOnSpecs := []
    mvarType? := fun _ => none
    litType? := litTypeFn
  }

private def initReplayState : Except String ReplayState := do
  let bootstrap : ConvertM (Nat × Nat) := do
    let natId ← internName natConstName
    let stringId ← internName stringConstName
    pure (natId, stringId)
  match bootstrap.run {} with
  | .error err => .error err
  | .ok ((natId, stringId), intern) =>
      .ok
        { intern := intern
          senv := mkEmptySEnv natId stringId
          knownNames := {} }

private def stageConstDecl
    (name : Name)
    (loweredType : Lean.Expr)
    (loweredValue? : Option Lean.Expr) : ConvertM (SConstDecl × SExpr × Option SExpr) := do
  let stagedName ← internName name
  let stagedType ← stageExpr loweredType
  let stagedValue? ←
    match loweredValue? with
    | some value =>
        let stagedValue ← stageExpr value
        pure (some stagedValue)
    | none => pure none
  let decl : SConstDecl :=
    match stagedValue? with
    | some value => Environment.ConstDecl.ofDef stagedName stagedType value
    | none => Environment.ConstDecl.ofType stagedName stagedType
  pure (decl, stagedType, stagedValue?)

private def addStagedDecl
    (state : ReplayState)
    (name : Name)
    (decl : SConstDecl)
    (imported : Bool) : ReplayState :=
  { state with
    senv := state.senv.addConst decl
    knownNames := state.knownNames.insert name
    importedConstCount := if imported then state.importedConstCount + 1 else state.importedConstCount
    acceptedModuleDeclCount := if imported then state.acceptedModuleDeclCount else state.acceptedModuleDeclCount + 1 }

private partial def ensureImportedDependencies
    (env : Lean.Environment)
    (moduleName : Name)
    (cfg : Cfg)
    (state : ReplayState)
    (targetName : Name)
    (queue : List Name)
    (visited : Std.HashSet Name := {})
    (added : Nat := 0) : IO (Except String (ReplayState × Nat)) := do
  match queue with
  | [] => pure (.ok (state, added))
  | name :: rest =>
      if visited.contains name || name == targetName then
        ensureImportedDependencies env moduleName cfg state targetName rest (visited.insert name) added
      else if state.knownNames.contains name then
        ensureImportedDependencies env moduleName cfg state targetName rest (visited.insert name) added
      else
        let owner := ownerModuleOf env name
        if owner == moduleName then
          pure <| .error s!"local dependency {name} was not available when batch export reached {targetName}"
        else
          match envConstInfo? env name with
          | none =>
              ensureImportedDependencies env moduleName cfg state targetName rest (visited.insert name) added
          | some ci =>
              if state.knownNames.size >= cfg.maxEnvConsts then
                pure <| .error s!"incremental import cache exceeded --max-env-consts={cfg.maxEnvConsts} while expanding {targetName}"
              else
                let loweredTypeResult ← lowerProjExpr env ci.type
                let loweredValueResult ←
                  if cfg.importValues then
                    lowerConstantValue? env ci
                  else
                    pure (.ok none)
                match loweredTypeResult, loweredValueResult with
                | .error err, _ => pure (.error s!"while lowering imported dependency {name}: {err}")
                | _, .error err => pure (.error s!"while lowering imported dependency {name}: {err}")
                | .ok loweredType, .ok loweredValue? =>
                    match (stageConstDecl name loweredType loweredValue?).run state.intern with
                    | .error err => pure (.error s!"staged conversion failed for imported dependency {name}: {err}")
                    | .ok ((decl, _, _), intern') =>
                        let refs0 := collectConstRefs loweredType
                        let refs :=
                          match loweredValue? with
                          | some loweredValue => collectConstRefs loweredValue refs0
                          | none => refs0
                        let state' := addStagedDecl { state with intern := intern' } name decl true
                        ensureImportedDependencies env moduleName cfg state' targetName
                          (refs.toList ++ rest) (visited.insert name) (added + 1)

private def compileBatchMachineJson
    (cfg : Cfg)
    (decodeTerm : Comb) : Except String (Json × Nat) := do
  let s0 <-
    match SKYMachineBounded.State.compileComb? (OracleRef := OracleRef) cfg.maxNodes decodeTerm with
    | some s => pure s
    | none => throw s!"out of heap during compilation; increase --max-nodes (currently {cfg.maxNodes})"
  pure (stateToJson cfg.maxNodes cfg.fuelReduce s0, s0.nodes.size)

private def replayDeclJsonBase
    (moduleName : Name)
    (declName : Name)
    (kind : String)
    (replayIndex : Nat) : List (String × Json) :=
  declJsonBase moduleName declName kind ++ [("replay_index", toJson replayIndex)]

private def exportBatchDecl
    (compiled : FullKernelSKY.FullCompiled)
    (env : Lean.Environment)
    (cfg : Cfg)
    (moduleName : Name)
    (replayIndex : Nat)
    (state : ReplayState)
    (info : PreparedDecl) : IO (ReplayState × Json) := do
  let started ← IO.monoMsNow
  let deps0 := collectConstRefs info.loweredType
  let deps :=
    match info.loweredValue? with
    | some loweredValue => collectConstRefs loweredValue deps0
    | none => deps0
  let ensured ← ensureImportedDependencies env moduleName cfg state info.name deps.toList
  match ensured with
  | .error err =>
      let elapsed := (← IO.monoMsNow) - started
      pure
        ( state
        , Json.mkObj <| replayDeclJsonBase moduleName info.name info.kind replayIndex ++
            [ ("accepted", Json.bool false)
            , ("eligible", Json.bool false)
            , ("has_executable_value", Json.bool info.loweredValue?.isSome)
            , ("skip_reason", Json.str err)
            , ("elapsed_ms", toJson elapsed)
            , ("env_const_count_before", toJson state.knownNames.size)
            , ("env_const_count_after", toJson state.knownNames.size)
            , ("new_imported_consts", toJson 0)
            ] )
  | .ok (stateAfterImports, newImports) =>
      match (stageConstDecl info.name info.loweredType info.loweredValue?).run stateAfterImports.intern with
      | .error err =>
          let elapsed := (← IO.monoMsNow) - started
          pure
            ( stateAfterImports
            , Json.mkObj <| replayDeclJsonBase moduleName info.name info.kind replayIndex ++
                [ ("accepted", Json.bool false)
                , ("eligible", Json.bool false)
                , ("has_executable_value", Json.bool info.loweredValue?.isSome)
                , ("skip_reason", Json.str s!"staged conversion failed: {err}")
                , ("elapsed_ms", toJson elapsed)
                , ("env_const_count_before", toJson state.knownNames.size)
                , ("env_const_count_after", toJson stateAfterImports.knownNames.size)
                , ("new_imported_consts", toJson newImports)
                ] )
      | .ok ((decl, targetType, targetValue?), intern') =>
          let stateForCheck := { stateAfterImports with intern := intern' }
          match targetValue? with
          | none =>
              let acceptedState := addStagedDecl stateForCheck info.name decl false
              let elapsed := (← IO.monoMsNow) - started
              pure
                ( acceptedState
                , Json.mkObj <| replayDeclJsonBase moduleName info.name info.kind replayIndex ++
                    [ ("accepted", Json.bool true)
                    , ("eligible", Json.bool false)
                    , ("has_executable_value", Json.bool false)
                    , ("skip_reason", Json.str "declaration has no executable value; staged type added to incremental environment")
                    , ("elapsed_ms", toJson elapsed)
                    , ("env_const_count_before", toJson state.knownNames.size)
                    , ("env_const_count_after", toJson acceptedState.knownNames.size)
                    , ("new_imported_consts", toJson newImports)
                    ] )
          | some targetValue =>
              match EnvironmentSKY.envCombWithMode? cfg.bracketMode [] stateForCheck.senv,
                    FullKernelSKY.encodeNatCombWithMode? cfg.bracketMode cfg.fuelCheck,
                    FullKernelSKY.compileExprNatUnitWithMode? cfg.bracketMode targetValue,
                    FullKernelSKY.compileExprNatUnitWithMode? cfg.bracketMode targetType with
              | some envC, some fuelC, some valueC, some typeC =>
                  let decodeTerm :=
                    Comb.app
                      (Comb.app
                        (Comb.app
                          (Comb.app
                            (Comb.app (Comb.app compiled.check envC) compiled.emptyRules)
                            fuelC)
                          compiled.emptyCtx)
                        valueC)
                      typeC
                  match compileBatchMachineJson cfg decodeTerm with
                  | .error err =>
                      let elapsed := (← IO.monoMsNow) - started
                      pure
                        ( stateForCheck
                        , Json.mkObj <| replayDeclJsonBase moduleName info.name info.kind replayIndex ++
                            [ ("accepted", Json.bool false)
                            , ("eligible", Json.bool false)
                            , ("has_executable_value", Json.bool true)
                            , ("skip_reason", Json.str s!"machine export failed: {err}")
                            , ("elapsed_ms", toJson elapsed)
                            , ("env_const_count_before", toJson state.knownNames.size)
                            , ("env_const_count_after", toJson stateForCheck.knownNames.size)
                            , ("new_imported_consts", toJson newImports)
                            ] )
                  | .ok (machineJson, nodeCount) =>
                      let acceptedState := addStagedDecl stateForCheck info.name decl false
                      let elapsed := (← IO.monoMsNow) - started
                      pure
                        ( acceptedState
                        , Json.mkObj <| replayDeclJsonBase moduleName info.name info.kind replayIndex ++
                            [ ("accepted", Json.bool true)
                            , ("eligible", Json.bool true)
                            , ("has_executable_value", Json.bool true)
                            , ("skip_reason", Json.null)
                            , ("elapsed_ms", toJson elapsed)
                            , ("env_const_count_before", toJson state.knownNames.size)
                            , ("env_const_count_after", toJson acceptedState.knownNames.size)
                            , ("new_imported_consts", toJson newImports)
                            , ("erased_universe_payload", Json.bool stateForCheck.intern.erasedUniversePayload)
                            , ("erased_expr_metas", Json.bool stateForCheck.intern.erasedExprMetas)
                            , ("node_count", toJson nodeCount)
                            , ("expected_tag_term", Json.str (reprStr expectedTrueTag))
                            , ("machine_json", machineJson)
                            ] )
              | _, _, _, _ =>
                  let elapsed := (← IO.monoMsNow) - started
                  pure
                    ( stateForCheck
                    , Json.mkObj <| replayDeclJsonBase moduleName info.name info.kind replayIndex ++
                        [ ("accepted", Json.bool false)
                        , ("eligible", Json.bool false)
                        , ("has_executable_value", Json.bool true)
                        , ("skip_reason", Json.str "failed to compile staged check inputs to closed SKY terms")
                        , ("elapsed_ms", toJson elapsed)
                        , ("env_const_count_before", toJson state.knownNames.size)
                        , ("env_const_count_after", toJson stateForCheck.knownNames.size)
                        , ("new_imported_consts", toJson newImports)
                        ] )

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

private def writeOutput (cfg : Cfg) (payload : Json) : IO Unit := do
  let text := payload.pretty
  match cfg.output with
  | some path =>
      IO.FS.writeFile path (text ++ "\n")
      IO.println s!"[export_sky] wrote {path}"
  | none =>
      IO.println text

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

def main (argv : List String) : IO UInt32 := do
  match parseArgs argv with
  | .error err =>
      IO.eprintln err
      pure 1
  | .ok cfg => do
      try
        HeytingLean.CLI.EnvBootstrap.bootstrapSearchPath
        let env ← importModules #[HeytingLean.CLI.EnvBootstrap.moduleImportFromString cfg.moduleName.toString] {}
        let decls := moduleDecls env cfg.moduleName
        let selected :=
          let base :=
            if cfg.includeDecls.isEmpty then
              decls
            else
              includedDecls env cfg.moduleName cfg.includeDecls
          match cfg.maxDecls with
          | some n => base.take n
          | none => base
        if cfg.listOnly then
          let exports :=
            selected.map (fun (declName, ci) =>
              listDeclJson cfg.moduleName declName (constKind ci) ((constantValueExpr? ci).isSome))
          let payload := Json.mkObj
            [ ("module", Json.str cfg.moduleName.toString)
            , ("selection_mode", Json.str <|
                if cfg.includeDecls.isEmpty then "module_scan_list_only" else "explicit_include_list_only")
            , ("list_only", Json.bool true)
            , ("batch_export_only", Json.bool false)
            , ("total_declarations", toJson decls.size)
            , ("selected_declarations", toJson selected.size)
            , ("eligible_declarations", toJson 0)
            , ("skipped_declarations", toJson selected.size)
            , ("fuel_check", toJson cfg.fuelCheck)
            , ("fuel_reduce", toJson cfg.fuelReduce)
            , ("max_nodes", toJson cfg.maxNodes)
            , ("max_env_consts", toJson cfg.maxEnvConsts)
            , ("bracket_mode", Json.str (bracketModeString cfg.bracketMode))
            , ("declarations", Json.arr exports)
            ]
          writeOutput cfg payload
          pure 0
        else if cfg.batchExportOnly then
          let allLocalNames :=
            decls.foldl (init := ({} : Std.HashSet Name)) fun acc (name, _) => acc.insert name
          let localDepsMap :=
            decls.foldl (init := ({} : Std.HashMap Name (Array Name))) fun acc (name, ci) =>
              acc.insert name (rawLocalDeps allLocalNames name ci)
          let selectedNames :=
            expandSelectedClosure localDepsMap (selected.map (fun entry => entry.1) |>.toList)
          let selectedRaw :=
            decls.foldl (init := #[]) fun acc entry =>
              if selectedNames.contains entry.1 then acc.push entry else acc
          let localNames :=
            selectedRaw.foldl (init := ({} : Std.HashSet Name)) fun acc (name, _) => acc.insert name
          let mut preparedDecls : Array PreparedDecl := #[]
          let mut prepErrors : Array Json := #[]
          for (declName, ci) in selectedRaw do
            let prepared ← prepareDecl env localNames declName ci
            match prepared with
            | .ok info => preparedDecls := preparedDecls.push info
            | .error err =>
                prepErrors := prepErrors.push <| Json.mkObj
                  [ ("module", Json.str cfg.moduleName.toString)
                  , ("decl_name", Json.str declName.toString)
                  , ("decl_kind", Json.str (constKind ci))
                  , ("accepted", Json.bool false)
                  , ("eligible", Json.bool false)
                  , ("has_executable_value", Json.bool ((constantValueExpr? ci).isSome))
                  , ("skip_reason", Json.str err)
                  ]
          let ordered := topologicalOrder preparedDecls
          let some compiled := FullKernelSKY.compileFullWithMode? cfg.bracketMode
            | do
              IO.eprintln "[export_sky] FAILED: unable to compile FullKernelSKY bundle"
              pure 1
          let some initState := initReplayState.toOption
            | do
              IO.eprintln "[export_sky] FAILED: unable to initialize incremental export state"
              pure 1
          let exportStarted ← IO.monoMsNow
          let mut state := initState
          let mut results : Array Json := prepErrors
          for idx in [:ordered.size] do
            let some info := ordered[idx]?
              | continue
            let (state', detail) ← exportBatchDecl compiled env cfg cfg.moduleName idx state info
            state := state'
            results := results.push detail
          let exportElapsed := (← IO.monoMsNow) - exportStarted
          let eligibleCount :=
            results.foldl (init := 0) fun acc j =>
              match j.getObjValAs? Bool "eligible" with
              | .ok true => acc + 1
              | _ => acc
          let payload := Json.mkObj
            [ ("module", Json.str cfg.moduleName.toString)
            , ("selection_mode", Json.str <|
                if cfg.includeDecls.isEmpty then "module_scan_batch_export_only" else "explicit_include_batch_export_only")
            , ("list_only", Json.bool false)
            , ("batch_export_only", Json.bool true)
            , ("total_declarations", toJson decls.size)
            , ("selected_declarations", toJson selectedRaw.size)
            , ("prepared_declarations", toJson ordered.size)
            , ("eligible_declarations", toJson eligibleCount)
            , ("skipped_declarations", toJson (results.size - eligibleCount))
            , ("imported_const_count", toJson state.importedConstCount)
            , ("accepted_module_decl_count", toJson state.acceptedModuleDeclCount)
            , ("final_env_const_count", toJson state.knownNames.size)
            , ("fuel_check", toJson cfg.fuelCheck)
            , ("fuel_reduce", toJson cfg.fuelReduce)
            , ("max_nodes", toJson cfg.maxNodes)
            , ("max_env_consts", toJson cfg.maxEnvConsts)
            , ("bracket_mode", Json.str (bracketModeString cfg.bracketMode))
            , ("import_value_policy", Json.str <|
                if cfg.importValues then "imported defs carry values" else "imported defs staged type-only by default")
            , ("total_elapsed_ms", toJson exportElapsed)
            , ("honest_assessment", Json.str
                "This batch export path imports the module environment once, expands local declaration dependencies once, and stages imported constants lazily on first use. It exports initial FullKernel SKY machine states only; reduction and parity checking are expected to happen outside Lean.")
            , ("replay_order", Json.arr <| ordered.map (fun info => Json.str info.name.toString))
            , ("declarations", Json.arr results)
            ]
          writeOutput cfg payload
          pure 0
        else
          let exports ←
            selected.mapM (fun (declName, ci) => exportDecl env cfg cfg.moduleName declName ci)
          let eligibleCount :=
            exports.foldl (init := 0) fun acc j =>
              match j.getObjValAs? Bool "eligible" with
              | .ok true => acc + 1
              | _ => acc
          let payload := Json.mkObj
            [ ("module", Json.str cfg.moduleName.toString)
            , ("selection_mode", Json.str <|
                if cfg.includeDecls.isEmpty then "module_scan" else "explicit_include")
            , ("list_only", Json.bool false)
            , ("batch_export_only", Json.bool false)
            , ("total_declarations", toJson decls.size)
            , ("selected_declarations", toJson selected.size)
            , ("eligible_declarations", toJson eligibleCount)
            , ("skipped_declarations", toJson (selected.size - eligibleCount))
            , ("fuel_check", toJson cfg.fuelCheck)
            , ("fuel_reduce", toJson cfg.fuelReduce)
            , ("max_nodes", toJson cfg.maxNodes)
            , ("max_env_consts", toJson cfg.maxEnvConsts)
            , ("bracket_mode", Json.str (bracketModeString cfg.bracketMode))
            , ("declarations", Json.arr exports)
            ]
          writeOutput cfg payload
          pure 0
      catch e =>
        IO.eprintln s!"[export_sky] FAILED: {e}"
        pure 1

end HeytingLean.CLI.ExportSKY

open HeytingLean.CLI.ExportSKY in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.ExportSKY.main args
