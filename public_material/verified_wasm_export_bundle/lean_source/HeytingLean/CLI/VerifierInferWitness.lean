import Lean
import Lean.Data.Json
import HeytingLean.CLI.EnvBootstrap
import HeytingLean.CLI.LeanExprJson
import HeytingLean.CLI.SKYStageCore
import HeytingLean.LoF.LeanKernel.Environment
import HeytingLean.LoF.LeanKernel.EnvironmentSKY
import HeytingLean.LoF.LeanKernel.FullKernelSKY
import HeytingLean.LoF.LeanKernel.DefEq
import HeytingLean.LoF.LeanKernel.Infer

open Lean
open System

namespace HeytingLean.CLI.VerifierInferWitness

open HeytingLean.CLI.SKYStageCore
open HeytingLean.LoF
open HeytingLean.LoF.Combinators
open HeytingLean.LoF.LeanKernel

abbrev SExpr := HeytingLean.CLI.SKYStageCore.SExpr
abbrev SEnv := HeytingLean.LoF.LeanKernel.Environment.Env Nat Unit Unit Unit
abbrev SConstDecl := HeytingLean.LoF.LeanKernel.Environment.ConstDecl Nat Unit Unit Unit

structure Cfg where
  moduleName : Name
  declName : Name
  output : Option FilePath := none
  bracketMode : Bracket.BracketMode := .classic
  directOnly : Bool := false
  fuelDefEq : Nat := 20
  fuelInfer : Nat := 20
  fuelReduce : Nat := 400000
  maxNodes : Nat := 200000
  maxEnvConsts : Nat := 512

private def usage : String :=
  String.intercalate "\n"
    [ "Usage: verifier_infer_witness <Module.Name> --decl Decl.Name [--output FILE] [--bracket-mode <classic|bulk>] [--direct-only] [--fuel-defeq N] [--fuel-infer N] [--fuel-reduce N] [--max-nodes N] [--max-env-consts N]"
    , ""
    , "Freeze one declaration-level infer witness by comparing:"
    , "  1. native Lean inferType (lowered)"
    , "  2. staged direct Infer.infer?"
    , "  3. SKY FullKernelSKY.infer"
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

private def parseArgs (argv : List String) : Except String Cfg := do
  match argv with
  | [] => throw usage
  | moduleText :: rest =>
      let moduleName := HeytingLean.CLI.EnvBootstrap.moduleNameFromString moduleText
      let rec go (declName? : Option Name) (cfg : Cfg) : List String → Except String Cfg
        | [] =>
            match declName? with
            | some declName => pure { cfg with declName := declName }
            | none => throw s!"missing required --decl\n\n{usage}"
        | "--decl" :: name :: xs =>
            go (some (HeytingLean.CLI.EnvBootstrap.moduleNameFromString name)) cfg xs
        | "--output" :: path :: xs =>
            go declName? { cfg with output := some path } xs
        | "--bracket-mode" :: mode :: xs => do
            let bracketMode ← parseBracketMode mode
            go declName? { cfg with bracketMode := bracketMode } xs
        | "--direct-only" :: xs =>
            go declName? { cfg with directOnly := true } xs
        | "--fuel-defeq" :: n :: xs => do
            let fuelDefEq ← parseNatFlag "--fuel-defeq" n
            go declName? { cfg with fuelDefEq := fuelDefEq } xs
        | "--fuel-infer" :: n :: xs => do
            let fuelInfer ← parseNatFlag "--fuel-infer" n
            go declName? { cfg with fuelInfer := fuelInfer } xs
        | "--fuel-reduce" :: n :: xs => do
            let fuelReduce ← parseNatFlag "--fuel-reduce" n
            go declName? { cfg with fuelReduce := fuelReduce } xs
        | "--max-nodes" :: n :: xs => do
            let maxNodes ← parseNatFlag "--max-nodes" n
            go declName? { cfg with maxNodes := maxNodes } xs
        | "--max-env-consts" :: n :: xs => do
            let maxEnvConsts ← parseNatFlag "--max-env-consts" n
            go declName? { cfg with maxEnvConsts := maxEnvConsts } xs
        | "--help" :: _ => throw usage
        | x :: _ => throw s!"unexpected argument: {x}\n\n{usage}"
      go none { moduleName := moduleName, declName := moduleName } rest

private def writeOutput (cfg : Cfg) (payload : Json) : IO Unit := do
  let text := payload.pretty
  match cfg.output with
  | some path =>
      IO.FS.writeFile path (text ++ "\n")
      IO.eprintln s!"[verifier_infer_witness] wrote {path}"
  | none =>
      IO.println text

private def constantValueExpr? : ConstantInfo → Option Lean.Expr
  | .defnInfo info => some info.value
  | .opaqueInfo info => some info.value
  | .thmInfo _ => none
  | _ => none

private def envConstInfo? (env : Lean.Environment) (n : Name) : Option ConstantInfo :=
  env.constants.find? n

private def internName (n : Name) : StateT InternState (Except String) Nat := do
  let st ← get
  match st.names.get? n with
  | some id => pure id
  | none =>
      let id := st.nextId
      set { st with nextId := id + 1, names := st.names.insert n id }
      pure id

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

private def natConstName : Name := `Nat
private def stringConstName : Name := `String

private partial def closureNames
    (env : Lean.Environment)
    (targetName : Name)
    (seed : List Name)
    (maxConsts : Nat) : IO (Except String (Array Name)) := do
  let rec loop (queue : List Name) (seen : Std.HashSet Name) (acc : Array Name) : IO (Except String (Array Name)) := do
    match queue with
    | [] => pure (.ok acc)
    | name :: rest =>
        if seen.contains name then
          loop rest seen acc
        else if acc.size >= maxConsts then
          pure <| .error s!"environment closure exceeded --max-env-consts={maxConsts} while expanding {targetName}"
        else
          let seen' := seen.insert name
          match envConstInfo? env name with
          | none => loop rest seen' acc
          | some ci =>
              let normTypeResult ← lowerProjExpr env ci.type
              match normTypeResult with
              | .error err => pure (.error s!"while lowering dependency {name}: {err}")
              | .ok normType =>
                  let refs0 := collectConstRefs normType
                  let refsResult ←
                    match constantValueExpr? ci with
                    | some value => do
                        let normValueResult ← lowerProjExpr env value
                        match normValueResult with
                        | .error err => pure (Except.error s!"while lowering dependency {name}: {err}")
                        | .ok normValue => pure (Except.ok (collectConstRefs normValue refs0))
                    | none =>
                        pure (Except.ok refs0)
                  match refsResult with
                  | .error err => pure (.error err)
                  | .ok refs =>
                      loop (refs.toList ++ rest) seen' (acc.push name)
  loop seed {} #[]

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
  | .error err, _ => pure (.error err)
  | _, .error err => pure (.error err)
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
      let convert : StateT InternState (Except String) (SEnv × SExpr × SExpr) := do
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
              | some normValue =>
                  let value' ← stageExpr normValue
                  pure (some value')
              | none =>
                  pure none
          let decl : SConstDecl :=
            match stagedValue? with
            | some value => Environment.ConstDecl.ofDef stagedName stagedType value
            | none => Environment.ConstDecl.ofType stagedName stagedType
          senv := senv.addConst decl
        pure (senv, targetType', targetValue')
      pure <|
        match convert.run {} with
        | .error err => .error err
        | .ok ((senv, targetType', targetValue'), st) => .ok (senv, targetType', targetValue', st)

private def withElapsedMs (action : IO α) : IO (α × Nat) := do
  let startMs ← IO.monoMsNow
  let value ← action
  let endMs ← IO.monoMsNow
  pure (value, endMs - startMs)

private def nativeInfer (env : Lean.Environment) (e : Lean.Expr) : IO (Except String (Lean.Expr × Nat)) := do
  try
    let (result, elapsed) ← withElapsedMs <| runMetaAtEnv env do
      let ty ← Meta.inferType e
      instantiateMVars ty
    pure (.ok (result, elapsed))
  catch ex =>
    pure (.error s!"native inferType failed: {ex}")

private def compileExprComb (cfg : Cfg) (what : String) (e : SExpr) : Except String Comb := do
  match FullKernelSKY.compileExprNatUnitWithMode? cfg.bracketMode e with
  | some v => pure v
  | none => throw s!"failed to compile {what} to Comb"

private def encodeFuelComb (cfg : Cfg) (what : String) (n : Nat) : Except String Comb := do
  match FullKernelSKY.encodeNatCombWithMode? cfg.bracketMode n with
  | some v => pure v
  | none => throw s!"failed to encode {what}"

private def jsonStringArray (xs : Array String) : Json :=
  Json.arr <| xs.map Json.str

private def exprTag (e : SExpr) : String :=
  match e with
  | .bvar _ => "bvar"
  | .mvar _ => "mvar"
  | .sort _ => "sort"
  | .const _ _ => "const"
  | .app _ _ => "app"
  | .lam _ _ _ _ => "lam"
  | .forallE _ _ _ _ => "forallE"
  | .letE _ _ _ _ _ => "letE"
  | .lit _ => "lit"

private def defeqStaged (env : SEnv) (fuel : Nat) (lhs rhs : SExpr) : Bool :=
  let cfg0 := Environment.Env.toInferConfig (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) env
  DefEq.isDefEqWithDelta (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit)
    cfg0.constValue? cfg0.iotaRules fuel lhs rhs

private def faultDomain
    (nativeSome : Bool)
    (stagedDirectSome : Bool)
    (skySome : Bool)
    (stagedDirectMatchesNative : Bool)
    (skyMatchesStagedDirect : Bool)
    (skyMatchesNative : Bool) : String :=
  if nativeSome && !stagedDirectSome then
    "staging_or_environment_or_core_infer"
  else if stagedDirectSome && !stagedDirectMatchesNative then
    "staging_or_environment_or_core_infer"
  else if stagedDirectSome && !skySome then
    "fullkernelsky_or_infersky"
  else if skySome && !skyMatchesStagedDirect then
    "fullkernelsky_or_infersky"
  else if skySome && !skyMatchesNative then
    "fullkernelsky_or_infersky"
  else
    "no_gap_on_this_witness"

private def witnessJson
    (cfg : Cfg)
    (declName : Name)
    (closure : Array Name)
    (loweredValue loweredType loweredInferType : Lean.Expr)
    (nativeInferMs : Nat)
    (targetValue targetType inferTypeExpr : SExpr)
    (stagedDirectInfer? : Option SExpr)
    (skyTag? : Option String)
    (skySome : Bool)
    (stagedDirectMatchesNative : Bool)
    (skyMatchesStagedDirect : Bool)
    (skyMatchesNative : Bool) : Json :=
  Json.mkObj
    [ ("tool", Json.str "verifier_infer_witness")
    , ("module", Json.str cfg.moduleName.toString)
    , ("decl_name", Json.str declName.toString)
    , ("bracket_mode", Json.str (match cfg.bracketMode with | .classic => "classic" | .bulk => "bulk"))
    , ("fuel_defeq", toJson cfg.fuelDefEq)
    , ("fuel_infer", toJson cfg.fuelInfer)
    , ("fuel_reduce", toJson cfg.fuelReduce)
    , ("max_nodes", toJson cfg.maxNodes)
    , ("max_env_consts", toJson cfg.maxEnvConsts)
    , ("env_const_count", toJson closure.size)
    , ("closure_names", jsonStringArray (closure.map (fun n => n.toString)))
    , ("native_infer_elapsed_ms", toJson nativeInferMs)
    , ("native", Json.mkObj
        [ ("lowered_type_repr", Json.str (reprStr loweredType))
        , ("lowered_value_repr", Json.str (reprStr loweredValue))
        , ("lowered_infer_repr", Json.str (reprStr loweredInferType))
        , ("lowered_type_json", HeytingLean.CLI.LeanExprJson.exprToJson loweredType)
        , ("lowered_value_json", HeytingLean.CLI.LeanExprJson.exprToJson loweredValue)
        , ("lowered_infer_json", HeytingLean.CLI.LeanExprJson.exprToJson loweredInferType)
        ])
    , ("staged", Json.mkObj
        [ ("target_type_repr", Json.str (reprStr targetType))
        , ("target_value_repr", Json.str (reprStr targetValue))
        , ("native_infer_repr", Json.str (reprStr inferTypeExpr))
        , ("native_infer_tag", Json.str (exprTag inferTypeExpr))
        , ("direct_infer_some", Json.bool stagedDirectInfer?.isSome)
        , ("direct_infer_repr", Json.str (stagedDirectInfer?.map reprStr |>.getD "<none>"))
        , ("direct_infer_tag", Json.str (stagedDirectInfer?.map exprTag |>.getD "<none>"))
        , ("direct_matches_native", Json.bool stagedDirectMatchesNative)
        ])
    , ("sky", Json.mkObj
        [ ("skipped", Json.bool cfg.directOnly)
        , ("infer_some", Json.bool skySome)
        , ("infer_tag", Json.str (skyTag?.getD "<none>"))
        , ("matches_staged_direct", Json.bool skyMatchesStagedDirect)
        , ("matches_native", Json.bool skyMatchesNative)
        ])
    , ("localization", Json.mkObj
        [ ("fault_domain", Json.str <|
            faultDomain true stagedDirectInfer?.isSome skySome stagedDirectMatchesNative skyMatchesStagedDirect skyMatchesNative)
        , ("summary", Json.str <|
            if !stagedDirectInfer?.isSome then
              "Staged direct Infer.infer? already failed on this witness while native Lean inferType succeeded."
            else if !stagedDirectMatchesNative then
              "The staged direct Infer.infer? result differs from the native lowered infer result, so the gap is before SKY execution."
            else if cfg.directOnly then
              "Direct-only mode stopped before SKY execution."
            else if !skySome then
              "SKY infer returned none where staged direct inference produced a type."
            else if !skyMatchesStagedDirect then
              "SKY infer returned a payload that is not defeq to the staged direct Infer.infer? result."
            else if !skyMatchesNative then
              "SKY infer matches staged direct infer but not the native lowered infer result."
            else
              "All three layers agree on this witness.")
        ])
    ]

private def mainImpl (cfg : Cfg) : IO Json := do
  HeytingLean.CLI.EnvBootstrap.bootstrapSearchPath
  let env ← importModules #[HeytingLean.CLI.EnvBootstrap.moduleImportFromString cfg.moduleName.toString] {}
  let some ci := env.constants.find? cfg.declName
    | throw <| IO.userError s!"declaration not found: {cfg.declName}"
  let some declValue := constantValueExpr? ci
    | throw <| IO.userError s!"declaration has no executable value: {cfg.declName}"

  let loweredTypeResult ← lowerProjExpr env ci.type
  let loweredValueResult ← lowerProjExpr env declValue
  let nativeInferResult ← nativeInfer env declValue
  let loweredType ←
    match loweredTypeResult with
    | .ok e => pure e
    | .error err => throw <| IO.userError err
  let loweredValue ←
    match loweredValueResult with
    | .ok e => pure e
    | .error err => throw <| IO.userError err
  let (nativeInferExpr, nativeInferMs) ←
    match nativeInferResult with
    | .ok v => pure v
    | .error err => throw <| IO.userError err
  let loweredInferResult ← lowerProjExpr env nativeInferExpr
  let loweredInferType ←
    match loweredInferResult with
    | .ok e => pure e
    | .error err => throw <| IO.userError err

  let seedRefs :=
    (collectConstRefs loweredType).toList ++
    (collectConstRefs loweredValue).toList ++
    (collectConstRefs loweredInferType).toList
  let closureResult ← closureNames env cfg.declName seedRefs cfg.maxEnvConsts
  let closure ←
    match closureResult with
    | .ok xs => pure xs
    | .error err => throw <| IO.userError err

  let stagedResult ← buildStagedEnv env cfg.declName closure loweredType loweredValue
  let (senv, targetType, targetValue, st0) ←
    match stagedResult with
    | .ok v => pure v
    | .error err => throw <| IO.userError err

  let inferTypeStageResult := stageExprWithState st0 loweredInferType
  let inferTypeExpr ←
    match inferTypeStageResult with
    | .ok (e, _) => pure e
    | .error err => throw <| IO.userError err

  let cfg0 := Environment.Env.toInferConfig (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) senv
  let ctx0 : Infer.Ctx Nat Unit Unit Unit := .empty
  let stagedDirectInfer? := Infer.infer? cfg0 cfg.fuelInfer ctx0 targetValue
  let stagedDirectMatchesNative :=
    match stagedDirectInfer? with
    | some directTy => defeqStaged senv cfg.fuelDefEq directTy inferTypeExpr
    | none => false

  let (skyTag?, skySome, skyMatchesNative, skyMatchesStagedDirect) ←
    if cfg.directOnly then
      pure (none, false, false, false)
    else do
      let inferComb ←
        match FullKernelSKY.inferFullCombWithMode? cfg.bracketMode with
        | some v => pure v
        | none => throw <| IO.userError "failed to compile FullKernelSKY infer comb"
      let isDefEqComb ←
        match FullKernelSKY.isDefEqFullCombWithMode? cfg.bracketMode with
        | some v => pure v
        | none => throw <| IO.userError "failed to compile FullKernelSKY defeq comb"
      let emptyCtxComb ←
        match InferSKY.emptyCtxCombWithMode? cfg.bracketMode with
        | some v => pure v
        | none => throw <| IO.userError "failed to compile InferSKY emptyCtx comb"
      let emptyRulesComb ←
        match FullKernelSKY.emptyRulesCombWithMode? cfg.bracketMode with
        | some v => pure v
        | none => throw <| IO.userError "failed to compile empty rules comb"
      let envC ←
        match EnvironmentSKY.envCombWithMode? cfg.bracketMode [] senv with
        | some v => pure v
        | none => throw <| IO.userError "failed to compile staged environment"
      let fuelInferC ←
        match encodeFuelComb cfg "infer fuel" cfg.fuelInfer with
        | .ok v => pure v
        | .error err => throw <| IO.userError err
      let fuelDefEqC ←
        match encodeFuelComb cfg "defeq fuel" cfg.fuelDefEq with
        | .ok v => pure v
        | .error err => throw <| IO.userError err
      let valueC ←
        match compileExprComb cfg "declared value" targetValue with
        | .ok v => pure v
        | .error err => throw <| IO.userError err
      let inferTypeC ←
        match compileExprComb cfg "native infer result" inferTypeExpr with
        | .ok v => pure v
        | .error err => throw <| IO.userError err
      let inferOutOpt :=
        Comb.app
          (Comb.app
            (Comb.app
              (Comb.app
                (Comb.app inferComb envC)
                emptyRulesComb)
              fuelInferC)
            emptyCtxComb)
          valueC
      let skyTag? := FullKernelSKY.decodeOptExprTagFuel cfg.fuelReduce inferOutOpt
      let skyTy? := FullKernelSKY.decodeOptExprCombFuel cfg.fuelReduce inferOutOpt
      let skySome := skyTy?.isSome
      let skyMatchesNative :=
        match skyTy? with
        | some skyTy =>
            let out :=
              SKYExec.reduceFuel cfg.fuelReduce <|
                Comb.app (Comb.app (Comb.app (Comb.app (Comb.app isDefEqComb envC) emptyRulesComb) fuelDefEqC) skyTy) inferTypeC
            match SKYExec.decodeChurchBoolFuel cfg.fuelReduce out with
            | some true => true
            | _ => false
        | none => false
      let skyMatchesStagedDirect :=
        match skyTy?, stagedDirectInfer? with
        | some skyTy, some directTy =>
            match compileExprComb cfg "staged direct infer result" directTy with
            | .ok directTyC =>
                let out :=
                  SKYExec.reduceFuel cfg.fuelReduce <|
                    Comb.app (Comb.app (Comb.app (Comb.app (Comb.app isDefEqComb envC) emptyRulesComb) fuelDefEqC) skyTy) directTyC
                match SKYExec.decodeChurchBoolFuel cfg.fuelReduce out with
                | some true => true
                | _ => false
            | .error _ => false
        | _, _ => false
      pure (skyTag?, skySome, skyMatchesNative, skyMatchesStagedDirect)

  pure <|
    witnessJson
      cfg
      cfg.declName
      closure
      loweredValue
      loweredType
      loweredInferType
      nativeInferMs
      targetValue
      targetType
      inferTypeExpr
      stagedDirectInfer?
      skyTag?
      skySome
      stagedDirectMatchesNative
      skyMatchesStagedDirect
      skyMatchesNative

def main (argv : List String) : IO UInt32 := do
  match parseArgs argv with
  | .error err =>
      IO.eprintln err
      pure 1
  | .ok cfg =>
      try
        let payload ← mainImpl cfg
        writeOutput cfg payload
        pure 0
      catch ex =>
        IO.eprintln s!"[verifier_infer_witness] {ex}"
        pure 2

end HeytingLean.CLI.VerifierInferWitness
