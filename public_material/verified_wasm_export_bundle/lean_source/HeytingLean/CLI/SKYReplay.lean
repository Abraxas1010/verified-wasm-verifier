import Lean
import Lean.Data.Json
import HeytingLean.CLI.LeanExprJson
import HeytingLean.CLI.SKYStageCore
import HeytingLean.CLI.WHNFTrace

open Lean
open System

namespace HeytingLean.CLI.SKYReplay

inductive Mode where
  | stageExprs (input : FilePath)
  | encodeWhnfSteps (input : FilePath)
  | encodeWhnfCalls (input : FilePath)

structure Cfg where
  mode : Mode
  output : Option FilePath := none
  maxNodes : Nat := 200000
  fuelWhnf : Nat := 20
  fuelReduce : Nat := 400000
  fuelDefEq : Nat := 20

structure StepItem where
  ident : String
  declName : String
  traceRole : String
  kind : String
  seqId : Nat
  input : Lean.Expr
  output : Lean.Expr

structure WhnfCallItem where
  ident : String
  declName : String
  traceRole : String
  input : Lean.Expr
  output : Lean.Expr
  projectedBetaZetaSteps : Nat
  stepCount : Nat
  deltaIotaSteps : Nat

abbrev JObject := Std.TreeMap.Raw String Json compare

private def usage : String :=
  String.intercalate "\n"
    [ "Usage:"
    , "  sky_replay --stage-exprs INPUT.json [--output FILE] [--max-nodes N] [--fuel-reduce N]"
    , "  sky_replay --encode-whnf-steps TRACE.json [--output FILE] [--max-nodes N] [--fuel-reduce N] [--fuel-defeq N]"
    , "  sky_replay --encode-whnf-calls TRACE.json [--output FILE] [--max-nodes N] [--fuel-whnf N] [--fuel-reduce N] [--fuel-defeq N]"
    , ""
    , "Stage Lean Expr payloads or encode traced beta/zeta WHNF steps into bounded SKY machine states."
    ]

private def parseNatFlag (flag value : String) : Except String Nat :=
  match value.toNat? with
  | some n => .ok n
  | none => .error s!"invalid {flag} value: {value}"

private def parseTail (cfg : Cfg) : List String → Except String Cfg
  | [] => .ok cfg
  | "--output" :: path :: xs => parseTail { cfg with output := some path } xs
  | "--max-nodes" :: n :: xs => do
      let maxNodes ← parseNatFlag "--max-nodes" n
      parseTail { cfg with maxNodes := maxNodes } xs
  | "--fuel-reduce" :: n :: xs => do
      let fuelReduce ← parseNatFlag "--fuel-reduce" n
      parseTail { cfg with fuelReduce := fuelReduce } xs
  | "--fuel-whnf" :: n :: xs => do
      let fuelWhnf ← parseNatFlag "--fuel-whnf" n
      parseTail { cfg with fuelWhnf := fuelWhnf } xs
  | "--fuel-defeq" :: n :: xs => do
      let fuelDefEq ← parseNatFlag "--fuel-defeq" n
      parseTail { cfg with fuelDefEq := fuelDefEq } xs
  | "--help" :: _ => throw usage
  | x :: _ => throw s!"unexpected argument: {x}\n\n{usage}"

private def parseArgs : List String → Except String Cfg
  | "--stage-exprs" :: input :: rest =>
      parseTail { mode := .stageExprs input } rest
  | "--encode-whnf-steps" :: input :: rest =>
      parseTail { mode := .encodeWhnfSteps input } rest
  | "--encode-whnf-calls" :: input :: rest =>
      parseTail { mode := .encodeWhnfCalls input } rest
  | _ => .error usage

private def writeOutput (cfg : Cfg) (payload : Json) : IO Unit := do
  let text := payload.pretty
  match cfg.output with
  | some path =>
      IO.FS.writeFile path (text ++ "\n")
      IO.eprintln s!"[sky_replay] wrote {path}"
  | none =>
      IO.println text

private def parseExprItems (json : Json) : Except String (Array (String × Lean.Expr)) := do
  let rows ←
    match json with
    | .arr xs => pure xs
    | .obj fields =>
        match fields.get? "exprs" with
        | some (.arr xs) => pure xs
        | _ => throw "stage-exprs input must be an array or an object with `exprs`"
    | _ =>
        throw "stage-exprs input must be an array or an object with `exprs`"
  let rec go (index : Nat) (remaining : List Json) (acc : Array (String × Lean.Expr)) :
      Except String (Array (String × Lean.Expr)) := do
    match remaining with
    | [] => pure acc
    | row :: rest =>
        match row.getObj? with
        | .error _ => throw "each stage-exprs row must be a JSON object"
        | .ok fields =>
            let ident :=
              match fields.get? "id" with
              | some (.str s) => s
              | _ => s!"expr-{index}"
            let exprJson? := fields.get? "expr" <|> fields.get? "expr_json"
            let some exprJson := exprJson?
              | throw s!"stage-exprs row `{ident}` is missing `expr`"
            let expr ← HeytingLean.CLI.LeanExprJson.exprFromJson exprJson
            go (index + 1) rest (acc.push (ident, expr))
  go 0 rows.toList #[]

private def lookupObjField (obj : JObject) (key : String) : Option Json :=
  Std.TreeMap.Raw.get? obj key

private def parseNatObjField (obj : JObject) (key : String) : Except String Nat := do
  match lookupObjField obj key with
  | some value =>
      match value.getNat? with
      | .ok n => pure n
      | .error _ => throw s!"field `{key}` is not a Nat"
  | none =>
      throw s!"missing Nat field `{key}`"

private def parseStringObjField (obj : JObject) (key : String) : Except String String := do
  match lookupObjField obj key with
  | some (.str s) => pure s
  | _ => throw s!"missing string field `{key}`"

private def appendStepRow
    (row : Json)
    (acc : Array StepItem) : Except String (Array StepItem) := do
  let fields ←
    match row.getObj? with
    | .ok obj => pure obj
    | .error _ => throw "trace step row must be a JSON object"
  let kind ← parseStringObjField fields "kind"
  if kind != "beta" && kind != "zeta" then
    pure acc
  else
    let declName := (fields.get? "decl_name").bind (fun
      | .str s => some s
      | _ => none) |>.getD "<unknown>"
    let traceRole := (fields.get? "trace_role").bind (fun
      | .str s => some s
      | _ => none) |>.getD "<unknown>"
    let seqId ← parseNatObjField fields "seq_id"
    let some inputJson := fields.get? "input_expr_json"
      | throw "trace step row is missing `input_expr_json`"
    let some outputJson := fields.get? "output_expr_json"
      | throw "trace step row is missing `output_expr_json`"
    let input ← HeytingLean.CLI.LeanExprJson.exprFromJson inputJson
    let output ← HeytingLean.CLI.LeanExprJson.exprFromJson outputJson
    let ident := s!"{declName}:{traceRole}:{seqId}:{kind}"
    pure <| acc.push { ident, declName, traceRole, kind, seqId, input, output }

private def collectStepsFromTraceEntries
    (entries : List Json)
    (acc : Array StepItem) : Except String (Array StepItem) := do
  match entries with
  | [] => pure acc
  | entry :: rest =>
      let entryObj ←
        match entry.getObj? with
        | .ok obj => pure obj
        | .error _ => throw "trace entry must be a JSON object"
      let steps ←
        match entryObj.get? "steps" with
        | some (.arr xs) => pure xs.toList
        | _ => throw "trace entry is missing `steps`"
      let acc' ← steps.foldlM (init := acc) fun inner step => appendStepRow step inner
      collectStepsFromTraceEntries rest acc'

private def parseWhnfStepItems (json : Json) : Except String (Array StepItem) := do
  match json with
  | .arr rows =>
      rows.toList.foldlM (init := #[]) fun acc row => appendStepRow row acc
  | .obj root =>
      match root.get? "declarations" with
      | some (.arr decls) =>
          let rec goDecls (remaining : List Json) (acc : Array StepItem) :
              Except String (Array StepItem) := do
            match remaining with
            | [] => pure acc
            | decl :: rest =>
                let declObj ←
                  match decl.getObj? with
                  | .ok obj => pure obj
                  | .error _ => throw "declaration entry must be a JSON object"
                let traceEntries ←
                  match declObj.get? "trace_entries" with
                  | some (.arr xs) => pure xs.toList
                  | _ => throw "declaration entry is missing `trace_entries`"
                let acc' ← collectStepsFromTraceEntries traceEntries acc
                goDecls rest acc'
          goDecls decls.toList #[]
      | _ =>
          throw "encode-whnf-steps input must be a verified_check trace payload or a flat step array"
  | _ =>
      throw "encode-whnf-steps input must be JSON"

private def appendWhnfCallRow
    (row : Json)
    (acc : Array WhnfCallItem) : Except String (Array WhnfCallItem) := do
  let fields ←
    match row.getObj? with
    | .ok obj => pure obj
    | .error _ => throw "WHNF call row must be a JSON object"
  let projectedBetaZetaSteps := fields.get? "projected_beta_zeta_steps" |>.map (fun j => j.getNat?.toOption.getD 0) |>.getD 0
  if projectedBetaZetaSteps == 0 then
    pure acc
  else
    let declName := (fields.get? "decl_name").bind (fun | .str s => some s | _ => none) |>.getD "<unknown>"
    let traceRole := (fields.get? "trace_role").bind (fun | .str s => some s | _ => none) |>.getD "<unknown>"
    let stepCount := fields.get? "step_count" |>.map (fun j => j.getNat?.toOption.getD 0) |>.getD 0
    let deltaIotaSteps := fields.get? "delta_iota_steps" |>.map (fun j => j.getNat?.toOption.getD 0) |>.getD 0
    let some inputJson := fields.get? "input_expr_json"
      | throw "WHNF call row is missing `input_expr_json`"
    let some outputJson := fields.get? "output_expr_json"
      | throw "WHNF call row is missing `output_expr_json`"
    let input ← HeytingLean.CLI.LeanExprJson.exprFromJson inputJson
    let output ← HeytingLean.CLI.LeanExprJson.exprFromJson outputJson
    let ident := s!"{declName}:{traceRole}:whnf"
    pure <| acc.push {
      ident,
      declName,
      traceRole,
      input,
      output,
      projectedBetaZetaSteps,
      stepCount,
      deltaIotaSteps
    }

private def parseWhnfCallItems (json : Json) : Except String (Array WhnfCallItem) := do
  match json with
  | .obj root =>
      match root.get? "declarations" with
      | some (.arr decls) =>
          let rec goDecls (remaining : List Json) (acc : Array WhnfCallItem) :
              Except String (Array WhnfCallItem) := do
            match remaining with
            | [] => pure acc
            | decl :: rest =>
                let declObj ←
                  match decl.getObj? with
                  | .ok obj => pure obj
                  | .error _ => throw "declaration entry must be a JSON object"
                let traceEntries ←
                  match declObj.get? "trace_entries" with
                  | some (.arr xs) => pure xs.toList
                  | _ => throw "declaration entry is missing `trace_entries`"
                let acc' ← traceEntries.foldlM (init := acc) fun inner entry => appendWhnfCallRow entry inner
                goDecls rest acc'
          goDecls decls.toList #[]
      | _ =>
          throw "encode-whnf-calls input must be a verified_check trace payload"
  | _ =>
      throw "encode-whnf-calls input must be JSON"

private def runStageExprs (cfg : Cfg) (inputPath : FilePath) : IO Json := do
  let inputText ← IO.FS.readFile inputPath
  let inputJson ←
    match Json.parse inputText with
    | Except.ok j => pure j
    | Except.error err => throw <| IO.userError s!"failed to parse stage-exprs input: {err}"
  let exprs ←
    match parseExprItems inputJson with
    | .ok rows => pure rows
    | .error err => throw <| IO.userError err
  let mut items : Array Json := #[]
  let mut successCount := 0
  for (ident, expr) in exprs do
    match SKYStageCore.stageExprWithState {} expr with
    | .error err =>
        items := items.push <| Json.mkObj
              [ ("id", Json.str ident)
              , ("eligible", Json.bool false)
              , ("skip_reason", Json.str err)
              ]
    | .ok (staged, _) =>
        match
          HeytingLean.LoF.LeanKernel.Lean4LeanSKY.Enc.compileExprNatUnit? staged,
          HeytingLean.LoF.Combinators.SKYMachineBounded.State.compileComb?
            (OracleRef := SKYStageCore.OracleRef) cfg.maxNodes
        with
        | some term, compileState =>
            match compileState term with
            | some state =>
                successCount := successCount + 1
                items := items.push <| Json.mkObj
                  [ ("id", Json.str ident)
                  , ("eligible", Json.bool true)
                  , ("node_count", toJson state.nodes.size)
                  , ("machine_json", SKYStageCore.stateToJson cfg.maxNodes cfg.fuelReduce state)
                  ]
            | none =>
                items := items.push <| Json.mkObj
                  [ ("id", Json.str ident)
                  , ("eligible", Json.bool false)
                  , ("skip_reason", Json.str s!"out of heap during staged Expr compilation (maxNodes={cfg.maxNodes})")
                  ]
        | _, _ =>
            items := items.push <| Json.mkObj
              [ ("id", Json.str ident)
              , ("eligible", Json.bool false)
              , ("skip_reason", Json.str "failed to encode the staged Expr as a SKY combinator")
              ]
  pure <| Json.mkObj
    [ ("tool", Json.str "sky_replay")
    , ("mode", Json.str "stage_exprs")
    , ("input_count", toJson exprs.size)
    , ("success_count", toJson successCount)
    , ("max_nodes", toJson cfg.maxNodes)
    , ("fuel_reduce", toJson cfg.fuelReduce)
    , ("items", Json.arr items)
    ]

private def runEncodeWhnfSteps (cfg : Cfg) (inputPath : FilePath) : IO Json := do
  let inputText ← IO.FS.readFile inputPath
  let inputJson ←
    match Json.parse inputText with
    | Except.ok j => pure j
    | Except.error err => throw <| IO.userError s!"failed to parse trace input: {err}"
  let steps ←
    match parseWhnfStepItems inputJson with
    | .ok rows => pure rows
    | .error err => throw <| IO.userError err
  let traceCfg : HeytingLean.CLI.WHNFTrace.TraceCfg :=
    { fuelWhnf := cfg.fuelWhnf
      fuelDefEq := cfg.fuelDefEq
      fuelReduce := cfg.fuelReduce
      maxNodes := cfg.maxNodes
      grain := .step
    }
  let mut items : Array Json := #[]
  let mut successCount := 0
  for step in steps do
    let verifyResult ← HeytingLean.CLI.WHNFTrace.buildStepVerificationJson traceCfg step.input step.output
    match verifyResult with
    | .error err =>
        items := items.push <| Json.mkObj
          [ ("id", Json.str step.ident)
          , ("decl_name", Json.str step.declName)
          , ("trace_role", Json.str step.traceRole)
          , ("kind", Json.str step.kind)
          , ("seq_id", toJson step.seqId)
          , ("gpu_verifiable", Json.bool false)
          , ("eligible", Json.bool false)
          , ("skip_reason", Json.str err)
          ]
    | .ok verifyJson =>
        successCount := successCount + 1
        match verifyJson.getObj? with
        | .ok verifyFields =>
            items := items.push <| Json.mkObj <|
              [ ("id", Json.str step.ident)
              , ("decl_name", Json.str step.declName)
              , ("trace_role", Json.str step.traceRole)
              , ("kind", Json.str step.kind)
              , ("seq_id", toJson step.seqId)
              , ("gpu_verifiable", Json.bool true)
              ] ++ verifyFields.toList
        | .error _ =>
            items := items.push <| Json.mkObj
              [ ("id", Json.str step.ident)
              , ("decl_name", Json.str step.declName)
              , ("trace_role", Json.str step.traceRole)
              , ("kind", Json.str step.kind)
              , ("seq_id", toJson step.seqId)
              , ("gpu_verifiable", Json.bool false)
              , ("eligible", Json.bool false)
              , ("skip_reason", Json.str "internal verifier JSON was not an object")
              ]
  pure <| Json.mkObj
    [ ("tool", Json.str "sky_replay")
    , ("mode", Json.str "encode_whnf_steps")
    , ("input_count", toJson steps.size)
    , ("success_count", toJson successCount)
    , ("max_nodes", toJson cfg.maxNodes)
    , ("fuel_reduce", toJson cfg.fuelReduce)
    , ("fuel_defeq", toJson cfg.fuelDefEq)
    , ("items", Json.arr items)
    ]

private def runEncodeWhnfCalls (cfg : Cfg) (inputPath : FilePath) : IO Json := do
  let inputText ← IO.FS.readFile inputPath
  let inputJson ←
    match Json.parse inputText with
    | Except.ok j => pure j
    | Except.error err => throw <| IO.userError s!"failed to parse WHNF-call trace input: {err}"
  let calls ←
    match parseWhnfCallItems inputJson with
    | .ok rows => pure rows
    | .error err => throw <| IO.userError err
  let traceCfg : HeytingLean.CLI.WHNFTrace.TraceCfg :=
    { fuelWhnf := cfg.fuelWhnf
      fuelDefEq := cfg.fuelDefEq
      fuelReduce := cfg.fuelReduce
      maxNodes := cfg.maxNodes
      grain := .whnf
    }
  let mut items : Array Json := #[]
  let mut successCount := 0
  for call in calls do
    let verifyResult ← HeytingLean.CLI.WHNFTrace.buildWhnfVerificationJson traceCfg call.input call.output
    match verifyResult with
    | .error err =>
        items := items.push <| Json.mkObj
          [ ("id", Json.str call.ident)
          , ("decl_name", Json.str call.declName)
          , ("trace_role", Json.str call.traceRole)
          , ("kind", Json.str "whnf_call")
          , ("gpu_verifiable", Json.bool false)
          , ("eligible", Json.bool false)
          , ("projected_beta_zeta_steps", toJson call.projectedBetaZetaSteps)
          , ("step_count", toJson call.stepCount)
          , ("delta_iota_steps", toJson call.deltaIotaSteps)
          , ("skip_reason", Json.str err)
          ]
    | .ok verifyJson =>
        successCount := successCount + 1
        match verifyJson.getObj? with
        | .ok verifyFields =>
            items := items.push <| Json.mkObj <|
              [ ("id", Json.str call.ident)
              , ("decl_name", Json.str call.declName)
              , ("trace_role", Json.str call.traceRole)
              , ("kind", Json.str "whnf_call")
              , ("gpu_verifiable", Json.bool true)
              , ("projected_beta_zeta_steps", toJson call.projectedBetaZetaSteps)
              , ("step_count", toJson call.stepCount)
              , ("delta_iota_steps", toJson call.deltaIotaSteps)
              ] ++ verifyFields.toList
        | .error _ =>
            items := items.push <| Json.mkObj
              [ ("id", Json.str call.ident)
              , ("decl_name", Json.str call.declName)
              , ("trace_role", Json.str call.traceRole)
              , ("kind", Json.str "whnf_call")
              , ("gpu_verifiable", Json.bool false)
              , ("eligible", Json.bool false)
              , ("projected_beta_zeta_steps", toJson call.projectedBetaZetaSteps)
              , ("step_count", toJson call.stepCount)
              , ("delta_iota_steps", toJson call.deltaIotaSteps)
              , ("skip_reason", Json.str "internal verifier JSON was not an object")
              ]
  pure <| Json.mkObj
    [ ("tool", Json.str "sky_replay")
    , ("mode", Json.str "encode_whnf_calls")
    , ("input_count", toJson calls.size)
    , ("success_count", toJson successCount)
    , ("max_nodes", toJson cfg.maxNodes)
    , ("fuel_whnf", toJson cfg.fuelWhnf)
    , ("fuel_reduce", toJson cfg.fuelReduce)
    , ("fuel_defeq", toJson cfg.fuelDefEq)
    , ("items", Json.arr items)
    ]

def main (argv : List String) : IO UInt32 := do
  match parseArgs argv with
  | .error err =>
      IO.eprintln err
      pure 1
  | .ok cfg => do
      try
        let payload ←
          match cfg.mode with
          | .stageExprs input => runStageExprs cfg input
          | .encodeWhnfSteps input => runEncodeWhnfSteps cfg input
          | .encodeWhnfCalls input => runEncodeWhnfCalls cfg input
        writeOutput cfg payload
        pure 0
      catch ex =>
        IO.eprintln s!"[sky_replay] FAILED: {ex}"
        pure 1

end HeytingLean.CLI.SKYReplay

open HeytingLean.CLI.SKYReplay in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.SKYReplay.main args
