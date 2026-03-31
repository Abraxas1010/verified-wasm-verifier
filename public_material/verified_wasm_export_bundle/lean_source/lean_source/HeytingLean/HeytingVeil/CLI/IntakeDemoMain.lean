/-
Copyright (c) 2026 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

import HeytingLean.HeytingVeil.Intake.Examples.TicketToEnvelopeDemo
import HeytingLean.HeytingVeil.Intake

/-!
# CLI for HeytingVeil intake demo surfaces.

Usage:
  -- Command `manifest`: emits route + emission plan manifest.
  -- Command `add1`, `add2`, `add1-highirc`, `add2-highirc`: emit envelopes.
  -- Command `plan-add1`, `plan-add2`, `plan-add1-highirc`, `plan-add2-highirc`: emit plan strings.
  -- Command `minicc-route`: emit miniCCore route label.
  -- Command `ticket-import`: validates a ticket-like payload schema for future import workflows.
  -- Flags: `--n` (Nat), `--x` (Nat), `--y` (Nat), `--help`.
-/
namespace HeytingLean
namespace HeytingVeil
namespace CLI

open HeytingLean.HeytingVeil.Intake
open HeytingLean.HeytingVeil.Intake.Examples

private def parseNat? (s : String) : Option Nat :=
  s.toNat?

private inductive Command where
  | manifest
  | runAdd1
  | runAdd2
  | runAdd1High
  | runAdd2High
  | planAdd1
  | planAdd2
  | planAdd1High
  | planAdd2High
  | miniCCoreRoute
  | ticketImport
  | ticketToArtifact
  deriving BEq

private def parseCommand : String → Option Command
  | "manifest" => some Command.manifest
  | "add1" => some Command.runAdd1
  | "add2" => some Command.runAdd2
  | "add1-highirc" => some Command.runAdd1High
  | "add2-highirc" => some Command.runAdd2High
  | "plan-add1" => some Command.planAdd1
  | "plan-add2" => some Command.planAdd2
  | "plan-add1-highirc" => some Command.planAdd1High
  | "plan-add2-highirc" => some Command.planAdd2High
  | "minicc-route" => some Command.miniCCoreRoute
  | "ticket-import" => some Command.ticketImport
  | "ticket-to-artifact" => some Command.ticketToArtifact
  | _ => none

private structure CliArgs where
  command : Command
  n : Option Nat := none
  x : Option Nat := none
  y : Option Nat := none
  payload : Option String := none
  seenN : Bool := false
  seenX : Bool := false
  seenY : Bool := false
  seenPayload : Bool := false

private def usage : String :=
  String.intercalate "\n"
    [ "heytingveil_intake_cli <command> [options]"
    , "Commands:"
    , "  manifest --n <n> --x <x> --y <y>          emit operator manifest"
    , "  add1 --n <n>                               emit add1 envelope"
    , "  add2 --x <x> --y <y>                       emit add2 envelope"
    , "  add1-highirc --n <n>                        emit add1 highIRC envelope"
    , "  add2-highirc --x <x> --y <y>                emit add2 highIRC envelope"
    , "  plan-add1 --n <n>                          emit add1 file plan"
    , "  plan-add2 --x <x> --y <y>                  emit add2 stdout plan"
    , "  plan-add1-highirc --n <n>                   emit add1 highIRC plan"
    , "  plan-add2-highirc --x <x> --y <y>           emit add2 highIRC plan"
    , "  minicc-route                                emit miniCCore route label"
    , "  ticket-import --payload <payload>             validate + promote intake payload to ticket draft"
    , "  ticket-to-artifact --payload <payload> [--n <n> | --x <x> --y <y>]"
    , "                                            emit route-mapped artifact from ticket payload"
  , "Shared flags: --n <Nat>, --x <Nat>, --y <Nat>, --help"
  ]

private def expectModeArg (s : String) : String :=
  s!"--{s} requires a Nat argument"

private def parseArgs : List String → Except String CliArgs
  | [] => throw "missing command (run --help for usage)"
  | "--help" :: _ => throw "help"
  | head :: rest =>
    match parseCommand head with
    | none => throw s!"unknown command: {head}"
    | some command =>
      let rec loop (acc : CliArgs) : List String → Except String CliArgs
        | [] => return acc
        | "--" :: tail => loop acc tail
        | "--n" :: [] => throw (expectModeArg "n")
        | "--x" :: [] => throw (expectModeArg "x")
        | "--y" :: [] => throw (expectModeArg "y")
        | "--n" :: val :: tail =>
          if acc.seenN then
            throw "duplicate flag --n"
          else
          match parseNat? val with
          | none => throw s!"invalid Nat for --n: {val}"
          | some n => loop { acc with n := some n, seenN := true } tail
        | "--x" :: val :: tail =>
          if acc.seenX then
            throw "duplicate flag --x"
          else
          match parseNat? val with
          | none => throw s!"invalid Nat for --x: {val}"
          | some x => loop { acc with x := some x, seenX := true } tail
        | "--y" :: val :: tail =>
          if acc.seenY then
            throw "duplicate flag --y"
          else
          match parseNat? val with
          | none => throw s!"invalid Nat for --y: {val}"
          | some y => loop { acc with y := some y, seenY := true } tail
        | "--payload" :: [] => throw "payload requires a value"
        | "--payload" :: val :: tail =>
          if acc.seenPayload then
            throw "duplicate flag --payload"
          else
            loop { acc with payload := some val, seenPayload := true } tail
        | "--help" :: _ => throw "help"
        | bad :: _ => throw s!"unknown arg: {bad}"
    loop { command := command } rest

private def requirePayload : Option String → Except String String
  | some payload => .ok payload
  | none => throw "missing required flag --payload"

private def requireNat (label : String) : Option Nat → Except String Nat
  | some n => .ok n
  | none => throw s!"missing required flag --{label}"

private def rejectIfSeen (command : String) (flag : String) (seen : Bool) : Except String Unit :=
  if seen then throw s!"command {command} does not accept {flag}" else .ok ()

private structure TicketPayload where
  title : String
  prompt : String
  desiredProperty : String
  irClass : Routing.IRClass
  provenance : String
  preferredBackend? : Option Routing.BackendClass

private def irClassFromString (s : String) : Option Routing.IRClass :=
  match s with
  | "nat" => some Routing.IRClass.lambdaNat
  | "nat2" => some Routing.IRClass.lambdaNat2
  | "minicc" => some Routing.IRClass.miniCCore
  | "generic" => some Routing.IRClass.generic
  | _ => none

private def backendFromString (s : String) : Option Routing.BackendClass :=
  match s with
  | "c" => some Routing.BackendClass.c
  | "wasm" => some Routing.BackendClass.wasmMini
  | "highirc" => some Routing.BackendClass.highIRC
  | "python" => some Routing.BackendClass.pythonFFI
  | "solidity" => some Routing.BackendClass.solidity
  | _ => none

private def irClassName : Routing.IRClass → String
  | .lambdaNat => "nat"
  | .lambdaNat2 => "nat2"
  | .miniCCore => "minicc"
  | .generic => "generic"

private def backendName : Routing.BackendClass → String
  | .c => "c"
  | .wasmMini => "wasm"
  | .highIRC => "highirc"
  | .pythonFFI => "python"
  | .solidity => "solidity"

private def splitEscapedPipeFields (s : String) : Except String (List String) := do
  let chars := s.toList
  let rec loop
    (rest : List Char)
    (acc : List (List Char))
    (cur : List Char)
    (inQuote : Bool)
    (escaped : Bool) : Except String (List String) :=
    match rest with
    | [] =>
      if escaped then
        throw "malformed payload schema: trailing escape sequence"
      else if inQuote then
        throw "malformed payload schema: unclosed quote"
      else
        let fields := (cur :: acc).reverse
        return fields.map (fun chars => String.mk chars.reverse)
    | c :: tail =>
      if escaped then
        loop tail acc (c :: cur) inQuote false
      else if c = '\\' then
        loop tail acc cur inQuote true
      else if c = '"' then
        loop tail acc cur (!inQuote) false
      else if c = '|' && !inQuote then
        loop tail (cur :: acc) [] false false
      else
        loop tail acc (c :: cur) inQuote false
  let fields ← loop chars [] [] false false
  return fields

private def parseTicketPayload (s : String) : Except String TicketPayload := do
  let fields ← splitEscapedPipeFields (s.trim)
  let (title, prompt, desired, irRaw, provenance, backendOptRaw) ←
    match fields with
    | [title, prompt, desired, ir, provenance] =>
      pure (title.trim, prompt.trim, desired.trim, ir.trim, provenance.trim, none)
    | [title, prompt, desired, ir, provenance, backend] =>
      let backendTrim := backend.trim
      let backendOpt : Option String :=
        if backendTrim.isEmpty then
          none
        else
          some backendTrim
      pure (title.trim, prompt.trim, desired.trim, ir.trim, provenance.trim, backendOpt)
    | _ =>
      throw "malformed payload schema: expected title|prompt|desiredProperty|ir|provenance(|backend)"
  if title.isEmpty then
    throw "malformed payload schema: title is required"
  let irNorm := irRaw.toLower
  let irClass ←
    match irClassFromString irNorm with
    | some c => pure c
    | none => throw s!"unsupported ir class: {irRaw}"
  let backendNorm :=
    backendOptRaw.map String.toLower
  let preferredBackend? ←
    match backendOptRaw with
    | none => pure none
    | some backendRaw =>
      match backendFromString (backendNorm.getD "") with
      | some b => pure (some b)
      | none => throw s!"unsupported backend: {backendRaw}"
  let parsed : TicketPayload :=
    { title := title
    , prompt := prompt
    , desiredProperty := desired
    , irClass := irClass
    , provenance := provenance
    , preferredBackend? := preferredBackend? }
  return parsed

private def jsonEscape (s : String) : String :=
  s.foldl
    (fun acc ch =>
      match ch with
      | '"' => acc ++ "\\\""
      | '\\' => acc ++ "\\\\"
      | '\n' => acc ++ "\\n"
      | '\r' => acc ++ "\\r"
      | '\t' => acc ++ "\\t"
      | c => acc ++ String.mk [c])
    ""

private def ticketImportResult (parsed : TicketPayload) (route : Routing.Route) : String :=
  let intent : SpecIntent :=
    {
      title := parsed.title
      userPrompt := parsed.prompt
      desiredProperty := parsed.desiredProperty
      provenanceRef := some parsed.provenance
    }
  let intakeState := Intake.start intent
  let intakeStateWithPolicy := Policy.applyBaselinePolicy intakeState
  let policyReady : Bool := Policy.baselinePolicyReady intakeStateWithPolicy
  let blockersText : String :=
    "[" ++ String.intercalate "," (Policy.baselineBlockers intakeStateWithPolicy
      |>.map (fun blocker => "\"" ++ Policy.blockerTag blocker ++ "\"")) ++ "]"
  let normalizedSpec :=
    "prompt: " ++ parsed.prompt ++ " | desired: " ++ parsed.desiredProperty ++
      " | provenance: " ++ parsed.provenance
  let normalizedSpecEscaped := jsonEscape normalizedSpec
  let maybeTicket :=
    if policyReady then
      some <|
        Intake.toTicket intakeStateWithPolicy
          normalizedSpec parsed.irClass parsed.preferredBackend?
    else
      none
  let resolvedRoute :=
    match maybeTicket with
    | some ticket => Intake.selectRouteForTicket ticket
    | none => route
  let continuationForRoute (resolvedRoute : Routing.Route) : String :=
    let routeLabelText := jsonEscape (Routing.routeLabel resolvedRoute)
    match resolvedRoute.ir, resolvedRoute.backend with
    | .lambdaNat, .c =>
      "{"
        ++ "\"status\":\"ready\","
        ++ "\"lane\":\"nat-add1\","
        ++ "\"route\":\"" ++ routeLabelText ++ "\","
        ++ "\"commandTemplate\":\"add1 --n <n>\","
        ++ "\"planTemplate\":\"plan-add1 --n <n>\","
        ++ "\"note\":\"emit lane available: add1 demo + plan generation\""
        ++ "}"
    | .lambdaNat, .highIRC =>
      "{"
        ++ "\"status\":\"ready\","
        ++ "\"lane\":\"nat-add1-highirc\","
        ++ "\"route\":\"" ++ routeLabelText ++ "\","
        ++ "\"commandTemplate\":\"add1-highirc --n <n>\","
        ++ "\"planTemplate\":\"plan-add1-highirc --n <n>\","
        ++ "\"note\":\"route-aware highIRC lane available\""
        ++ "}"
    | .lambdaNat, .wasmMini =>
      "{"
        ++ "\"status\":\"ready\","
        ++ "\"lane\":\"nat-add1-wasm\","
        ++ "\"route\":\"" ++ routeLabelText ++ "\","
        ++ "\"commandTemplate\":\"ticket-to-artifact --payload <payload> --n <n>\","
        ++ "\"planTemplate\":\"(artifact-only)\","
        ++ "\"note\":\"wasm backend accepted; emit artifact from ticket-to-artifact using --n.\""
        ++ "}"
    | .lambdaNat, .pythonFFI =>
      "{" 
        ++ "\"status\":\"ready\"," 
        ++ "\"lane\":\"nat-add1-python\"," 
        ++ "\"route\":\"" ++ routeLabelText ++ "\"," 
        ++ "\"commandTemplate\":\"ticket-to-artifact --payload <payload> --n <n>\"," 
        ++ "\"planTemplate\":\"(artifact-only)\"," 
        ++ "\"note\":\"python backend accepted by schema; emit artifact from ticket-to-artifact using --n.\""
        ++ "}"
    | .lambdaNat, .solidity =>
      "{"
        ++ "\"status\":\"ready\","
        ++ "\"lane\":\"nat-add1-solidity\","
        ++ "\"route\":\"" ++ routeLabelText ++ "\","
        ++ "\"commandTemplate\":\"ticket-to-artifact --payload <payload> --n <n>\","
        ++ "\"planTemplate\":\"(artifact-only)\","
        ++ "\"note\":\"solidity backend accepted with fail-closed shape checks; emit contract envelope from ticket-to-artifact using --n.\""
        ++ "}"
    | .lambdaNat2, .c =>
      "{"
        ++ "\"status\":\"ready\","
        ++ "\"lane\":\"nat2-add2\","
        ++ "\"route\":\"" ++ routeLabelText ++ "\","
        ++ "\"commandTemplate\":\"add2 --x <x> --y <y>\","
        ++ "\"planTemplate\":\"plan-add2 --x <x> --y <y>\","
        ++ "\"note\":\"emit lane available: add2 demo + plan generation\""
        ++ "}"
    | .lambdaNat2, .highIRC =>
      "{"
        ++ "\"status\":\"ready\","
        ++ "\"lane\":\"nat2-add2-highirc\","
        ++ "\"route\":\"" ++ routeLabelText ++ "\","
        ++ "\"commandTemplate\":\"add2-highirc --x <x> --y <y>\","
        ++ "\"planTemplate\":\"plan-add2-highirc --x <x> --y <y>\","
        ++ "\"note\":\"route-aware highIRC lane available\""
        ++ "}"
    | .lambdaNat2, .wasmMini =>
      "{"
        ++ "\"status\":\"ready\","
        ++ "\"lane\":\"nat2-add2-wasm\","
        ++ "\"route\":\"" ++ routeLabelText ++ "\","
        ++ "\"commandTemplate\":\"ticket-to-artifact --payload <payload> --x <x> --y <y>\","
        ++ "\"planTemplate\":\"(artifact-only)\","
        ++ "\"note\":\"wasm backend accepted; emit artifact from ticket-to-artifact using --x/--y.\""
        ++ "}"
    | .lambdaNat2, .pythonFFI =>
      "{" 
        ++ "\"status\":\"ready\"," 
        ++ "\"lane\":\"nat2-add2-python\"," 
        ++ "\"route\":\"" ++ routeLabelText ++ "\"," 
        ++ "\"commandTemplate\":\"ticket-to-artifact --payload <payload> --x <x> --y <y>\"," 
        ++ "\"planTemplate\":\"(artifact-only)\"," 
        ++ "\"note\":\"python backend accepted by schema; emit artifact from ticket-to-artifact using --x/--y.\""
        ++ "}"
    | .lambdaNat2, .solidity =>
      "{"
        ++ "\"status\":\"ready\","
        ++ "\"lane\":\"nat2-add2-solidity\","
        ++ "\"route\":\"" ++ routeLabelText ++ "\","
        ++ "\"commandTemplate\":\"ticket-to-artifact --payload <payload> --x <x> --y <y>\","
        ++ "\"planTemplate\":\"(artifact-only)\","
        ++ "\"note\":\"solidity backend accepted with fail-closed shape checks; emit contract envelope from ticket-to-artifact using --x/--y.\""
        ++ "}"
    | .miniCCore, _ =>
      "{"
        ++ "\"status\":\"route_only\","
        ++ "\"lane\":\"minicc\","
        ++ "\"route\":\"" ++ routeLabelText ++ "\","
        ++ "\"commandTemplate\":\"ticket-to-artifact --payload <payload>\","
        ++ "\"planTemplate\":\"(artifact-only)\","
        ++ "\"note\":\"miniCCore route validated; emit artifact from ticket-to-artifact.\""
        ++ "}"
    | .generic, _ =>
      "{"
        ++ "\"status\":\"route_only\","
        ++ "\"lane\":\"generic\","
        ++ "\"route\":\"" ++ routeLabelText ++ "\","
        ++ "\"commandTemplate\":\"(not implemented)\","
        ++ "\"planTemplate\":\"(not implemented)\","
        ++ "\"note\":\"generic bridge is next workstream continuation target.\""
        ++ "}"
  let statusText := if policyReady then "ready_for_ticket" else "intake_checks_not_ready"
  let ticketText : String :=
    match maybeTicket with
    | some ticket =>
      let preferredBackendText :=
        match ticket.preferredBackend? with
        | none => "null"
        | some b => "\"" ++ jsonEscape (backendName b) ++ "\""
      "{"
        ++ "\"title\":\"" ++ jsonEscape ticket.intent.title ++ "\","
        ++ "\"status\":\"ready\","
        ++ "\"normalizedSpec\":\"" ++ normalizedSpecEscaped ++ "\","
        ++ "\"desiredProperty\":\"" ++ jsonEscape ticket.intent.desiredProperty ++ "\","
        ++ "\"provenance\":\"" ++ jsonEscape parsed.provenance ++ "\","
        ++ "\"ir\":\"" ++ irClassName parsed.irClass ++ "\","
        ++ "\"preferredBackend\":" ++ preferredBackendText ++ ","
        ++ "\"resolvedBackend\":\"" ++ backendName resolvedRoute.backend ++ "\","
        ++ "\"route\":\"" ++ Routing.routeLabel resolvedRoute ++ "\"}"
    | none => "null"
  let continuationText : String :=
    match maybeTicket with
    | some _ => continuationForRoute resolvedRoute
    | none => "null"
  let preferredBackendText :=
    match parsed.preferredBackend? with
    | none => "null"
    | some b => "\"" ++ jsonEscape (backendName b) ++ "\""
  "ticket-import-result {" ++
    "\"status\":\"" ++ statusText ++ "\"," ++
    "\"policyScore\":" ++ toString (Policy.baselinePolicyScore intakeStateWithPolicy) ++ "," ++
    "\"policyMaxScore\":" ++ toString Policy.baselinePolicyMaxScore ++ "," ++
    "\"blockers\":" ++ blockersText ++ "," ++
    "\"ticket\":" ++ ticketText ++ "," ++
    "\"artifactContinuation\":" ++ continuationText ++ "," ++
    "\"title\":\"" ++ jsonEscape parsed.title ++ "\"," ++
    "\"prompt\":\"" ++ jsonEscape parsed.prompt ++ "\"," ++
    "\"desiredProperty\":\"" ++ jsonEscape parsed.desiredProperty ++ "\"," ++
    "\"provenance\":\"" ++ jsonEscape parsed.provenance ++ "\"," ++
    "\"ir\":\"" ++ irClassName parsed.irClass ++ "\"," ++
    "\"preferredBackend\":" ++ preferredBackendText ++ "," ++
  "\"resolvedBackend\":\"" ++ backendName resolvedRoute.backend ++ "\"," ++
  "\"route\":\"" ++ Routing.routeLabel resolvedRoute ++ "\"}"

private def blockersText (intakeStateWithPolicy : IntakeState) : String :=
  "[" ++ String.intercalate "," (Policy.baselineBlockers intakeStateWithPolicy
    |>.map (fun blocker => "\"" ++ Policy.blockerTag blocker ++ "\"")) ++ "]"

private def enforceArtifactArgShape (route : Routing.Route) (args : CliArgs) : Except String Unit := do
  match route.ir, route.backend with
  | .lambdaNat, .c =>
    rejectIfSeen "ticket-to-artifact" "--x" args.seenX
    rejectIfSeen "ticket-to-artifact" "--y" args.seenY
  | .lambdaNat, .highIRC =>
    rejectIfSeen "ticket-to-artifact" "--x" args.seenX
    rejectIfSeen "ticket-to-artifact" "--y" args.seenY
  | .lambdaNat, .wasmMini =>
    rejectIfSeen "ticket-to-artifact" "--x" args.seenX
    rejectIfSeen "ticket-to-artifact" "--y" args.seenY
  | .lambdaNat, .pythonFFI =>
    rejectIfSeen "ticket-to-artifact" "--x" args.seenX
    rejectIfSeen "ticket-to-artifact" "--y" args.seenY
  | .lambdaNat, .solidity =>
    rejectIfSeen "ticket-to-artifact" "--x" args.seenX
    rejectIfSeen "ticket-to-artifact" "--y" args.seenY
  | .lambdaNat2, .c =>
    rejectIfSeen "ticket-to-artifact" "--n" args.seenN
  | .lambdaNat2, .highIRC =>
    rejectIfSeen "ticket-to-artifact" "--n" args.seenN
  | .lambdaNat2, .wasmMini =>
    rejectIfSeen "ticket-to-artifact" "--n" args.seenN
  | .lambdaNat2, .pythonFFI =>
    rejectIfSeen "ticket-to-artifact" "--n" args.seenN
  | .lambdaNat2, .solidity =>
    rejectIfSeen "ticket-to-artifact" "--n" args.seenN
  | .miniCCore, _ =>
    rejectIfSeen "ticket-to-artifact" "--n" args.seenN
    rejectIfSeen "ticket-to-artifact" "--x" args.seenX
    rejectIfSeen "ticket-to-artifact" "--y" args.seenY
  | .generic, _ =>
    rejectIfSeen "ticket-to-artifact" "--n" args.seenN
    rejectIfSeen "ticket-to-artifact" "--x" args.seenX
    rejectIfSeen "ticket-to-artifact" "--y" args.seenY

private def ticketToArtifactResult (parsed : TicketPayload) (args : CliArgs) : Except String String := do
  let intent : SpecIntent :=
    {
      title := parsed.title
      userPrompt := parsed.prompt
      desiredProperty := parsed.desiredProperty
      provenanceRef := some parsed.provenance
    }
  let intakeState := Intake.start intent
  let intakeStateWithPolicy := Policy.applyBaselinePolicy intakeState
  if !Policy.baselinePolicyReady intakeStateWithPolicy then
    throw <| "ticket-not-ready-for-emission: blockers=" ++ blockersText intakeStateWithPolicy
  let ticket : FormalizationTicket :=
    Intake.toTicket intakeStateWithPolicy
      ("prompt: " ++ parsed.prompt ++ " | desired: " ++ parsed.desiredProperty ++
        " | provenance: " ++ parsed.provenance)
      parsed.irClass parsed.preferredBackend?
  let route := Intake.selectRouteForTicket ticket
  let _ ← enforceArtifactArgShape route args
  match route.ir, route.backend with
  | .lambdaNat, .c =>
    let n := ← requireNat "n" args.n
    return runDemoWithBackendAndJob n Routing.BackendClass.c
  | .lambdaNat, .highIRC =>
    let n := ← requireNat "n" args.n
    return runDemoWithBackendAndJob n Routing.BackendClass.highIRC
  | .lambdaNat, .wasmMini =>
    let n := ← requireNat "n" args.n
    return runDemoWithBackendAndJob n Routing.BackendClass.wasmMini
  | .lambdaNat, .pythonFFI =>
    let n := ← requireNat "n" args.n
    return runDemoWithBackendAndJob n Routing.BackendClass.pythonFFI
  | .lambdaNat, .solidity =>
    let n := ← requireNat "n" args.n
    if !add1SolidityEmissionReady n then
      throw "unsupported_solidity_shape: add1 route is not in supported Solidity lowering subset"
    return runDemoWithBackendAndJob n Routing.BackendClass.solidity
  | .lambdaNat2, .c =>
    let x := ← requireNat "x" args.x
    let y := ← requireNat "y" args.y
    return runDemo2WithBackendAndJob x y Routing.BackendClass.c
  | .lambdaNat2, .highIRC =>
    let x := ← requireNat "x" args.x
    let y := ← requireNat "y" args.y
    return runDemo2WithBackendAndJob x y Routing.BackendClass.highIRC
  | .lambdaNat2, .wasmMini =>
    let x := ← requireNat "x" args.x
    let y := ← requireNat "y" args.y
    return runDemo2WithBackendAndJob x y Routing.BackendClass.wasmMini
  | .lambdaNat2, .pythonFFI =>
    let x := ← requireNat "x" args.x
    let y := ← requireNat "y" args.y
    return runDemo2WithBackendAndJob x y Routing.BackendClass.pythonFFI
  | .lambdaNat2, .solidity =>
    let x := ← requireNat "x" args.x
    let y := ← requireNat "y" args.y
    if !add2SolidityEmissionReady x y then
      throw "unsupported_solidity_shape: add2 route is not in supported Solidity lowering subset"
    return runDemo2WithBackendAndJob x y Routing.BackendClass.solidity
  | .miniCCore, _ =>
    return runDemo3WithBackendAndJob route.backend
  | .generic, _ =>
    throw "generic route not yet supported in ticket-to-artifact"

private def commandOutput (args : CliArgs) : Except String String :=
  match args.command with
  | Command.manifest => do
    rejectIfSeen "manifest" "--payload" args.seenPayload
    let n := ← requireNat "n" args.n
    let x := ← requireNat "x" args.x
    let y := ← requireNat "y" args.y
    return runDemoPlanManifest n x y
  | Command.runAdd1 => do
    rejectIfSeen "add1" "--payload" args.seenPayload
    rejectIfSeen "add1" "--x" args.seenX
    rejectIfSeen "add1" "--y" args.seenY
    let n := ← requireNat "n" args.n
    return runDemo n
  | Command.runAdd2 => do
    rejectIfSeen "add2" "--payload" args.seenPayload
    rejectIfSeen "add2" "--n" args.seenN
    let x := ← requireNat "x" args.x
    let y := ← requireNat "y" args.y
    return runDemo2 x y
  | Command.runAdd1High => do
    rejectIfSeen "add1-highirc" "--payload" args.seenPayload
    rejectIfSeen "add1-highirc" "--x" args.seenX
    rejectIfSeen "add1-highirc" "--y" args.seenY
    let n := ← requireNat "n" args.n
    return runDemo4 n
  | Command.runAdd2High => do
    rejectIfSeen "add2-highirc" "--payload" args.seenPayload
    rejectIfSeen "add2-highirc" "--n" args.seenN
    let x := ← requireNat "x" args.x
    let y := ← requireNat "y" args.y
    return runDemo5 x y
  | Command.planAdd1 => do
    rejectIfSeen "plan-add1" "--payload" args.seenPayload
    rejectIfSeen "plan-add1" "--x" args.seenX
    rejectIfSeen "plan-add1" "--y" args.seenY
    let n := ← requireNat "n" args.n
    return runDemo1Plan n
  | Command.planAdd2 => do
    rejectIfSeen "plan-add2" "--payload" args.seenPayload
    rejectIfSeen "plan-add2" "--n" args.seenN
    let x := ← requireNat "x" args.x
    let y := ← requireNat "y" args.y
    return runDemo2Plan x y
  | Command.planAdd1High => do
    rejectIfSeen "plan-add1-highirc" "--payload" args.seenPayload
    rejectIfSeen "plan-add1-highirc" "--x" args.seenX
    rejectIfSeen "plan-add1-highirc" "--y" args.seenY
    let n := ← requireNat "n" args.n
    return runDemo4Plan n
  | Command.planAdd2High => do
    rejectIfSeen "plan-add2-highirc" "--payload" args.seenPayload
    rejectIfSeen "plan-add2-highirc" "--n" args.seenN
    let x := ← requireNat "x" args.x
    let y := ← requireNat "y" args.y
    return runDemo5Plan x y
  | Command.miniCCoreRoute => do
    rejectIfSeen "minicc-route" "--payload" args.seenPayload
    rejectIfSeen "minicc-route" "--n" args.seenN
    rejectIfSeen "minicc-route" "--x" args.seenX
    rejectIfSeen "minicc-route" "--y" args.seenY
    return runDemo3
  | Command.ticketImport => do
    rejectIfSeen "ticket-import" "--n" args.seenN
    rejectIfSeen "ticket-import" "--x" args.seenX
    rejectIfSeen "ticket-import" "--y" args.seenY
    let payload := ← requirePayload args.payload
    let parsed ← parseTicketPayload payload
    let route := Routing.selectRoute parsed.irClass parsed.preferredBackend?
    return ticketImportResult parsed route
  | Command.ticketToArtifact => do
    let payload := ← requirePayload args.payload
    let parsed := ← parseTicketPayload payload
    ticketToArtifactResult parsed args

def run (argv : List String) : IO UInt32 := do
  let args ←
    match parseArgs argv with
    | .ok a => pure a
    | .error "help" =>
      IO.println usage
      return 0
    | .error e =>
      IO.eprintln e
      IO.eprintln usage
      return 2
  match commandOutput args with
  | .ok out =>
    IO.println out
    return 0
  | .error e =>
    IO.eprintln e
    IO.eprintln usage
    return 2

end CLI
end HeytingVeil
end HeytingLean

def main (argv : List String) : IO UInt32 := do
  HeytingLean.HeytingVeil.CLI.run argv
