import Lean.Data.Json
import HeytingLean.LoF.Combinators.SKYMachineBounded
import HeytingLean.LoF.Combinators.STLC
import HeytingLean.LoF.Combinators.STLCSKY
import HeytingLean.LoF.Combinators.AIGOracle
import HeytingLean.LoF.LoFPrimary.AIG

/-!
# lof_stlc_fpga_export (Phase 6 demo artifact generator)

This executable exports a bounded heap+stack SKY machine instance for an STLC type-checking
example, together with an AIGER oracle circuit.

The intent is an FPGA demo:
* load the exported heap image into BRAM,
* wire the oracle Boolean (from AIG),
* step the machine for `fuel` cycles,
* and check the final head tag (`K` for true, `S` for false).
-/

namespace HeytingLean.CLI.LoFSTLCFPGAExportMain

open System
open Lean

open HeytingLean.LoF
open HeytingLean.LoF.Combinators

abbrev OracleRef : Type := AIGOracle.Ref 0

private def oracleInputs0 : Fin 0 → Bool := fun v => nomatch v

private def oracleRefTrue : OracleRef :=
  { expr := LoFPrimary.Expr.marked (n := 0), inputs := oracleInputs0 }

private def oracleRefFalse : OracleRef :=
  { expr := LoFPrimary.Expr.void (n := 0), inputs := oracleInputs0 }

private def oracleEval (r : OracleRef) : Bool :=
  AIGOracle.eval r

private def usage : String :=
  String.intercalate "\n"
    [ "Usage: lof_stlc_fpga_export [--out DIR] [--fuel N] [--max-nodes N] [--oracle true|false]"
    , "                          [--case appIdTrue|badApp|idBool|var0_in_ctx]"
    , ""
    , "Exports a bounded SKY machine heap image for an STLC type-checking demo, plus oracle AIGER."
    , ""
    , "Defaults:"
    , "  --out dist/lof_stlc_fpga"
    , "  --fuel 20000"
    , "  --max-nodes 300000"
    , "  --oracle true"
    ]

structure Cfg where
  outDir : FilePath := "dist" / "lof_stlc_fpga"
  fuel : Nat := 20000
  maxNodes : Nat := 300000
  oracleTrue : Bool := true
  caseName : String := "appIdTrue"
deriving Repr

private def parseArgs (argv : List String) : IO Cfg := do
  let rec go (cfg : Cfg) : List String → IO Cfg
    | [] => pure cfg
    | "--help" :: _ => do
        IO.println usage
        throw (IO.userError "help")
    | "--out" :: d :: rest =>
        go { cfg with outDir := d } rest
    | "--fuel" :: n :: rest =>
        match n.toNat? with
        | some v => go { cfg with fuel := v } rest
        | none => throw <| IO.userError s!"invalid --fuel value: {n}"
    | "--max-nodes" :: n :: rest =>
        match n.toNat? with
        | some v => go { cfg with maxNodes := v } rest
        | none => throw <| IO.userError s!"invalid --max-nodes value: {n}"
    | "--oracle" :: v :: rest =>
        match v with
        | "true" => go { cfg with oracleTrue := true } rest
        | "false" => go { cfg with oracleTrue := false } rest
        | _ => throw <| IO.userError s!"invalid --oracle value: {v}"
    | "--case" :: v :: rest =>
        go { cfg with caseName := v } rest
    | x :: _ =>
        throw <| IO.userError s!"unexpected argument: {x}\n\n{usage}"
  go {} argv

private def die (code : UInt32) (msg : String) : IO UInt32 := do
  IO.eprintln msg
  pure code

private def writeFileSafe (path : FilePath) (contents : String) : IO Unit := do
  IO.FS.writeFile path contents

private def mkOutDir (outDir : FilePath) : IO (Except String Unit) := do
  try
    IO.FS.createDirAll outDir
    pure (Except.ok ())
  catch e =>
    pure (Except.error s!"failed to create output directory {outDir}: {e}")

private def nodeToJson (n : SKYGraph.Node OracleRef) : Json :=
  match n with
  | .combK => Json.mkObj [("tag", Json.str "K")]
  | .combS => Json.mkObj [("tag", Json.str "S")]
  | .combY => Json.mkObj [("tag", Json.str "Y")]
  | .app f a => Json.mkObj [("tag", Json.str "app"), ("f", toJson f), ("a", toJson a)]
  | .oracle r =>
      let e := reprStr r.expr
      Json.mkObj [("tag", Json.str "oracle"), ("expr", Json.str e), ("eval", toJson (oracleEval r))]

private def stateToJson (maxNodes fuel : Nat) (s : SKYMachineBounded.State OracleRef) : Json :=
  Json.mkObj
    [ ("maxNodes", toJson maxNodes)
    , ("fuel", toJson fuel)
    , ("nodesUsed", toJson s.nodes.size)
    , ("focus", toJson s.focus)
    , ("stack", toJson s.stack.toArray)
    , ("nodes", Json.arr (s.nodes.map nodeToJson))
    ]

private def exportOne (cfg : Cfg) : IO UInt32 := do
  let outDir := cfg.outDir
  match (← mkOutDir outDir) with
  | .error msg => return (← die 2 s!"[lof_stlc_fpga_export] E-OUTDIR: {msg}")
  | .ok () => pure ()

  -- STLC demo instance.
  let (Γ, tm, ty) ←
    match cfg.caseName with
    | "appIdTrue" => pure ([], STLC.tAppIdTrue, .bool)
    | "badApp" => pure ([], STLC.tBadApp, .bool)
    | "idBool" => pure ([], STLC.tIdBool, (.bool ⟶ .bool))
    | "var0_in_ctx" => pure ([.bool], STLC.Term.var 0, .bool)
    | other => do
        let _ ← die 1 s!"[lof_stlc_fpga_export] unknown --case: {other}"
        throw (IO.userError "bad_args")

  let leanRes := STLC.check Γ tm ty

  -- Compile the STLC checker (λ) into SKY combinators, then build the decode term `b K S`.
  let chk <- match STLCSKY.checkComb? with
    | some c => pure c
    | none => return (← die 1 "[lof_stlc_fpga_export] internal error: failed to compile checker to Comb")

  let Γc <- match STLCSKY.compileClosed? (STLCSKY.encodeCtx Γ) with
    | some c => pure c
    | none => return (← die 1 "[lof_stlc_fpga_export] internal error: failed to compile ctx encoding to Comb")

  let tmc <- match STLCSKY.compileClosed? (STLCSKY.encodeTerm tm) with
    | some c => pure c
    | none => return (← die 1 "[lof_stlc_fpga_export] internal error: failed to compile term encoding to Comb")

  let tyc <- match STLCSKY.compileClosed? (STLCSKY.encodeTy ty) with
    | some c => pure c
    | none => return (← die 1 "[lof_stlc_fpga_export] internal error: failed to compile type encoding to Comb")

  let checkApp : Comb :=
    Comb.app (Comb.app (Comb.app chk Γc) tmc) tyc

  let decodeTerm : Comb :=
    Comb.app (Comb.app checkApp Comb.K) Comb.S

  let r : OracleRef := if cfg.oracleTrue then oracleRefTrue else oracleRefFalse
  let thenTerm := decodeTerm
  let elseTerm := Comb.S

  let s0 : SKYMachineBounded.State OracleRef := { nodes := #[], focus := 0, stack := [] }
  let sInit <- match SKYMachineBounded.State.wrapOracleSelect (OracleRef := OracleRef) cfg.maxNodes s0 r thenTerm elseTerm with
    | some s => pure s
    | none => return (← die 1 "[lof_stlc_fpga_export] out of heap during initial compilation; increase --max-nodes")

  let rec runWithStats (fuel : Nat) (s : SKYMachineBounded.State OracleRef)
      (stepsTaken maxStack maxNodesUsed : Nat) :
      Nat × Nat × Nat × SKYMachineBounded.State.StepResult OracleRef :=
    match fuel with
    | 0 => (stepsTaken, maxStack, maxNodesUsed, .halted s)
    | Nat.succ n =>
        match SKYMachineBounded.State.step (OracleRef := OracleRef) oracleEval cfg.maxNodes s with
        | .progress s' =>
            let maxStack' := Nat.max maxStack s'.stack.length
            let maxNodesUsed' := Nat.max maxNodesUsed s'.nodes.size
            runWithStats n s' (stepsTaken + 1) maxStack' maxNodesUsed'
        | .halted s' => (stepsTaken, maxStack, maxNodesUsed, .halted s')
        | .outOfHeap s' => (stepsTaken, maxStack, maxNodesUsed, .outOfHeap s')

  let (stepsTaken, maxStack, maxNodesUsed, out) :=
    runWithStats cfg.fuel sInit 0 sInit.stack.length sInit.nodes.size

  let expectedHead : String := if cfg.oracleTrue then (if leanRes then "K" else "S") else "S"

  let (statusTag, finalState) :=
    match out with
    | .progress s => ("progress", s)
    | .halted s => ("halted", s)
    | .outOfHeap s => ("outOfHeap", s)

  let gotHead := (SKYMachineBounded.State.headTag? (OracleRef := OracleRef) finalState).getD "none"

  if statusTag = "outOfHeap" then
    return (← die 1 s!"[lof_stlc_fpga_export] machine ran out of heap (maxNodes={cfg.maxNodes}); increase --max-nodes")

  if gotHead ≠ expectedHead then
    return (← die 1 s!"[lof_stlc_fpga_export] mismatch: expected head {expectedHead}, got {gotHead} (status={statusTag}). Try increasing --fuel.")

  let machineJson := stateToJson cfg.maxNodes cfg.fuel sInit
  let finalJson := stateToJson cfg.maxNodes cfg.fuel finalState

  let cfgPath := outDir / "config.repr.txt"
  let machinePath := outDir / "machine.json"
  let finalPath := outDir / "final.json"
  let expectedPath := outDir / "expected.txt"
  let aigPath := outDir / "oracle.aag"

  try
    writeFileSafe cfgPath (reprStr cfg ++ "\n")
    writeFileSafe machinePath (toString machineJson ++ "\n")
    writeFileSafe finalPath (toString finalJson ++ "\n")
    writeFileSafe expectedPath (String.intercalate "\n"
      [ s!"oracle={cfg.oracleTrue}"
      , s!"lean_check={leanRes}"
      , s!"expected_head={expectedHead}"
      , s!"got_head={gotHead}"
      , s!"status={statusTag}"
      , s!"steps_taken={stepsTaken}"
      , s!"max_stack={maxStack}"
      , s!"max_nodes_used={maxNodesUsed}"
      ] ++ "\n")
    let aig := LoFPrimary.AIG.ofMuxNet (LoFPrimary.MuxNet.toMuxNet r.expr)
    writeFileSafe aigPath (aig.toAigerAscii ++ "\n")
  catch e =>
    return (← die 3 s!"[lof_stlc_fpga_export] E-WRITE: failed to write outputs: {e}")

  IO.println s!"[lof_stlc_fpga_export] wrote {machinePath}"
  IO.println s!"[lof_stlc_fpga_export] wrote {finalPath}"
  IO.println s!"[lof_stlc_fpga_export] wrote {aigPath} (AIGER ASCII; oracle={cfg.oracleTrue})"
  IO.println s!"[lof_stlc_fpga_export] ok (expected_head={expectedHead}, got_head={gotHead})"
  pure 0

def main (argv : List String) : IO UInt32 := do
  try
    let cfg ← parseArgs argv
    exportOne cfg
  catch e =>
    match e with
    | .userError "help" => pure 0
    | .userError "bad_args" => pure 1
    | _ => die 1 s!"[lof_stlc_fpga_export] error: {e}"

end HeytingLean.CLI.LoFSTLCFPGAExportMain

open HeytingLean.CLI.LoFSTLCFPGAExportMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.LoFSTLCFPGAExportMain.main args
