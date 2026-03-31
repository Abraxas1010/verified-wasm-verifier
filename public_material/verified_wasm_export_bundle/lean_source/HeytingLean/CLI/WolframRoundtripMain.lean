import Lean
import Lean.Data.Json
import HeytingLean.Util.SHA

open Lean
open System

namespace HeytingLean
namespace CLI

namespace WolframRoundtrip

structure Args where
  outDir : FilePath := FilePath.mk ".tmp" / "wolfram_roundtrip"
  echoDemo : Bool := false
  notebook : Option FilePath := none
  notebookIndex : Nat := 1
  notebookSteps : Nat := 10
deriving Inhabited

private def parseArg (xs : List String) (flag : String) : Option String :=
  match xs with
  | [] => none
  | x :: y :: rest => if x == flag then some y else parseArg (y :: rest) flag
  | _ => none

private def parseArgs (argv : List String) : Args :=
  let outDir :=
    (parseArg argv "--out").map FilePath.mk
      |>.getD (FilePath.mk ".tmp" / "wolfram_roundtrip")
  let echoDemo := argv.any (· == "--echo")
  let notebook := (parseArg argv "--notebook").map (fun s => FilePath.mk s)
  let notebookIndex := (parseArg argv "--index").bind (·.toNat?) |>.getD 1
  let notebookSteps := (parseArg argv "--steps").bind (·.toNat?) |>.getD 10
  { outDir, echoDemo, notebook, notebookIndex, notebookSteps }

private def usage : String :=
  String.intercalate "\n"
    [ "wolfram_roundtrip (lossless Lean ↔ Wolfram demo)"
    , ""
    , "Safe default: running with no args exits 0."
    , ""
    , "Usage:"
    , "  lake exe wolfram_roundtrip -- --echo"
    , "  lake exe wolfram_roundtrip -- --notebook ~/Downloads/claude_test_hypergraph.nb --index 1 --steps 10"
    , ""
    , "Options:"
    , "  --out <dir>        output directory (default: .tmp/wolfram_roundtrip)"
    , "  --echo             run Lean→Wolfram→Lean binary echo demo"
    , "  --notebook <path>  run notebook extraction via wolframscript + SetReplace`"
    , "  --index <n>        select extracted WolframModel call (default: 1; use 0 to list)"
    , "  --steps <n>        override steps (default: 10)"
    ]

private def expandTilde (p : FilePath) : IO FilePath := do
  let s := p.toString
  if s.startsWith "~/" then
    match (← IO.getEnv "HOME") with
    | some home => pure <| FilePath.mk home / FilePath.mk (s.drop 2)
    | none => pure p
  else
    pure p

private partial def findRepoRoot (start : FilePath) (fuel : Nat := 6) : IO (Option FilePath) := do
  if fuel == 0 then
    return none
  let lakefile := start / "lakefile.lean"
  if (← lakefile.pathExists) then
    -- This repo keeps the Lean project under `lean/`, with a top-level `lakefile.lean` symlink.
    -- If invoked from within `lean/`, prefer the parent directory as the repo root so we can
    -- locate `ffi/` and `scripts/` reliably.
    if start.fileName == some "lean" then
      match start.parent with
      | some p =>
          let parentLakefile := p / "lakefile.lean"
          if (← parentLakefile.pathExists) then
            return some p
          else
            return some start
      | none => return some start
    else
      return some start
  match start.parent with
  | none => return none
  | some p => findRepoRoot p (fuel - 1)

private def u64BytesLE (u : UInt64) : Array UInt8 :=
  let rec go (k : Nat) (n : Nat) (acc : Array UInt8) : Array UInt8 :=
    match k with
    | 0 => acc
    | k + 1 =>
        let b : UInt8 := UInt8.ofNat (n % 256)
        go k (n / 256) (acc.push b)
  go 8 u.toNat #[]

private def encodeU64LEList (xs : List UInt64) : ByteArray :=
  let out : Array UInt8 := Id.run do
    let mut acc : Array UInt8 := #[]
    for x in xs do
      for b in u64BytesLE x do
        acc := acc.push b
    return acc
  ByteArray.mk out

private def decodeU64AtLE (bytes : ByteArray) (offset : Nat) : UInt64 :=
  let rec go (i : Nat) (pow : Nat) (acc : Nat) : Nat :=
    if i < 8 then
      let b := bytes.get! (offset + i) |>.toNat
      go (i + 1) (pow * 256) (acc + b * pow)
    else
      acc
  UInt64.ofNat (go 0 1 0)

private def decodeU64LEList (bytes : ByteArray) : Except String (List UInt64) := Id.run do
  let sz := bytes.size
  if sz % 8 != 0 then
    return .error s!"binary size not multiple of 8 (size={sz})"
  let n := sz / 8
  let mut acc : Array UInt64 := #[]
  for i in [0:n] do
    acc := acc.push (decodeU64AtLE bytes (i * 8))
  return .ok acc.toList

private def splitByLengths (lengths : List Nat) (data : List Nat) : Except String (List (List Nat)) :=
  match lengths with
  | [] =>
      if data.isEmpty then .ok [] else .error "data remaining after consuming all lengths"
  | len :: rest =>
      let (edge, tail) := data.splitAt len
      if edge.length != len then
        .error s!"insufficient data for edge length={len} (got {edge.length})"
      else
        match splitByLengths rest tail with
        | .ok edges => .ok (edge :: edges)
        | .error e => .error e

private def flattenEdges (edges : List (List Nat)) : List Nat :=
  edges.foldl (fun acc e => acc ++ e) []

private def edgeLengths (edges : List (List Nat)) : List Nat :=
  edges.map List.length

private def metricSumVertices (edges : List (List Nat)) : Nat :=
  edges.foldl (fun acc e => e.foldl (fun acc2 v => acc2 + v) acc) 0

private def readHypergraph (dataPath lengthsPath : FilePath) : IO (Except String (List (List Nat))) := do
  let dataBytes ← IO.FS.readBinFile dataPath
  let lensBytes ← IO.FS.readBinFile lengthsPath
  match (decodeU64LEList lensBytes, decodeU64LEList dataBytes) with
  | (.error e, _) => return .error s!"lengths decode failed: {e}"
  | (_, .error e) => return .error s!"data decode failed: {e}"
  | (.ok lensU, .ok dataU) =>
      let lens := lensU.map (·.toNat)
      let data := dataU.map (·.toNat)
      return splitByLengths lens data

private def writeHypergraph (dataPath lengthsPath : FilePath) (edges : List (List Nat)) : IO Unit := do
  let lens := edgeLengths edges |>.map UInt64.ofNat
  let flat := flattenEdges edges |>.map UInt64.ofNat
  IO.FS.writeBinFile lengthsPath (encodeU64LEList lens)
  IO.FS.writeBinFile dataPath (encodeU64LEList flat)

private def readVerifiedMetric? (metaPath : FilePath) : IO (Option Nat) := do
  if !(← metaPath.pathExists) then
    return none
  let raw ← IO.FS.readFile metaPath
  match Json.parse raw with
  | .error _ => return none
  | .ok j =>
      match j.getObjVal? "verifiedMetric" with
      | .ok (.str s) => return s.toNat?
      | _ => return none

private def runWolframscript (args : Array String) (cwd : Option FilePath := none) : IO (Except String IO.Process.Output) := do
  try
    let out ← IO.Process.output { cmd := "wolframscript", args := args, cwd := cwd }
    return .ok out
  catch e =>
    return .error s!"failed to run wolframscript: {e}"

private def requireOk (label : String) (out : IO.Process.Output) : Except String Unit :=
  if out.exitCode == 0 then
    .ok ()
  else
    .error s!"{label} failed rc={out.exitCode} stderr={out.stderr.trim}"

private def echoDemo (root : FilePath) (outDir : FilePath) : IO (Except String Unit) := do
  IO.println "[echo] Lean→Wolfram→Lean (lossless binary echo)"
  let outDir := if outDir.isAbsolute then outDir else root / outDir
  let demoEdges : List (List Nat) := [[1, 2, 3], [2, 4, 5]]
  let inData := outDir / "echo_in_hypergraph.bin"
  let inLens := outDir / "echo_in_lengths.bin"
  let outData := outDir / "echo_out_hypergraph.bin"
  let outLens := outDir / "echo_out_lengths.bin"

  try
    IO.FS.createDirAll outDir
  catch e =>
    return .error s!"failed to create out dir {outDir}: {e}"

  writeHypergraph inData inLens demoEdges

  let echoWls := root / "ffi" / "heyting_wolfram_bridge" / "echo_hypergraph_binary.wls"
  if !(← echoWls.pathExists) then
    return .error s!"missing echo script: {echoWls}"

  let out? ← runWolframscript #["-file", echoWls.toString, inData.toString, inLens.toString, outData.toString, outLens.toString] (cwd := some root)
  match out? with
  | .error e => return .error e
  | .ok out =>
      match requireOk "echo_hypergraph_binary.wls" out with
      | .error e => return .error e
      | .ok _ =>
          let shaInData ← HeytingLean.Util.sha256HexOfFileIO inData
          let shaOutData ← HeytingLean.Util.sha256HexOfFileIO outData
          let shaInLens ← HeytingLean.Util.sha256HexOfFileIO inLens
          let shaOutLens ← HeytingLean.Util.sha256HexOfFileIO outLens
          if shaInData != shaOutData || shaInLens != shaOutLens then
            return .error s!"sha256 mismatch (data: {shaInData} vs {shaOutData}; lens: {shaInLens} vs {shaOutLens})"

          let decoded? ← readHypergraph outData outLens
          match decoded? with
          | .error e => return .error e
          | .ok edges =>
              if edges != demoEdges then
                return .error "decoded hypergraph differs from original demoEdges"
              IO.println "[echo] OK (byte-identical roundtrip)"
              return .ok ()

private def notebookDemo (root : FilePath) (args : Args) : IO (Except String Unit) := do
  match args.notebook with
  | none => return .ok ()
  | some nb0 =>
      IO.println "[notebook] WolframModel(.nb) → binary → Lean metric check"
      let nb ← expandTilde nb0
      if !(← nb.pathExists) then
        return .error s!"notebook not found: {nb}"

      let outRoot := if args.outDir.isAbsolute then args.outDir else root / args.outDir
      let outDir := outRoot / "notebook"
      try
        IO.FS.createDirAll outDir
      catch e =>
        return .error s!"failed to create out dir {outDir}: {e}"

      let runnerWls := root / "ffi" / "heyting_wolfram_bridge" / "notebook_hypergraph_analysis.wls"
      if !(← runnerWls.pathExists) then
        return .error s!"missing notebook runner script: {runnerWls}"

      let out? ← runWolframscript #[
        "-file", runnerWls.toString,
        nb.toString,
        toString args.notebookIndex,
        toString args.notebookSteps,
        outDir.toString
      ] (cwd := some root)
      match out? with
      | .error e => return .error e
      | .ok out =>
          match requireOk "notebook_hypergraph_analysis.wls" out with
          | .error e => return .error e
          | .ok _ =>
              let modelKey := nb.fileStem.getD "notebook" ++ s!"_nb{args.notebookIndex}"
              let dataPath := outDir / s!"{modelKey}_hypergraph.bin"
              let lensPath := outDir / s!"{modelKey}_lengths.bin"
              let metaPath := outDir / s!"{modelKey}_metadata.json"

              let edges? ← readHypergraph dataPath lensPath
              match edges? with
              | .error e => return .error e
              | .ok edges =>
                  let metric := metricSumVertices edges
                  IO.println s!"[notebook] Lean metric: {metric}"

                  if let some vm ← readVerifiedMetric? metaPath then
                    IO.println s!"[notebook] Wolfram(heyting_add2) metric: {vm}"
                    if vm != metric then
                      return .error s!"metric mismatch (Lean={metric}, Wolfram={vm})"
                    IO.println "[notebook] OK (metrics match)"
                  else
                    IO.println "[notebook] NOTE: no verifiedMetric found in metadata (skipping cross-check)"

                  -- Confirm our re-encoding matches the Wolfram-exported bytes.
                  let origData ← IO.FS.readBinFile dataPath
                  let origLens ← IO.FS.readBinFile lensPath
                  let flat := flattenEdges edges |>.map UInt64.ofNat
                  let lens := edgeLengths edges |>.map UInt64.ofNat
                  let encData := encodeU64LEList flat
                  let encLens := encodeU64LEList lens
                  if origData != encData || origLens != encLens then
                    return .error "Lean re-encoding does not match Wolfram-exported bytes"

                  IO.println "[notebook] OK (Lean re-encoding is byte-identical)"
                  return .ok ()

def main (argv : List String) : IO UInt32 := do
  if argv.isEmpty || argv.any (· == "--help") then
    IO.println usage
    return 0

  let args := parseArgs argv
  let cwd ← IO.currentDir
  let root ←
    match (← findRepoRoot cwd) with
    | some r => pure r
    | none => pure cwd

  if !args.echoDemo && args.notebook.isNone then
    -- No mode selected: be a safe no-op.
    return 0

  let mut ok : Bool := true

  if args.echoDemo then
    match (← echoDemo root args.outDir) with
    | .ok _ => pure ()
    | .error e =>
        ok := false
        IO.eprintln s!"[echo] FAIL: {e}"

  match (← notebookDemo root args) with
  | .ok _ => pure ()
  | .error e =>
      ok := false
      IO.eprintln s!"[notebook] FAIL: {e}"

  return (if ok then 0 else 1)

end WolframRoundtrip

end CLI
end HeytingLean

def main (argv : List String) : IO UInt32 :=
  HeytingLean.CLI.WolframRoundtrip.main argv
