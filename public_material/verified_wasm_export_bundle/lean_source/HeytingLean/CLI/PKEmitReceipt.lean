import Lean
import Lean.Data.Json
import HeytingLean.CLI.Args
import HeytingLean.Util.SHA

/-!
Emit a proof-kit compatible execution receipt from the outputs of pm_prove.
Reads `public.json`, `r1cs.json`, and `certificate.json` from an output directory
and writes `receipt.json` with required fields.
-/

namespace HeytingLean
namespace CLI
namespace PKEmitReceipt

open Lean

private def readFileE (p : System.FilePath) : IO (Except String String) := do
  try let s ← IO.FS.readFile p; pure (.ok s) catch e => pure (.error s!"read error at {p}: {e}")

def main (args : List String) : IO UInt32 := do
  let args := HeytingLean.CLI.stripLakeArgs args
  match args with
  | [outDirStr] =>
      let outDir := System.FilePath.mk outDirStr
      let pubPath := outDir / "public.json"
      let r1csPath := outDir / "r1cs.json"
      let certPath := outDir / "certificate.json"
      let pubRaw ← match (← readFileE pubPath) with | .ok s => pure s | .error m => IO.eprintln m; return 1
      let r1csRaw ← match (← readFileE r1csPath) with | .ok s => pure s | .error m => IO.eprintln m; return 1
      let certRaw ← match (← readFileE certPath) with | .ok s => pure s | .error m => IO.eprintln m; return 1
      let pubJ ← match Json.parse pubRaw with | .ok j => pure j | .error e => IO.eprintln e; return 1
      -- cert_hash = sha256(certRaw) as 64 hex without 0x
      let certHashHex ← HeytingLean.Util.sha256HexOfStringIO certRaw
      let cert_hash :=
        if certHashHex.startsWith "0x" then certHashHex.drop 2 else certHashHex
      -- blueprint_hash = sha256(r1csRaw) as 64 hex without 0x
      let blueprintHashHex ← HeytingLean.Util.sha256HexOfStringIO r1csRaw
      let blueprint_hash :=
        if blueprintHashHex.startsWith "0x" then blueprintHashHex.drop 2 else blueprintHashHex
      -- Build receipt
      let receipt := Json.mkObj
        [ ("public", pubJ)
        , ("proof", Json.str "")
        , ("cert_hash", Json.str cert_hash)
        , ("blueprint_hash", Json.str blueprint_hash)
        ]
      let outPath := outDir / "receipt.json"
      IO.FS.writeFile outPath (receipt.compress)
      IO.println s!"wrote {outPath}"
      return 0
  | _ =>
      IO.eprintln "usage: lake exe pk_emit_receipt <outdir>"; return 2

end PKEmitReceipt
end CLI
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.PKEmitReceipt.main args
