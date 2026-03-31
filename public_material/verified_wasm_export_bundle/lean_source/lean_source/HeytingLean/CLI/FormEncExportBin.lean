import Lean
import Lean.Data.Json
import HeytingLean.Util.Base64
import HeytingLean.Crypto.FormJson
import HeytingLean.Crypto.FormEncBin

open Lean

namespace HeytingLean.CLI
namespace FormEncExportBin

def run : IO Unit := do
  -- v0 binary encoding for Form 3: base64 of a minimal tag-based encoding
  let s? ← do
    match (← IO.getEnv "LOF_FORM_PATH") with
    | some p =>
        let fp := System.FilePath.mk p
        try
          if ← fp.pathExists then
            let txt ← IO.FS.readFile fp
            pure (some txt)
          else
            pure none
        catch _ => pure none
    | none => pure none
  let j :=
    match s? with
    | some txt => match Json.parse txt with
                  | .ok j => j
                  | .error _ => Json.mkObj [("tag", Json.str "top")]
    | none     => Json.mkObj [("tag", Json.str "top")]
  let encBytes :=
    match HeytingLean.Crypto.Form3.fromJson j with
    | some f => HeytingLean.Crypto.FormEncBin.encode3 f
    | none   => ByteArray.mk #[]
  let b64 := HeytingLean.Util.Base64.encode encBytes
  IO.println b64

end FormEncExportBin
end HeytingLean.CLI

def main : IO Unit := HeytingLean.CLI.FormEncExportBin.run
