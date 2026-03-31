import Lean
import Lean.Data.Json
import HeytingLean.Util.Base64

open Lean

namespace HeytingLean.CLI
namespace FormEncExport

def run : IO Unit := do
  -- Read LOF_FORM_PATH and emit the canonical JSON string (compressed) as the encoding
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
  let canon := j.compress
  let b64 := HeytingLean.Util.Base64.encode canon.toUTF8
  IO.println b64

end FormEncExport
end HeytingLean.CLI

def main : IO Unit := HeytingLean.CLI.FormEncExport.run
