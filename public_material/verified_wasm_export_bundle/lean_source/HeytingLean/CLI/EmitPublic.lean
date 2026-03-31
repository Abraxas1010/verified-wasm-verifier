import Lean
import Lean.Data.Json
import HeytingLean.Crypto.Form
import HeytingLean.Crypto.FormJson
import HeytingLean.Crypto.Hash.Poseidon

open Lean
open HeytingLean
open HeytingLean.Crypto

namespace HeytingLean.CLI
namespace EmitPublic

private def readFileIfExists (p : System.FilePath) : IO (Option String) := do
  try
    if ← p.pathExists then return some (← IO.FS.readFile p) else return none
  catch _ => return none

def run : IO Unit := do
  -- Resolve form JSON
  let j ← do
    match (← IO.getEnv "LOF_FORM_PATH") with
    | some p =>
        match (← readFileIfExists (System.FilePath.mk p)) with
        | some s =>
            match Json.parse s with
            | .ok j => pure j
            | .error _ => pure (Json.mkObj [("tag", Json.str "top")])
        | none => pure (Json.mkObj [("tag", Json.str "top")])
    | none => pure (Json.mkObj [("tag", Json.str "top")])

  let canonStr := j.compress
  -- If LOF_FORM_ENC_PATH is set, use its contents as the Poseidon payload; otherwise use canonical JSON
  let payload ← do
    match (← IO.getEnv "LOF_FORM_ENC_PATH") with
    | some p =>
        let fp := System.FilePath.mk p
        try
          if ← fp.pathExists then pure (← IO.FS.readFile fp) else pure canonStr
        catch _ => pure canonStr
    | none => pure canonStr
  let commit ← HeytingLean.Crypto.Hash.commitFormIO payload
  let init := (← IO.getEnv "LOF_INITIAL_STATE").getD "init0"
  let fin  := (← IO.getEnv "LOF_FINAL_STATE").getD "final0"
  let lens := (← IO.getEnv "LOF_LENS_SEL").getD "0"

  let outJ := Json.mkObj [
    ("form_commitment", Json.str commit),
    ("initial_state", Json.str init),
    ("final_state", Json.str fin),
    ("lens_selector", Json.str lens)
  ]

  match (← IO.getEnv "LOF_PUBLIC_OUT") with
  | some path =>
      IO.FS.createDirAll (System.FilePath.mk path |>.parent.getD (System.FilePath.mk "."))
      IO.FS.writeFile (System.FilePath.mk path) outJ.compress
      IO.println s!"wrote {path}"
  | none => IO.println outJ.compress

end EmitPublic
end HeytingLean.CLI

def main : IO Unit := HeytingLean.CLI.EmitPublic.run
