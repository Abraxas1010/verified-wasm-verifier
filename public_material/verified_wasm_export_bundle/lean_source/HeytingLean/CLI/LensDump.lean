import Lean
import Lean.Data.Json
import HeytingLean.Crypto.Form
import HeytingLean.Crypto.FormJson
import HeytingLean.LoF.Core
import HeytingLean.LoF.Lens.Tensor
import HeytingLean.LoF.Lens.Graph
import HeytingLean.LoF.Lens.Clifford

open Lean
open HeytingLean
open HeytingLean.Crypto

namespace HeytingLean.CLI
namespace LensDump

def mkSampleForm : Form 3 :=
  let x0 : Form 3 := .var ⟨0, by decide⟩
  let x1 : Form 3 := .var ⟨1, by decide⟩
  let x2 : Form 3 := .var ⟨2, by decide⟩
  .and x0 (.or x1 x2)

def run : IO Unit := do
  -- Parse optional LOF_FORM_PATH or use sample
  let form : Form 3 ← do
    match (← IO.getEnv "LOF_FORM_PATH") with
    | some p =>
        let fp := System.FilePath.mk p
        let content? ← (do
          try
            if ← fp.pathExists then
              let s ← IO.FS.readFile fp
              pure (some s)
            else pure none
          catch _ => pure none)
        match content? with
        | some content =>
            match Json.parse content with
            | .ok j => match HeytingLean.Crypto.Form3.fromJson j with
                        | some f => pure f
                        | none => pure mkSampleForm
            | .error _ => pure mkSampleForm
        | none => pure mkSampleForm
    | none => pure mkSampleForm

  let canon := HeytingLean.LoF.canonicalize form
  let tensor := HeytingLean.LoF.Lens.encodeTensor form
  let graph := HeytingLean.LoF.Lens.encodeGraph form
  let cliff := HeytingLean.LoF.Lens.encodeClifford form

  -- Round-trip check using scaffold decoders
  let rt :=
    let c1 := HeytingLean.LoF.Lens.decodeTensorToCanonical tensor canon
    let c2 := HeytingLean.LoF.Lens.decodeGraphToCanonical graph canon
    let c3 := HeytingLean.LoF.Lens.decodeCliffordToCanonical cliff canon
    c1.asString == canon.asString && c2.asString == canon.asString && c3.asString == canon.asString

  let out := Json.mkObj [
    ("canonical", Json.str canon.asString),
    ("tensor", Json.str tensor),
    ("graph", Json.str graph),
    ("clifford", Json.str cliff),
    ("roundTripOK", Json.bool rt)
  ]
  IO.println (out.compress)

end LensDump
end HeytingLean.CLI

def main : IO Unit := HeytingLean.CLI.LensDump.run
