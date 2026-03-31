import Lean
import Lean.Data.Json
import HeytingLean.Crypto.Form
import HeytingLean.Crypto.FormJson
import HeytingLean.Crypto.PublicJson
import HeytingLean.Crypto.WitnessJson
import HeytingLean.Crypto.CoreTypes
import HeytingLean.Crypto.ZK.Groth16

open Lean
open HeytingLean
open HeytingLean.Crypto

namespace HeytingLean.CLI
namespace ZKStubDemo

def readFileIfExists (p : System.FilePath) : IO (Option String) := do
  try
    if ← p.pathExists then return some (← IO.FS.readFile p) else return none
  catch _ => return none

def run : IO Unit := do
  -- Read form
  let formJson ← do
    match (← IO.getEnv "LOF_FORM_PATH") with
    | some p =>
        match (← readFileIfExists (System.FilePath.mk p)) with
        | some s =>
            match Json.parse s with
            | .ok j => pure j
            | .error _ => pure (Json.mkObj [("tag", Json.str "top")])
        | none => pure (Json.mkObj [("tag", Json.str "top")])
    | none => pure (Json.mkObj [("tag", Json.str "top")])

  -- Public inputs
  let publicCore? ← do
    match (← IO.getEnv "LOF_PUBLIC_PATH") with
    | some p =>
        match (← readFileIfExists (System.FilePath.mk p)) with
        | some s =>
            match Json.parse s with
            | .ok j =>
                match HeytingLean.Crypto.PublicInputs.fromJson j with
                | some pub => pure (some (HeytingLean.Crypto.Convert.toCorePublic pub))
                | none => pure none
            | .error _ => pure none
        | none => pure none
    | none => pure none

  -- Witness
  let witnessCore? ← do
    match (← IO.getEnv "LOF_WITNESS_PATH") with
    | some p =>
        match (← readFileIfExists (System.FilePath.mk p)) with
        | some s =>
            match Json.parse s with
            | .ok j =>
                match HeytingLean.Crypto.Witness.fromJson j with
                | some wit => pure (HeytingLean.Crypto.Convert.toCoreWitness wit)
                | none => pure none
            | .error _ => pure none
        | none => pure none
    | none => pure none

  let mut info := "insufficient inputs"
  let mut verified := false
  let mut proofStr := ""

  match (publicCore?, witnessCore?) with
  | (some pub, some wit) =>
      match HeytingLean.Crypto.ZK.proveStructureEvalTrace formJson wit pub with
      | .ok π =>
          proofStr := π
          verified := HeytingLean.Crypto.ZK.verifyStructureEvalTrace formJson pub π
          info := "proof generated"
      | .error e =>
          info := s!"prove error: {e}"
  | _ => info := info

  let out := Json.mkObj [
    ("info", Json.str info),
    ("verified", Json.bool verified),
    ("proof", Json.str proofStr)
  ]
  IO.println (out.compress)

end ZKStubDemo
end HeytingLean.CLI

def main : IO Unit := HeytingLean.CLI.ZKStubDemo.run
