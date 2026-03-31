import Lean.Data.Json
import HeytingLean.Crypto.ZK.Groth16
import HeytingLean.Crypto.ZK.Spec.Groth16

namespace HeytingLean.Tests.WitnessVerification

open HeytingLean.Crypto
open HeytingLean.Crypto.ZK
open HeytingLean.Crypto.ZK.Spec.Groth16

def expect (msg : String) (b : Bool) : IO Unit := do
  if b then
    pure ()
  else
    throw <| IO.userError s!"WitnessVerification test failed: {msg}"

def expectedCommit (formJson : Lean.Json) (p : PublicInputsCore) : String :=
  let formC_new := HeytingLean.Crypto.Hash.commitForm formJson.compress
  let formC_legacy := HeytingLean.Crypto.commitString "FORM" formJson.compress
  if p.form_commitment == formC_new then formC_new else formC_legacy

def run : IO Unit := do
  let formJson : Lean.Json := Lean.Json.null
  let p : PublicInputsCore :=
    { form_commitment := expectedCommit formJson
        { form_commitment := "", initial_state := "", final_state := "", lens_selector := 0 }
    , initial_state := "init"
    , final_state := "final"
    , lens_selector := 0 }
  let w : WitnessCore :=
    { reentry_values := [], boundary_marks := [], eval_trace := [] }
  match proveStructureEvalTrace formJson w p with
  | .error e => throw <| IO.userError s!"prover failed: {e}"
  | .ok π =>
      expect "verifier rejected prover output" (verifyStructureEvalTrace formJson p π)
      pure ()

def main (_args : List String) : IO UInt32 := do
  try
    run
    IO.println "Witness verification passed"
    pure 0
  catch e =>
    IO.eprintln e
    pure 1

end HeytingLean.Tests.WitnessVerification

/-- expose test entry point for lake target. -/
def main (args : List String) : IO UInt32 :=
  HeytingLean.Tests.WitnessVerification.main args
