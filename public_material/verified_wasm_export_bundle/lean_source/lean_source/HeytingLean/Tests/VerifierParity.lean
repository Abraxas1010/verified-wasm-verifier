import Lean.Data.Json
import HeytingLean.Crypto.ZK.Groth16

namespace HeytingLean.Tests.VerifierParity

open HeytingLean.Crypto
open HeytingLean.Crypto.ZK

def expect (msg : String) (b : Bool) : IO Unit := do
  if b then
    pure ()
  else
    throw <| IO.userError s!"VerifierParity test failed: {msg}"

def run : IO Unit := do
  let formJson : Lean.Json := Lean.Json.null
  let p : PublicInputsCore :=
    { form_commitment := HeytingLean.Crypto.Hash.commitForm formJson.compress
    , initial_state := "init"
    , final_state := "final"
    , lens_selector := 0 }
  let w : WitnessCore :=
    { reentry_values := [], boundary_marks := [], eval_trace := [] }
  match proveStructureEvalTrace formJson w p with
  | .error e => throw <| IO.userError s!"prover failed unexpectedly: {e}"
  | .ok π =>
      expect "verifier rejected prover output" (verifyStructureEvalTrace formJson p π)
      -- Tamper the proof: change it and ensure the verifier rejects.
      let π' := π ++ "tamper"
      expect "verifier accepted tampered proof" (!verifyStructureEvalTrace formJson p π')

def main (_args : List String) : IO UInt32 := do
  try
    run
    IO.println "Verifier parity passed"
    pure 0
  catch e =>
    IO.eprintln e
    pure 1

end HeytingLean.Tests.VerifierParity

/-- expose test entry point for lake target. -/
def main (args : List String) : IO UInt32 :=
  HeytingLean.Tests.VerifierParity.main args

