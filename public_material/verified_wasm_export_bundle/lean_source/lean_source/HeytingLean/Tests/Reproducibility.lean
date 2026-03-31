import HeytingLean.Crypto.Hash.Poseidon

namespace HeytingLean.Tests.Reproducibility

open HeytingLean.Crypto.Hash

def expect (msg : String) (b : Bool) : IO Unit := do
  if b then
    pure ()
  else
    throw <| IO.userError s!"Reproducibility test failed: {msg}"

def run : IO Unit := do
  let payload := "repro"
  let a := commitForm payload
  let b := commitForm payload
  expect "commitForm not deterministic" (decide (a = b))

def main (_args : List String) : IO UInt32 := do
  try
    run
    IO.println "Reproducibility passed"
    pure 0
  catch e =>
    IO.eprintln e
    pure 1

end HeytingLean.Tests.Reproducibility

/-- expose test entry point for lake target. -/
def main (args : List String) : IO UInt32 :=
  HeytingLean.Tests.Reproducibility.main args

