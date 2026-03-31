import HeytingLean.Crypto.Hash.Poseidon

namespace HeytingLean.Tests.PoseidonDeterminism

open HeytingLean.Crypto.Hash

def expect (msg : String) (b : Bool) : IO Unit := do
  if b then
    pure ()
  else
    throw <| IO.userError s!"Poseidon test failed: {msg}"

def run : IO Unit := do
  let payload := "hello"
  let h1 := poseidonCommit "FORM" payload
  let h2 := poseidonCommit "FORM" payload
  expect "poseidonCommit not deterministic" (decide (h1 = h2))
  let hTensor := poseidonCommit "TENSOR" payload
  expect "domain separation failed" (decide (h1 ≠ hTensor))
  IO.println s!"poseidonCommit sample={h1}"

def main (_args : List String) : IO UInt32 := do
  try
    run
    IO.println "Poseidon determinism passed"
    pure 0
  catch e =>
    IO.eprintln e
    pure 1

end HeytingLean.Tests.PoseidonDeterminism

/-- expose test entry point for lake target. -/
def main (args : List String) : IO UInt32 :=
  HeytingLean.Tests.PoseidonDeterminism.main args

