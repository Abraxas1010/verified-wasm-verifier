import HeytingLean.Blockchain.MerkleModel

namespace HeytingLean.Tests.MerkleCorrectness

open HeytingLean.Blockchain.MerkleModel
open HeytingLean.Payments.Merkle

def expect (msg : String) (b : Bool) : IO Unit := do
  if b then
    pure ()
  else
    throw <| IO.userError s!"Merkle test failed: {msg}"

def run : IO Unit := do
  let t : Tree := Tree.node (Tree.leaf "a") (Tree.leaf "b")
  match h : buildPath? "b" t with
  | none =>
      throw <| IO.userError "Merkle test failed: expected path, got none"
  | some path =>
      let _ : member "b" t := by
        exact buildPath?_member "b" t path (by simpa using h)
      let p : VProof := { root := root t, recipient := "b", path := path }
      let out := verifyMembership p
      expect "verifyMembership rejected buildPath? witness" (decide (out = (true, root t)))

def main (_args : List String) : IO UInt32 := do
  try
    run
    IO.println "Merkle correctness passed"
    pure 0
  catch e =>
    IO.eprintln e
    pure 1

end HeytingLean.Tests.MerkleCorrectness

/-- expose test entry point for lake target. -/
def main (args : List String) : IO UInt32 :=
  HeytingLean.Tests.MerkleCorrectness.main args
