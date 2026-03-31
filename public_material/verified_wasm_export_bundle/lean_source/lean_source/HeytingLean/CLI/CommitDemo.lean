import Lean
import HeytingLean.Crypto.Commit
import HeytingLean.Crypto.Hash.Poseidon
import HeytingLean.Payments.Merkle

/-
# commit_demo CLI

Tiny CLI that exercises the string/Poseidon commitment helpers and the
string-mode Merkle helpers on example inputs. It is intended as a sanity
check for the commitment boundary rather than a cryptographic test.
-/

namespace HeytingLean
namespace CLI
namespace CommitDemo

open HeytingLean.Crypto
open HeytingLean.Crypto.Hash
open HeytingLean.Payments
open HeytingLean.Payments.Merkle

def main (_argv : List String) : IO UInt32 := do
  let msg := "hello"
  let c1 := commitString "demo" msg
  let c2 := commitString "demo" msg
  let formC := commitForm msg
  let leaf := computeLeaf "alice"
  let leaf' := computeLeaf "alice"
  IO.println s!"commit_demo:"
  IO.println s!"  commitString deterministic = {c1 == c2}"
  IO.println s!"  commitForm (Poseidon boundary) = {formC}"
  IO.println s!"  Merkle.computeLeaf deterministic = {leaf == leaf'}"
  pure 0

end CommitDemo
end CLI
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.CommitDemo.main args
