import HeytingLean.Crypto.ZK.RangeProofExample

/-
# CLI.RangeDemo

Tiny CLI exercising the example range-proofs correctness statement from
`Crypto.ZK.RangeProofExample`.

It constructs a simple example with `val = 5`, `lo = 0`, `hi = 10`,
checks that the example verifier accepts, and reports that the in-range
property follows from `RangeProofExample.statement_holds`.
-/

namespace HeytingLean
namespace CLI
namespace RangeDemo

open Crypto.ZK

def main (_args : List String) : IO UInt32 := do
  let p : RangeProofExample.Proof := { val := 5, lo := 0, hi := 10 }
  IO.println "RangeDemo: example range-proof correctness"
  IO.println s!"  val = {p.val}"
  IO.println s!"  lo  = {p.lo}"
  IO.println s!"  hi  = {p.hi}"
  let v := RangeProofExample.verify p
  IO.println s!"  verify p = {v}"
  if h : v = true then
    let _ : p.lo ≤ p.val ∧ p.val ≤ p.hi :=
      RangeProofExample.statement_holds p h
    IO.println "  By `RangeProofExample.statement_holds`, accepted proofs imply lo ≤ val ≤ hi."
    IO.println s!"  So  {p.lo} ≤ {p.val} ≤ {p.hi}."
  else
    IO.println "  Unexpected: verifier did not accept the example proof."
  pure 0

end RangeDemo
end CLI
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.RangeDemo.main args
