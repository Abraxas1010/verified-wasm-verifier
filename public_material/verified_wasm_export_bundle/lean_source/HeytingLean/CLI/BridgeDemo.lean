import HeytingLean.Crypto.ZK.BridgeToy

/-
# CLI.BridgeDemo

Tiny CLI exercising the example ZK-bridge soundness statement from
`Crypto.ZK.BridgeToy`.

It constructs a simple example proof with matching source and
destination messages, checks that `verify` accepts it, and reports that
the equality of messages follows from `BridgeToy.statement_holds`.
-/

namespace HeytingLean
namespace CLI
namespace BridgeDemo

open Crypto.ZK

def main (_args : List String) : IO UInt32 := do
  let p : BridgeToy.Proof := { srcMsg := 7, dstMsg := 7 }
  IO.println "BridgeDemo: example ZK bridge soundness"
  IO.println s!"  srcMsg = {p.srcMsg}"
  IO.println s!"  dstMsg = {p.dstMsg}"
  let v := BridgeToy.verify p
  IO.println s!"  verify p = {v}"
  if h : v = true then
    let _hEq : p.srcMsg = p.dstMsg :=
      BridgeToy.statement_holds p h
    IO.println "  By `BridgeToy.statement_holds`, accepted proofs imply srcMsg = dstMsg."
    IO.println s!"  So srcMsg = dstMsg = {p.srcMsg}."
  else
    IO.println "  Unexpected: verifier did not accept the example proof."
  pure 0

end BridgeDemo
end CLI
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.BridgeDemo.main args
