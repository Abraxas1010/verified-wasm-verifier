import HeytingLean.Crypto.ZK.FraudProofToy

/-
# CLI.FraudDemo

Tiny CLI exercising the example fraud-proof validity statement from
`Crypto.ZK.FraudProofToy`.

It constructs a simple example with `before = 10`, `w = 2`, and
`after = before + (w + 1) = 13`, checks that the equality holds, and
reports that `Statement` holds for this instance (which follows from
the proved theorem `FraudProofToy.statement_holds`).
-/

namespace HeytingLean
namespace CLI
namespace FraudDemo

open Crypto.ZK

def main (_args : List String) : IO UInt32 := do
  let before : Nat := 10
  let w : Nat := 2
  let after : Nat := before + Nat.succ w
  IO.println s!"Example fraud-proof:"
  IO.println s!"  before = {before}"
  IO.println s!"  witness w = {w} (so w+1 = {Nat.succ w})"
  IO.println s!"  after  = before + (w+1) = {after}"
  if h : after = before + Nat.succ w then
    let _hNe : after ≠ before :=
      FraudProofToy.statement_holds before after w h
    IO.println "Check: after = before + (w+1) holds."
    IO.println "By `FraudProofToy.statement_holds`, this implies after ≠ before."
    IO.println s!"  So indeed after ≠ before: {before} ≠ {after}."
  else
    IO.println "Unexpected: arithmetic example does not satisfy after = before + (w+1)."
  pure 0

end FraudDemo
end CLI
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.FraudDemo.main args
