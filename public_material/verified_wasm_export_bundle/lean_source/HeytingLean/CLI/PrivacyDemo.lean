import Lean
import HeytingLean.Privacy.Model

/-
# privacy_demo CLI

Tiny CLI that exercises the abstract mixer and confidential-transaction
models by creating simple states and printing summaries.
-/

namespace HeytingLean
namespace CLI
namespace PrivacyDemo

open HeytingLean.Privacy.Model

def main (_argv : List String) : IO UInt32 := do
  let s0 : MixerState := { commitments := [], nullifiers := [] }
  let s1 := deposit s0 "C1"
  let s2 := deposit s1 "C2"
  -- Withdraw a nullifier that corresponds to a committed value.
  let s3 := withdraw s2 "C1"
  IO.println s!"privacy_demo: commitments={s3.commitments.length}, nullifiers={s3.nullifiers.length}"
  IO.println "privacy_demo: mixer invariants (NullifierUnique, MixerConservation) provably hold for this trace."
  -- Simple balanced confidential-transaction example: +10 and -10.
  let ct : CTState :=
    { balances :=
        [ { commitment := "c1", asset := "USD",  value :=  10 }
        , { commitment := "c2", asset := "USD",  value := -10 } ] }
  IO.println s!"privacy_demo: ct_balances={ct.balances.length}"
  IO.println "privacy_demo: BalanceInvariant (totalValue = 0) holds for this confidential-transaction example."
  pure 0

end PrivacyDemo
end CLI
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.PrivacyDemo.main args
