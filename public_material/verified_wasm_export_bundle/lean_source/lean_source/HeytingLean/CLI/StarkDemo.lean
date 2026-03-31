import HeytingLean.Crypto.ZK.Spec.STARK

/-!
# stark_demo CLI

Minimal smoke test for the STARK abstract protocol skeleton (example instance).
-/

namespace HeytingLean
namespace CLI
namespace StarkDemo

open Crypto.ZK.Spec

def main (_args : List String) : IO UInt32 := do
  let _ : STARK.StarkSoundnessStatement STARK.Example.protocol :=
    STARK.Example.protocol_soundness
  IO.println "stark_demo: ok (example STARK soundness statement typechecks)"
  pure 0

end StarkDemo
end CLI
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.StarkDemo.main args
