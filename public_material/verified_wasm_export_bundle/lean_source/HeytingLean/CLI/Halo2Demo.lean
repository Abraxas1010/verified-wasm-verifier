import HeytingLean.Crypto.ZK.Spec.Halo2

/-!
# halo2_demo CLI

Minimal smoke test for the Halo2 abstract protocol skeleton (example instance).
-/

namespace HeytingLean
namespace CLI
namespace Halo2Demo

open Crypto.ZK.Spec

def main (_args : List String) : IO UInt32 := do
  let _ : Halo2.CorrectnessStatement Halo2.Example.protocol :=
    Halo2.Example.protocol_correctness
  IO.println "halo2_demo: ok (example protocol correctness statement typechecks)"
  pure 0

end Halo2Demo
end CLI
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.Halo2Demo.main args
