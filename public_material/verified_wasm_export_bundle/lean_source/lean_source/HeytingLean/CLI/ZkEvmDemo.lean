import HeytingLean.Crypto.ZK.Spec.ZkEvm

/-!
# zkevm_demo CLI

Minimal smoke test for the zkEVM equivalence skeleton (example model).
-/

namespace HeytingLean
namespace CLI
namespace ZkEvmDemo

open Crypto.ZK.Spec

def main (_args : List String) : IO UInt32 := do
  let _ : ZkEvm.EquivalenceStatement ZkEvm.Example.model :=
    ZkEvm.Example.model_equivalence
  IO.println "zkevm_demo: ok (example zkEVM equivalence statement typechecks)"
  pure 0

end ZkEvmDemo
end CLI
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.ZkEvmDemo.main args
