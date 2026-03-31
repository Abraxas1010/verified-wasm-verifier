import HeytingLean.Crypto.ZK.Spec.Groth16Constrained

/-!
# groth16_demo CLI

Minimal smoke test for the Groth16 spec façade, including the constrained
"multi-constraint" protocol-level soundness shape.
-/

namespace HeytingLean
namespace CLI
namespace Groth16Demo

open Crypto.ZK.Spec

def main (_args : List String) : IO UInt32 := do
  let _ := Groth16.ReferenceProtocol.knowledgeProtocol_soundness
  let _ := Groth16Constrained.Concrete.constrainedKnowledgeProtocol_soundness
  let _ := Groth16Constrained.Concrete.publicPrivateProtocol_soundness
  IO.println "groth16_demo: ok (Groth16 soundness statements typecheck)"
  pure 0

end Groth16Demo
end CLI
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.Groth16Demo.main args
