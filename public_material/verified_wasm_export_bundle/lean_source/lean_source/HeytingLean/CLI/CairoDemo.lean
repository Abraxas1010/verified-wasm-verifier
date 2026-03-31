import HeytingLean.Crypto.ZK.Spec.Cairo

/-!
# cairo_demo CLI

Minimal smoke test for the Cairo execution-correctness skeleton (example model).
-/

namespace HeytingLean
namespace CLI
namespace CairoDemo

open Crypto.ZK.Spec

def main (_args : List String) : IO UInt32 := do
  let _ : Cairo.ExecutionCorrectnessStatement Cairo.Example.model :=
    Cairo.Example.model_executionCorrectness
  IO.println "cairo_demo: ok (example Cairo execution-correctness statement typechecks)"
  pure 0

end CairoDemo
end CLI
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.CairoDemo.main args
