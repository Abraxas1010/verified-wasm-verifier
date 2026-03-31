-- import HeytingLean.Blockchain.Rollup.StateTransition -- heavy modules not needed for CLI banner
-- import HeytingLean.Blockchain.Rollup.MultiLens

namespace HeytingLean
namespace Blockchain
namespace Rollup
namespace CLI
namespace Demo

open IO

/-- A minimal CLI that reports the availability of the multi‑lens rollup verifier.
This demo does not execute verifiers at runtime (those are parametric over α and R);
it serves as an integration marker and help text for developers. -/
def main (_args : List String) : IO UInt32 := do
  println "HeytingLean Rollup Demo"
  println "Modules:"
  println "  - Blockchain.Rollup.StateTransition (Spec, validTransition, program, occamEval)"
  println "  - Blockchain.Rollup.MultiLens (verifyWith, tensor/graph/clifford, equivalence)"
  println "See lean/HeytingLean/Tests/Rollup/LensEquiv.lean for type-checked examples."
  pure 0

end Demo
end CLI
end Rollup
end Blockchain
end HeytingLean

-- Provide a top-level main alias for the executable linker
open HeytingLean.Blockchain.Rollup.CLI.Demo in
def main (args : List String) : IO UInt32 :=
  HeytingLean.Blockchain.Rollup.CLI.Demo.main args
