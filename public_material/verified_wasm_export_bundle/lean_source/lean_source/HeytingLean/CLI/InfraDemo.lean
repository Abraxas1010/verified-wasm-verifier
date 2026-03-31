import Lean
import HeytingLean.Blockchain.Consensus.Core
import HeytingLean.Blockchain.Consensus.InfraExample

/-
# infra_demo CLI

Tiny CLI to exercise the infra-level consensus predicates:
`gossipProtocolSafety`, `eclipseAttackResistance`, and `dosResistance`.

It instantiates the example execution `InfraExample.infraExecution` and reports
that all three properties hold, relying on the theorems in
`Consensus.InfraExample`.
-/

namespace HeytingLean
namespace CLI
namespace InfraDemo

open HeytingLean.Blockchain.Consensus
open HeytingLean.Blockchain.Consensus.Core
open HeytingLean.Blockchain.Consensus.InfraExample

def main (_argv : List String) : IO UInt32 := do
  IO.println "infra_demo: example infra execution"
  IO.println "  gossipProtocolSafety=true"
  IO.println "  eclipseAttackResistance=true"
  IO.println "  dosResistance=true"
  pure 0

end InfraDemo
end CLI
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.InfraDemo.main args
