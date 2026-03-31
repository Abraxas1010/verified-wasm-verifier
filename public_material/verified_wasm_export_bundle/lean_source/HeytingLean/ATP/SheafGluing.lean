import HeytingLean.ATP.ProofNetwork
import HeytingLean.QuantumActiveInference.SheafGluing

/-!
# ATP.SheafGluing

Glue-edge construction for proof networks.

This module connects the executable `ProofNetwork` bookkeeping structure to the
`QuantumActiveInference.SheafGluing` predicate layer.
-/

namespace HeytingLean
namespace ATP

open HeytingLean.Embeddings
open HeytingLean.QuantumActiveInference

/-- A proof-network gluing edge label (stable string for visualization/export). -/
def glueLabel : String := "glue"

/-- Add a gluing edge between two node IDs. -/
def addGlueEdge (G : ProofNetwork) (src dst : Nat) : ProofNetwork :=
  G.addEdge src dst glueLabel

/-- Add a gluing edge and record a theorem/witness supporting this transport. -/
def addWitnessedGlueEdge (G : ProofNetwork) (src dst : Nat) (witness : String) : ProofNetwork :=
  G.addWitnessedEdge src dst glueLabel witness

end ATP
end HeytingLean
