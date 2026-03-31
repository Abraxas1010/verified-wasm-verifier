import Lean
import HeytingLean.ProofGraph.Core

namespace HeytingLean.ProofGraph

open Lean

def renderJson (graph : ProofGraph) : String :=
  toString graph.asJson

end HeytingLean.ProofGraph
