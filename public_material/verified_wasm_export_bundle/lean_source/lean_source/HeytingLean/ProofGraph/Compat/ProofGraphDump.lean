import Lean
import HeytingLean.ProofGraph.Core

namespace HeytingLean.ProofGraph.Compat

open Lean
open HeytingLean.ProofGraph

def toLegacyDumpJson (graph : ProofGraph) : Json :=
  Json.mkObj
    [ ("schema", Json.str graph.schema)
    , ("target_decl", Json.str graph.targetDecl.toString)
    , ("proof_source", Json.str graph.proofSource.toString)
    , ("nodes", Json.arr <| graph.nodes.map (fun n =>
        Json.mkObj
          [ ("id", toJson n.id)
          , ("kind", Json.str n.kind.toString)
          , ("depth", toJson n.depth)
          , ("label", Json.str n.label)
          ]))
    , ("edges", Json.arr <| graph.edges.map (fun e =>
        Json.mkObj
          [ ("src", toJson e.src)
          , ("dst", toJson e.dst)
          , ("label", Json.str e.label)
          ]))
    , ("root", toJson graph.roots.typeRoot)
    ]

end HeytingLean.ProofGraph.Compat
