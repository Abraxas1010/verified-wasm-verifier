import Lean
import HeytingLean.ProofGraph.Core

namespace HeytingLean.ProofGraph

/-
The canonical schema reserves an InfoTree lane, but this first extraction pass
does not synthesize elaboration trees yet. Keeping the type explicit prevents
later agents from faking "proof graph completeness" by omission.
-/

structure InfoTreeAttachment where
  source : InfoTreeSource := .offlineUnavailable
  root? : Option NodeId := none
  nodes : Array Node := #[]
  edges : Array Edge := #[]
  deriving Inhabited

def emptyInfoTreeAttachment : InfoTreeAttachment := {}

end HeytingLean.ProofGraph
