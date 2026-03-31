import HeytingLean.Symbolic.SMT
import HeytingLean.Symbolic.TPTP
import HeytingLean.Bridge.Framework.Core

namespace HeytingLean.Symbolic

open HeytingLean.Bridge.Framework

structure SymbolicArtifact where
  id : String
  problem : Problem
  provenance : Provenance
  tags : List String := []
  deriving Repr

namespace SymbolicArtifact

def toSMTLIB2 (a : SymbolicArtifact) : String :=
  SMT.problemToSMTLIB2 a.problem

def toTPTPFOF (a : SymbolicArtifact) : List String :=
  TPTP.problemToFOFAxioms a.id a.problem

def withTag (a : SymbolicArtifact) (tag : String) : SymbolicArtifact :=
  { a with tags := a.tags.concat tag }

end SymbolicArtifact

end HeytingLean.Symbolic
