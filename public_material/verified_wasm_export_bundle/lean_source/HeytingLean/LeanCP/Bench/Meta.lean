import HeytingLean.LeanCP.VCG.SWP

namespace HeytingLean.LeanCP.Bench

open HeytingLean.LeanCP

inductive BenchDomain where
  | scalarArith
  | arraySearchSort
  | linkedHeap
  | treeHash
  | callsControlRec
  | stringMemorySystem
  deriving DecidableEq, Repr, Inhabited

inductive BenchProofKind where
  | symbolic
  | invariant
  | recursive
  | callAware
  | operational
  deriving DecidableEq, Repr, Inhabited

inductive BenchGenerality where
  | smokeOnly
  | concreteOperational
  | parametric
  | familyGeneric
  deriving DecidableEq, Repr, Inhabited

structure BenchEntry where
  id : String
  domain : BenchDomain
  moduleName : String
  theoremDecl : Lean.Name
  programDecl : Lean.Name
  entryKind : String
  proofKind : BenchProofKind
  generality : BenchGenerality
  usesAnnotations : Bool
  countsTowardPhase8 : Bool
  exclusionReason? : Option String := none
  deriving DecidableEq, Repr, Inhabited

def BenchEntry.isCounted (entry : BenchEntry) : Bool :=
  entry.countsTowardPhase8

def domainLabel : BenchDomain → String
  | .scalarArith => "scalar-arithmetic"
  | .arraySearchSort => "array-search-sort"
  | .linkedHeap => "linked-heap"
  | .treeHash => "tree-hash"
  | .callsControlRec => "calls-control-rec"
  | .stringMemorySystem => "string-memory-system"

end HeytingLean.LeanCP.Bench
