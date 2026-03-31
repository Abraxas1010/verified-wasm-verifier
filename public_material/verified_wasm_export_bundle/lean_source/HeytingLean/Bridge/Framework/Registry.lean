import HeytingLean.Bridge.Framework.Core

namespace HeytingLean.Bridge.Framework

/-- Known proof assistant systems -/
inductive ProofSystem where
  | lean4
  | coq
  | isabelle
  | holLight
  | agda
  | metamath
  | mizar
  deriving Repr, DecidableEq, Inhabited

/-- Known translation pipelines -/
structure TranslationPipeline where
  source : ProofSystem
  target : ProofSystem
  toolchain : String
  trustLevel : TrustLevel
  bidirectional : Bool
  deriving Repr

/-- Known automated reasoning backends -/
inductive SolverBackend where
  | z3
  | cvc5
  | vampire
  | eprover
  | bitwuzla
  | cadical
  | kissat
  deriving Repr, DecidableEq

/-- Solver capability categories -/
inductive SolverCapability where
  | sat
  | smt
  | firstOrderATP
  | higherOrderATP
  deriving Repr, DecidableEq

/-- Exchange formats for bridge artifacts. -/
inductive BridgeFormat where
  | lean
  | coq
  | isabelle
  | holLight
  | agda
  | metamath
  | smtlib2
  | tptp
  | symbolicExpr
  | pdeSpec
  deriving Repr, DecidableEq, Inhabited

/-- Registry record for external corpora that can be imported into bridge lanes. -/
structure CorpusSource where
  id : String
  format : BridgeFormat
  url : String
  trustLevel : TrustLevel
  tags : List String := []
  deriving Repr, Inhabited

end HeytingLean.Bridge.Framework
