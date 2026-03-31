import HeytingLean.Bridge.Solvers.SMTEmit
import HeytingLean.Bridge.Framework.Core
import HeytingLean.Bridge.Framework.Registry

namespace HeytingLean.Bridge.Solvers

open HeytingLean.Bridge.Framework

/-- Result of a solver invocation -/
inductive SolverResult where
  | sat (model : String)
  | unsat (core : Option String)
  | unknown (reason : String)
  | timeout
  | error (msg : String)
  deriving Repr

/-- Abstract solver interface -/
structure SolverConfig where
  backend : SolverBackend
  timeout : Nat
  logic : String
  deriving Repr

/-- Record of a solver invocation for audit trail -/
structure SolverRun where
  config : SolverConfig
  query : String
  result : SolverResult
  provenance : Provenance
  deriving Repr

end HeytingLean.Bridge.Solvers
