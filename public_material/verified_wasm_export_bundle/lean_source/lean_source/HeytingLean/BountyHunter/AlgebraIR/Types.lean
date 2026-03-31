import Lean

/-!
# HeytingLean.BountyHunter.AlgebraIR.Types

AlgebraIR is a **bilingual middle layer** between source-level IRs (e.g. Yul) and
concrete execution models (e.g. a minimal EVM semantics). The purpose of this
module is to define the smallest stable core needed for:

- canonical JSON interchange
- dominance-style safety checks (e.g. CEI)
- emitting minimal, checkable “witness” artifacts when a check fails
-/

namespace HeytingLean.BountyHunter.AlgebraIR

/-- Node identifiers are stable integers (used in JSON). -/
abbrev NodeId := Nat

/-- An operator tag. For Phase 0 we treat this as descriptive metadata:
the security checks are driven by explicit `Effect`s rather than `Op`. -/
structure Op where
  tag : String
  deriving Repr, DecidableEq, Inhabited

/-- Effects are the security-relevant events extracted from code. -/
inductive Effect where
  /-- Read from a storage slot (or other persistent slot-like resource). -/
  | storageRead (slot : Nat)
  /-- Read from a storage slot whose exact index is not a literal (e.g. mapping/struct). -/
  | storageReadDyn (slotExpr : String)
  /-- Write to a storage slot (or other persistent slot-like resource). -/
  | storageWrite (slot : Nat)
  /-- Write to a storage slot whose exact index is not a literal (e.g. mapping/struct). -/
  | storageWriteDyn (slotExpr : String)
  /-- A call boundary where control may escape (reentrancy boundary). -/
  | boundaryCall (target : String)
  deriving Repr, DecidableEq, Inhabited

/-- A node in AlgebraIR.

For Phase 0 we keep both dataflow (`args`) and control-flow (`succs`) explicit.
Dominance checks operate over control-flow (`succs`). -/
structure Node where
  id : NodeId
  op : Op
  args : Array NodeId := #[]
  effects : Array Effect := #[]
  succs : Array NodeId := #[]
  deriving Repr, DecidableEq, Inhabited

/-- A complete AlgebraIR graph. -/
structure Graph where
  version : String := "algebrair.v1"
  entry : NodeId
  exits : Array NodeId := #[]
  nodes : Array Node
  deriving Repr, DecidableEq, Inhabited

end HeytingLean.BountyHunter.AlgebraIR
