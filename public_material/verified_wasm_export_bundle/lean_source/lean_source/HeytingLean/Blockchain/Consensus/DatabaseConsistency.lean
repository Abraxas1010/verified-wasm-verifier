namespace HeytingLean
namespace Blockchain
namespace Consensus
namespace DatabaseConsistency

/-- Simple key type for the example consensus database model. -/
abbrev Key := String

/-- Simple value type for the example database model. -/
abbrev Value := Int

/-- Database state as a total map from keys to values. -/
structure DBState where
  data : Key → Value

namespace DBState

/-- Empty database state: every key maps to `0`. -/
def empty : DBState :=
  { data := fun _ => 0 }

/-- Read the value associated with a key in the database state. -/
def read (s : DBState) (k : Key) : Value :=
  s.data k

/-- Write a value for a key, shadowing any previous value. -/
def write (s : DBState) (k : Key) (v : Value) : DBState :=
  { data := fun k' => if k' = k then v else s.data k' }

end DBState

/-- Example database operations: currently a single write operation. -/
inductive Op where
  | write (k : Key) (v : Value)
  deriving Repr

open Op

/-- Apply a list of operations to an initial database state. -/
def applyOps (ops : List Op) (s : DBState) : DBState :=
  ops.foldl
    (fun st op =>
      match op with
      | .write k v => DBState.write st k v)
    s

/-- Log-based value for a key after executing the operations from the
    empty state. In this minimal model, it is defined directly via
    `applyOps` and `DBState.read`. -/
def logValue (ops : List Op) (k : Key) : Value :=
  DBState.read (applyOps ops DBState.empty) k

/-- Database-consistency statement: for every operation log and key,
    reading from the database after applying the log from the empty
    state agrees with the log-based value. -/
def Statement : Prop :=
  ∀ (ops : List Op) (k : Key),
    DBState.read (applyOps ops DBState.empty) k =
      logValue ops k

/-- The example database model satisfies `Statement` by construction. -/
theorem statement_holds : Statement := by
  intro ops k
  rfl

end DatabaseConsistency
end Consensus
end Blockchain
end HeytingLean
