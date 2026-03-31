import HeytingLean.VCS.FileOp
import Mathlib.Data.Finset.Basic

namespace HeytingLean
namespace VCS

/-- Result of pairwise merge:
- `merged`: same-path merge with deterministic tie-break
- `both`: disjoint-path merge retaining both ops
-/
inductive MergeResult where
  | merged (op : FileOp)
  | both (ops : Finset FileOp)
  deriving DecidableEq

/-- Deterministic resolution for same-path conflicts. -/
def resolveConflict (a b : FileOp) : FileOp :=
  if a.stableKey ≤ b.stableKey then b else a

/-- Pairwise merge:
- if operations target the same primary path, resolve deterministically
- otherwise retain both operations (commutative carrier)
-/
def merge (a b : FileOp) : MergeResult :=
  if a.primaryPath = b.primaryPath then
    .merged (resolveConflict a b)
  else
    .both ({a, b} : Finset FileOp)

end VCS
end HeytingLean
