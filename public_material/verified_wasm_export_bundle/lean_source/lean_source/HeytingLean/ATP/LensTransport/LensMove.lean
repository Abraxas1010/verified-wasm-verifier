import HeytingLean.ATP.LensTransport.FaithfulTransportGraph
import HeytingLean.ATP.DifferentiableATP.SearchTree
import HeytingLean.ATP.DifferentiableATP.CoreOps

/-
- source_type: ATP infrastructure (search move extension)
- attribution_status: n/a
- claim_status: n/a
- proof_status: proved
-/

namespace HeytingLean
namespace ATP
namespace LensTransport

open HeytingLean.Embeddings
open HeytingLean.LoF.Combinators.Differential
open HeytingLean.LoF.Combinators.Differential.Compute

/-- A search move is either a tactic application or a lens transition. -/
inductive SearchMove where
  /-- Apply a tactic in the current lens. -/
  | tactic (name : String) (combinator : Comb)
  /-- Transition to a different lens (reshapes the search space). -/
  | lensTransition (src dst : LensID)
      (safe : isSafeTransport src dst = true)


/-- A proof state annotated with its current lens. -/
structure LensProofState where
  /-- The current lens representation. -/
  currentLens : LensID
  /-- The proof state (as FSum in the current lens basis). -/
  state : FSum
  /-- The goal (as FSum in the current lens basis). -/
  goal : FSum
  /-- History of lens transitions taken to reach this state. -/
  lensHistory : List LensID
  /-- Depth in the search DAG (tactic steps + lens transitions). -/
  depth : Nat
  deriving Repr

/-- Apply a lens transition to a proof state. -/
def applyLensTransition
    (ps : LensProofState)
    (dst : LensID)
    (_hsafe : isSafeTransport ps.currentLens dst = true) :
    LensProofState where
  currentLens := dst
  state := DifferentiableATP.lensProjection dst ps.state
  goal := DifferentiableATP.lensProjection dst ps.goal
  lensHistory := dst :: ps.lensHistory
  depth := ps.depth + 1

/-- Transport a proof back to the original lens. -/
def transportProofBack?
    (proofState : LensProofState)
    (origLens : LensID)
    (proof : FSum) :
    Option FSum :=
  if proofState.currentLens == origLens then
    some proof
  else if basisSubsetB origLens proofState.currentLens then
    -- Back-transport from coarser proof lens to finer origin is an embedding.
    some proof
  else
    -- Reject lossy projection-as-proof.
    none

/-- Maximum number of lens transitions allowed in a single search path. -/
def maxLensTransitions : Nat := 3

/-- Check whether a lens transition is allowed given the search history. -/
def canTransition (ps : LensProofState) (dst : LensID) : Bool :=
  isSafeTransport ps.currentLens dst &&
  ps.lensHistory.length < maxLensTransitions &&
  dst ∉ ps.lensHistory &&
  ps.currentLens != dst

private def insertByResolutionDesc (x : LensID) : List LensID → List LensID
  | [] => [x]
  | y :: ys =>
      if DifferentiableATP.resolutionForLens x > DifferentiableATP.resolutionForLens y then
        x :: y :: ys
      else
        y :: insertByResolutionDesc x ys

private def sortByResolutionDesc (xs : List LensID) : List LensID :=
  xs.foldl (fun acc x => insertByResolutionDesc x acc) []

/-- Generate available lens moves from a proof state. -/
def availableLensMoves (ps : LensProofState) : List LensID :=
  sortByResolutionDesc <| (faithfulTargets ps.currentLens).filter (canTransition ps)

/-- Applying a lens transition increments search depth by one. -/
theorem applyLensTransition_depth (ps : LensProofState) (dst : LensID)
    (hsafe : isSafeTransport ps.currentLens dst = true) :
    (applyLensTransition ps dst hsafe).depth = ps.depth + 1 := by
  rfl

/-- Lens history grows monotonically. -/
theorem applyLensTransition_history_length (ps : LensProofState) (dst : LensID)
    (hsafe : isSafeTransport ps.currentLens dst = true) :
    (applyLensTransition ps dst hsafe).lensHistory.length = ps.lensHistory.length + 1 := by
  rfl

end LensTransport
end ATP
end HeytingLean
