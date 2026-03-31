/-
Copyright (c) 2026 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

import HeytingLean.HeytingVeil.ModelCheck.BFS

/-!
# Verify / Refine Loop (bounded)

Computable CTI-refinement loop over bounded reachable states.
-/

namespace HeytingLean
namespace HeytingVeil
namespace ModelCheck

universe u

/-- Lightweight unresolved CTI edge witness. -/
structure CTIEdgeWitness (State : Type u) where
  pre : State
  next : State
  deriving Repr

/-- Summary of the bounded refinement loop. -/
structure VerifyRefineSummary (State : Type u) where
  refinements : Nat
  blockedStates : List State
  unresolvedCTI : Option (CTIEdgeWitness State)
  deriving Repr

private def blockedInvariant {State : Type u} [DecidableEq State]
    (base : State → Prop) (blocked : List State) : State → Prop :=
  fun s => base s ∧ s ∉ blocked

private def blockedCandidate {State : Type u} [DecidableEq State]
    (dc : DecidableInvCandidate State) (blocked : List State) : DecidableInvCandidate State :=
  {
    inv := blockedInvariant dc.inv blocked
    decInv := by
      intro s
      dsimp [blockedInvariant]
      haveI : Decidable (dc.inv s) := dc.decInv s
      infer_instance
  }

private def loop {State : Type u} [DecidableEq State]
    (dm : DecidableMachine State)
    (dc : DecidableInvCandidate State)
    (bound : Nat)
    (fuel : Nat)
    (blocked : List State)
    (refinements : Nat) : VerifyRefineSummary State :=
  let cand := blockedCandidate dc blocked
  match findCTIReachable dm cand bound with
  | none =>
      { refinements := refinements
        blockedStates := blocked
        unresolvedCTI := none }
  | some cti =>
      match fuel with
      | 0 =>
          { refinements := refinements
            blockedStates := blocked
            unresolvedCTI := some { pre := cti.pre, next := cti.next } }
      | n + 1 =>
          let blocked' := if cti.next ∈ blocked then blocked else blocked ++ [cti.next]
          loop dm dc bound n blocked' (refinements + 1)

/-- Execute bounded verify/refine loop and either close CTIs or return unresolved edge. -/
def verifyRefineLoop {State : Type u} [DecidableEq State]
    (dm : DecidableMachine State)
    (dc : DecidableInvCandidate State)
    (bound : Nat)
    (maxRefinements : Nat) : VerifyRefineSummary State :=
  loop dm dc bound maxRefinements [] 0

end ModelCheck
end HeytingVeil
end HeytingLean
