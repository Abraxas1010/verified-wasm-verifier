/-
Copyright (c) 2026 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

import HeytingLean.HeytingVeil.ModelCheck.Decidable
import HeytingLean.HeytingVeil.Verify.Core

/-!
# BFS Model Checker

Executable bounded reachability + CTI extraction.
-/

namespace HeytingLean
namespace HeytingVeil
namespace ModelCheck

open HeytingLean.HeytingVeil.Temporal
open HeytingLean.HeytingVeil.Verify

universe u

private def insertNew {α : Type u} [DecidableEq α] (xs ys : List α) : List α :=
  ys.foldl (fun acc y => if y ∈ acc then acc else acc ++ [y]) xs

private def bfsStep {State : Type u} [DecidableEq State]
    (dm : DecidableMachine State) (visited frontier : List State) : List State × List State :=
  let nextRaw := frontier.foldl (fun acc s => acc ++ successors dm s) []
  let next := nextRaw.filter (fun s => s ∉ visited) |>.eraseDups
  (insertNew visited next, next)

/-- BFS reachability from initial states up to `bound` expansions. -/
def bfsReachable {State : Type u} [DecidableEq State]
    (dm : DecidableMachine State) (bound : Nat) : List State :=
  let start := (initStates dm).eraseDups
  let rec go : Nat → List State → List State → List State
    | 0, visited, _ => visited
    | _ + 1, visited, [] => visited
    | k + 1, visited, frontier =>
        let (visited', frontier') := bfsStep dm visited frontier
        go k visited' frontier'
  go bound start start

private def findCTIOnSuccs {State : Type u} [DecidableEq State]
    (dm : DecidableMachine State) (dc : DecidableInvCandidate State)
    (pre : State) : List State → Option (CTI dm.machine dc.inv)
  | [] => none
  | nxt :: rest =>
      haveI : Decidable (dc.inv pre) := dc.decInv pre
      if hpre : dc.inv pre then
        haveI : Decidable (dm.machine.Step pre nxt) := dm.decStep pre nxt
        if hstep : dm.machine.Step pre nxt then
          haveI : Decidable (dc.inv nxt) := dc.decInv nxt
          if hnot : ¬ dc.inv nxt then
            some
              { pre := pre
                next := nxt
                pre_inv := hpre
                step := hstep
                next_not_inv := hnot }
          else
            findCTIOnSuccs dm dc pre rest
        else
          findCTIOnSuccs dm dc pre rest
      else
        none

private def findCTIOnReachable {State : Type u} [DecidableEq State]
    (dm : DecidableMachine State) (dc : DecidableInvCandidate State) :
    List State → Option (CTI dm.machine dc.inv)
  | [] => none
  | pre :: rest =>
      match findCTIOnSuccs dm dc pre (successors dm pre) with
      | some cti => some cti
      | none => findCTIOnReachable dm dc rest

/-- Find a CTI edge over the bounded reachable region. -/
def findCTIReachable {State : Type u} [DecidableEq State]
    (dm : DecidableMachine State) (dc : DecidableInvCandidate State) (bound : Nat) :
    Option (CTI dm.machine dc.inv) :=
  findCTIOnReachable dm dc (bfsReachable dm bound)

/-- Any CTI found by reachable-state BFS refutes one-step inductiveness. -/
theorem findCTIReachable_sound {State : Type u} [DecidableEq State]
    {dm : DecidableMachine State} {dc : DecidableInvCandidate State}
    {bound : Nat} {cti : CTI dm.machine dc.inv}
    (_h : findCTIReachable dm dc bound = some cti) :
    ¬ (∀ s t : State, dc.inv s → dm.machine.Step s t → dc.inv t) := by
  exact cti_breaks_inductiveness cti

/-- Bounded completeness witness: `none` means no CTI was discovered in explored states. -/
def noCTIWithinBound {State : Type u} [DecidableEq State]
    (dm : DecidableMachine State) (dc : DecidableInvCandidate State) (bound : Nat) : Prop :=
  findCTIReachable dm dc bound = none

end ModelCheck
end HeytingVeil
end HeytingLean
