import HeytingLean.Information.Dynamics

/-!
# Information as distinction: proof-trace layer

This module encodes the “dynamics run” as an inductive proof object.

The key statement is that the structural size of such a proof object (counting inductive
`step` constructors) matches the `Nat` index carried by the proposition.
-/

namespace HeytingLean
namespace Information

open HeytingLean.LoF
open scoped Classical

/-- Proof object certifying that an initial `InfoState` reaches a stable point in `n` steps.

The stability predicate is `Dynamics.IsStable`, i.e. fixed by the nucleus, non-bottom, and inside
the re-entry support window.
-/
inductive ReachesFixedPoint
    {α : Type _} [PrimaryAlgebra α]
    (R : Reentry α) (interpret : InfoState → α) :
    InfoState → α → Nat → Type
  | stable (s : InfoState) (h : IsStable R (interpret s)) :
      ReachesFixedPoint R interpret s (interpret s) 0
  | step (s : InfoState) {a : α} {n : Nat}
      (h : ¬ IsStable R (interpret s))
      (p : ReachesFixedPoint R interpret (InfoState.step s) a n) :
      ReachesFixedPoint R interpret s a (n + 1)

namespace ReachesFixedPoint

/-- Count the number of `step` constructors in a `ReachesFixedPoint` certificate. -/
def structuralInformation
    {α : Type _} [PrimaryAlgebra α]
    {R : Reentry α} {interpret : InfoState → α}
    {s : InfoState} {a : α} {n : Nat} :
    ReachesFixedPoint R interpret s a n → Nat
  | stable _ _ => 0
  | step _ _ p => structuralInformation p + 1

/-- Main theorem: the proof-trace “size” equals the time index. -/
theorem information_is_dynamics
    {α : Type _} [PrimaryAlgebra α]
    {R : Reentry α} {interpret : InfoState → α}
    {s : InfoState} {a : α} {n : Nat}
    (p : ReachesFixedPoint R interpret s a n) :
    structuralInformation p = n := by
  induction p with
  | stable => rfl
  | step _ _ p ih =>
      simp [ReachesFixedPoint.structuralInformation, ih]

end ReachesFixedPoint

/-! ## Certified runner -/

structure RunResult
    {α : Type _} [PrimaryAlgebra α]
    (R : Reentry α) (interpret : InfoState → α) (s : InfoState) where
  steps : Nat
  final : α
  cert : ReachesFixedPoint R interpret s final steps

/-- Fuel-bounded run that returns a certificate if it succeeds. -/
noncomputable def runUntilStableCertified?
    {α : Type _} [PrimaryAlgebra α]
    (R : Reentry α) (interpret : InfoState → α) :
    Nat → (s : InfoState) → Option (RunResult R interpret s)
  | 0, _ => none
  | fuel + 1, s =>
      let a := interpret s
      if h : IsStable R a then
        some ⟨0, a, ReachesFixedPoint.stable (R := R) (interpret := interpret) s h⟩
      else
        match runUntilStableCertified? R interpret fuel (InfoState.step s) with
        | none => none
        | some r =>
            some
              ⟨r.steps + 1,
               r.final,
               ReachesFixedPoint.step (R := R) (interpret := interpret) s h r.cert⟩

end Information
end HeytingLean
