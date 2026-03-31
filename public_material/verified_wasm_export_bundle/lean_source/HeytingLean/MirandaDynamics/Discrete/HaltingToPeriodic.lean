import Mathlib.Dynamics.PeriodicPts.Defs
import HeytingLean.MirandaDynamics.Undecidability.Transfers

/-!
# MirandaDynamics.Discrete: halting ↔ reaching a periodic orbit (fully mechanized)

The Miranda/TKFT/billiards/fluids literature often uses the pattern:

1. encode halting into a dynamical predicate (periodic orbit, reachability, etc.),
2. conclude undecidability/non-computability of the dynamical predicate.

Step (2) is easy to mechanize; Step (1) is usually geometric/PDE-heavy.

This file closes Step (1) **in a fully discrete model** (no geometry) to provide an end-to-end,
“mathematically perfect” example inside Lean:

> halting of a code `c` at input `n`  ↔  the induced discrete trajectory reaches a period-2 orbit.

This gives a concrete, verifiable reduction from the halting predicate to a periodic-orbit
predicate and then applies the general undecidability-transfer lemma.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Discrete

open Nat.Partrec
open Nat.Partrec.Code

/-! ## The discrete dynamical system (parameterized by `c` and input `n`) -/

/-- States either search for a halting witness (with counter `k`) or toggle on a 2-cycle. -/
abbrev State : Type :=
  Sum Nat Bool

/-- One step of the dynamical system: increment the counter until `evaln` succeeds, then enter a
2-cycle forever. -/
def step (n : Nat) (c : Code) : State → State
  | Sum.inl k =>
    match evaln k c n with
    | Option.none => Sum.inl (k + 1)
    | Option.some _ => Sum.inr false
  | Sum.inr b => Sum.inr (!b)

/-- Canonical initial state. -/
def start : State :=
  Sum.inl 0

/-! ## Step-indexed “hit” predicate -/

/-- The evaluator returns `some` output by time bound `k`. -/
def HitsAt (n : Nat) (c : Code) (k : Nat) : Prop :=
  ∃ x : Nat, evaln k c n = some x

instance (n : Nat) (c : Code) (k : Nat) : Decidable (HitsAt n c k) := by
  unfold HitsAt
  cases h : evaln k c n with
  | none =>
    refine isFalse ?_
    rintro ⟨x, hx⟩
    cases hx
  | some x =>
    refine isTrue ?_
    exact ⟨x, rfl⟩

theorem not_hitsAt_iff_evaln_eq_none (n : Nat) (c : Code) (k : Nat) :
    ¬HitsAt n c k ↔ evaln k c n = Option.none := by
  constructor
  · intro h
    cases hk : evaln k c n with
    | none => rfl
    | some x =>
      exfalso
      exact h ⟨x, hk⟩
  · intro hk h
    rcases h with ⟨x, hx⟩
    simp [hk] at hx

/-! ## Trajectory facts -/

theorem iterate_step_inl_of_noHitsBefore (n : Nat) (c : Code) :
    ∀ t : Nat, (∀ i < t, ¬HitsAt n c i) → (step n c)^[t] start = Sum.inl t
  | 0, _ => rfl
  | t + 1, hNo => by
    have hNo' : ∀ i < t, ¬HitsAt n c i := fun i hi => hNo i (Nat.lt_succ_of_lt hi)
    have ht : ¬HitsAt n c t := hNo t (Nat.lt_succ_self t)
    have htNone : evaln t c n = Option.none := (not_hitsAt_iff_evaln_eq_none n c t).1 ht
    have hPrev : (step n c)^[t] start = Sum.inl t :=
      iterate_step_inl_of_noHitsBefore n c t hNo'
    calc
      (step n c)^[t + 1] start = step n c ((step n c)^[t] start) := by
        simp [Function.iterate_succ_apply']
      _ = step n c (Sum.inl t) := by simp [hPrev]
      _ = Sum.inl (t + 1) := by
        simp [step, htNone]

/-- Mathlib halting predicate ↔ existence of an `evaln` witness. -/
theorem halts_iff_exists_evaln (n : Nat) (c : Code) :
    Undecidability.Halting.Halts n c ↔ ∃ k x, evaln k c n = some x := by
  -- `Halts n c` is `((Code.eval c n).Dom)`.
  unfold Undecidability.Halting.Halts
  constructor
  · intro hDom
    rcases (Part.dom_iff_mem.1 hDom) with ⟨x, hx⟩
    rcases (evaln_complete (c := c) (n := n) (x := x)).1 hx with ⟨k, hk⟩
    refine ⟨k, x, ?_⟩
    simpa [Option.mem_def] using hk
  · rintro ⟨k, x, hk⟩
    have hk' : x ∈ evaln k c n := by
      simpa [Option.mem_def] using hk
    have hx : x ∈ eval c n := evaln_sound hk'
    exact (Part.dom_iff_mem.2 ⟨x, hx⟩)

/-! ## Periodic-orbit reachability -/

/-- The orbit reaches a period-2 point (i.e. a periodic orbit of length dividing 2). -/
def ReachesPeriod2 (n : Nat) (c : Code) : Prop :=
  ∃ t : Nat, Function.IsPeriodicPt (step n c) 2 ((step n c)^[t] start)

theorem periodic2_inr (n : Nat) (c : Code) (b : Bool) :
    Function.IsPeriodicPt (step n c) 2 (Sum.inr b) := by
  -- `f^[2] (inr b) = inr b` because the `inr` branch toggles.
  dsimp [Function.IsPeriodicPt, Function.IsFixedPt]
  -- expand the `2`-fold iterate
  simp [step]

theorem not_periodic2_inl (n : Nat) (c : Code) (k : Nat) :
    ¬Function.IsPeriodicPt (step n c) 2 (Sum.inl k) := by
  -- compute `step^[2] (inl k)` and show it cannot equal `inl k`
  intro hper
  -- Unfold periodicity to an equality.
  have hEq : (step n c)^[2] (Sum.inl k) = Sum.inl k := by
    simpa [Function.IsPeriodicPt, Function.IsFixedPt] using hper
  have h2 : (step n c)^[2] (Sum.inl k) = step n c (step n c (Sum.inl k)) := by
    simp [Function.iterate_succ_apply']
  -- Evaluate the first step by cases; either way the second iterate cannot return to `inl k`.
  cases hk : evaln k c n with
  | none =>
    -- first step goes to `inl (k+1)`; second step either goes to `inl (k+2)` or to `inr false`.
    cases hk1 : evaln (k + 1) c n with
    | none =>
      have hIter : (step n c)^[2] (Sum.inl k) = Sum.inl (k + 2) := by
        simp [h2, step, hk, hk1]
      -- contradiction since `k+2 ≠ k`
      have hEqState : (Sum.inl (k + 2) : State) = Sum.inl k :=
        hIter.symm.trans hEq
      have hNat : k + 2 = k :=
        Sum.inl.inj hEqState
      exact (Nat.ne_of_gt (Nat.lt_add_of_pos_right (n := k) (by decide : 0 < 2))) hNat
    | some x =>
      have hIter : (step n c)^[2] (Sum.inl k) = Sum.inr false := by
        simp [h2, step, hk, hk1]
      -- contradiction: `inr` never equals `inl`
      have hContra : (Sum.inr false : State) = Sum.inl k :=
        hIter.symm.trans hEq
      cases hContra
  | some x =>
    -- first step goes to `inr false`, second step to `inr true`; cannot equal `inl k`.
    have hIter : (step n c)^[2] (Sum.inl k) = Sum.inr true := by
      simp [h2, step, hk]
    have hContra : (Sum.inr true : State) = Sum.inl k :=
      hIter.symm.trans hEq
    cases hContra

theorem reachesPeriod2_of_halting (n : Nat) (c : Code) :
    Undecidability.Halting.Halts n c → ReachesPeriod2 n c := by
  intro hHalts
  -- Find the first `k` where `evaln` returns `some`.
  have hex : ∃ k, HitsAt n c k := by
    rcases (halts_iff_exists_evaln n c).1 hHalts with ⟨k, x, hk⟩
    exact ⟨k, x, hk⟩
  let k0 : Nat := Nat.find hex
  have hk0 : HitsAt n c k0 := Nat.find_spec hex
  have hNo : ∀ i < k0, ¬HitsAt n c i := by
    intro i hi
    exact Nat.find_min hex (by simpa [k0] using hi)
  -- At time `k0` we are still in the `inl` branch.
  have hAt : (step n c)^[k0] start = Sum.inl k0 :=
    iterate_step_inl_of_noHitsBefore n c k0 (fun i hi => hNo i hi)
  -- The next step enters the 2-cycle.
  rcases hk0 with ⟨x, hk0x⟩
  have hNext : (step n c)^[k0 + 1] start = Sum.inr false := by
    -- unfold one iteration step
    simp [Function.iterate_succ_apply', hAt, step, hk0x]
  -- Therefore we reach a period-2 point.
  refine ⟨k0 + 1, ?_⟩
  -- rewrite to the concrete cycle point and use periodicity.
  simpa [hNext] using (periodic2_inr n c false)

theorem halting_of_reachesPeriod2 (n : Nat) (c : Code) :
    ReachesPeriod2 n c → Undecidability.Halting.Halts n c := by
  intro hReach
  -- Contrapositive: if there is no halting witness, the orbit stays on distinct `inl k` states.
  by_contra hNotHalts
  have hNoHitAll : ∀ k, ¬HitsAt n c k := by
    intro k hk
    rcases hk with ⟨x, hkx⟩
    exact hNotHalts ((halts_iff_exists_evaln n c).2 ⟨k, x, hkx⟩)
  rcases hReach with ⟨t, ht⟩
  -- The state at time `t` is necessarily `inl t`, hence cannot be period-2.
  have hState : (step n c)^[t] start = Sum.inl t :=
    iterate_step_inl_of_noHitsBefore n c t (fun i hi => hNoHitAll i)
  have : ¬Function.IsPeriodicPt (step n c) 2 ((step n c)^[t] start) := by
    simpa [hState] using not_periodic2_inl n c t
  exact this ht

theorem reachesPeriod2_iff_halts (n : Nat) (c : Code) :
    ReachesPeriod2 n c ↔ Undecidability.Halting.Halts n c :=
  ⟨halting_of_reachesPeriod2 n c, reachesPeriod2_of_halting n c⟩

/-! ## Many-one reduction + non-computability consequence -/

/-- In this discrete model, the halting predicate many-one reduces to reaching a period-2 orbit. -/
def haltingReducesToReachesPeriod2 (n : Nat) :
    Undecidability.ManyOne (p := Undecidability.Halting.Halts n) (q := fun c : Code => ReachesPeriod2 n c) where
  f := id
  computable_f := Computable.id
  correct := fun c => (reachesPeriod2_iff_halts n c).symm

theorem not_computable_reachesPeriod2 (n : Nat) :
    ¬ComputablePred (fun c : Code => ReachesPeriod2 n c) :=
  Undecidability.Halting.not_computable_of_halting_reduces (n := n) (haltingReducesToReachesPeriod2 n)

end Discrete
end MirandaDynamics
end HeytingLean
