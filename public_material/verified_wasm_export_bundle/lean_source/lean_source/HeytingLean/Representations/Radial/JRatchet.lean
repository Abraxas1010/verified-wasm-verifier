import HeytingLean.Representations.Radial.SheafStalk
import Mathlib.Data.Nat.Basic

/-!
# J-ratchet as radial expansion/collapse (scaffold)

This module provides a minimal “J-ratchet” API over a radial graph:
- `explore` consumes a bounded fuel budget and optionally moves one ring outward,
- `collapse` optionally moves one ring inward.

The fuel budget makes termination explicit and easy to test.
-/

namespace HeytingLean
namespace Representations
namespace Radial
namespace JRatchet

open HeytingLean.Representations.Radial

noncomputable section

/-- A J-state tracks the current state and a remaining exploration budget. -/
structure JState (G : RadialGraph) where
  current : G.StateIdx
  fuel : Nat
  deriving Repr

namespace JState

variable {G : RadialGraph}

/-- Explore outward by at most one ring, consuming one unit of fuel.

When no outward step exists (or the successor ring has no states), the state stays in place but
fuel is still consumed. `none` means fuel is exhausted.
-/
def explore (js : JState G) : Option (JState G) :=
  if js.fuel = 0 then
    none
  else
    let fuel' := js.fuel - 1
    match G.ringSucc? (G.ringOf js.current) with
    | none => some { js with fuel := fuel' }
    | some r' =>
        match G.stateInRing? r' with
        | none => some { js with fuel := fuel' }
        | some s' => some { current := s'.1, fuel := fuel' }

private def ringPred? (r : G.RingIdx) : Option G.RingIdx :=
  match h : r.val with
  | 0 => none
  | k + 1 =>
      some ⟨k, by
        have hk1 : k.succ < G.ringCount := by
          simpa [h] using r.isLt
        exact Nat.lt_of_succ_lt hk1⟩

/-- Collapse inward by one ring when possible (does not consume fuel). -/
def collapse (js : JState G) : JState G :=
  match ringPred? (G := G) (G.ringOf js.current) with
  | none => js
  | some r' =>
      match G.stateInRing? r' with
      | none => js
      | some s' => { js with current := s'.1 }

/-- Iterate exploration for at most `n` steps (or until fuel is exhausted). -/
def iterateExplore (js : JState G) : Nat → JState G
  | 0 => js
  | n + 1 =>
      match js.explore with
      | none => js
      | some js' => iterateExplore js' n

/-- Any successful `explore` step never increases remaining fuel. -/
lemma explore_fuel_le_of_some {js js' : JState G} (h : js.explore = some js') :
    js'.fuel ≤ js.fuel := by
  unfold explore at h
  by_cases h0 : js.fuel = 0
  · simp [h0] at h
  · simp [h0] at h
    cases hSucc : G.ringSucc? (G.ringOf js.current) with
    | none =>
        simp [hSucc] at h
        subst h
        exact Nat.sub_le _ _
    | some r =>
        cases hState : G.stateInRing? r with
        | none =>
            simp [hSucc, hState] at h
            subst h
            exact Nat.sub_le _ _
        | some s =>
            simp [hSucc, hState] at h
            subst h
            exact Nat.sub_le _ _

/-- Iterated exploration keeps fuel bounded by the initial budget. -/
theorem iterateExplore_fuel_le (js : JState G) (n : Nat) :
    (iterateExplore js n).fuel ≤ js.fuel := by
  induction n generalizing js with
  | zero =>
      simp [iterateExplore]
  | succ n ih =>
      simp [iterateExplore]
      cases hExplore : js.explore with
      | none =>
          simp
      | some js' =>
          exact le_trans (ih js') (explore_fuel_le_of_some (js := js) (js' := js') hExplore)

/-- One-step monotonicity: an extra exploration step cannot increase remaining fuel. -/
theorem iterateExplore_step_fuel_le (js : JState G) (n : Nat) :
    (iterateExplore js (n.succ)).fuel ≤ (iterateExplore js n).fuel := by
  induction n generalizing js with
  | zero =>
      simp [iterateExplore]
      cases hExplore : js.explore with
      | none =>
          simp
      | some js' =>
          simpa [hExplore] using explore_fuel_le_of_some (js := js) (js' := js') hExplore
  | succ n ih =>
      cases hExplore : js.explore with
      | none =>
          simp [iterateExplore, hExplore]
      | some js' =>
          simpa [iterateExplore, hExplore] using ih js'

/-- Remaining fuel is antitone in exploration budget. -/
theorem iterateExplore_fuel_antitone (js : JState G) :
    Antitone (fun n => (iterateExplore js n).fuel) := by
  intro n m hnm
  induction hnm with
  | refl =>
      simp
  | @step m hm ih =>
      exact le_trans (iterateExplore_step_fuel_le (js := js) (n := m)) ih

/-- Spent fuel after `n` exploration steps. -/
def spentFuel (js : JState G) (n : Nat) : Nat :=
  js.fuel - (iterateExplore js n).fuel

/-- Spent fuel is monotone in exploration budget. -/
theorem spentFuel_monotone (js : JState G) :
    Monotone (spentFuel js) := by
  intro n m hnm
  have hanti := iterateExplore_fuel_antitone (js := js) hnm
  exact Nat.sub_le_sub_left hanti js.fuel

end JState

end

end JRatchet
end Radial
end Representations
end HeytingLean
