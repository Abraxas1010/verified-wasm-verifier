import Mathlib.Data.List.Basic

namespace HeytingLean
namespace Numbers
namespace Surreal

/-!
# Rank-indexed games (finite Day)

This module defines a finite-Day family of games `GameN n` and a cumulative
type `Game := Sigma GameN` with basic accessors for left/right options.
-/

/-- Finite-Day games. -/
inductive GameN : Nat -> Type
| mk0 : GameN 0
| succ {n : Nat} (L R : List (Sigma GameN)) : GameN (n + 1)

/-- Cumulative game with Day tagged in the sigma. -/
abbrev Game := Sigma GameN

namespace Game

/-- Day of a cumulative game. -/
def day (g : Game) : Nat := g.fst

private def keepUnder (bound : Nat) (s : Sigma GameN) : Option Game :=
  if _ : s.1 < bound then some ⟨s.1, s.2⟩ else none

/-- Left options as a list of cumulative games. -/
def L (g : Game) : List Game :=
  match g with
  | ⟨0, .mk0⟩ => []
  | ⟨Nat.succ n, .succ L _⟩ => L.filterMap (keepUnder (Nat.succ n))

/-- Right options as a list of cumulative games. -/
def R (g : Game) : List Game :=
  match g with
  | ⟨0, .mk0⟩ => []
  | ⟨Nat.succ n, .succ _ R⟩ => R.filterMap (keepUnder (Nat.succ n))

@[simp] theorem L_zero : L ⟨0, GameN.mk0⟩ = [] := rfl
@[simp] theorem R_zero : R ⟨0, GameN.mk0⟩ = [] := rfl

theorem mem_L_day_lt {x l : Game} (h : l ∈ L x) : l.day < x.day := by
  cases x with
  | mk d gd =>
    cases d with
    | zero =>
      cases gd with
      | mk0 =>
        simp [L] at h
    | succ n =>
      cases gd with
      | succ Ls Rs =>
        dsimp [L, keepUnder] at h
        rcases List.mem_filterMap.mp h with ⟨s, _, hsSome⟩
        have hslt : s.1 < Nat.succ n := by
          by_cases hs : s.1 < Nat.succ n
          · exact hs
          · simp [keepUnder, hs] at hsSome
        have hsEq : (⟨s.1, s.2⟩ : Game) = l := by
          simpa [keepUnder, hslt] using hsSome
        have hday : l.day = s.1 := by
          simpa [Game.day] using congrArg Sigma.fst hsEq.symm
        exact hday ▸ hslt

theorem mem_R_day_lt {x r : Game} (h : r ∈ R x) : r.day < x.day := by
  cases x with
  | mk d gd =>
    cases d with
    | zero =>
      cases gd with
      | mk0 =>
        simp [R] at h
    | succ n =>
      cases gd with
      | succ Ls Rs =>
        dsimp [R, keepUnder] at h
        rcases List.mem_filterMap.mp h with ⟨s, _, hsSome⟩
        have hslt : s.1 < Nat.succ n := by
          by_cases hs : s.1 < Nat.succ n
          · exact hs
          · simp [keepUnder, hs] at hsSome
        have hsEq : (⟨s.1, s.2⟩ : Game) = r := by
          simpa [keepUnder, hslt] using hsSome
        have hday : r.day = s.1 := by
          simpa [Game.day] using congrArg Sigma.fst hsEq.symm
        exact hday ▸ hslt

theorem mem_L_day_le {x l : Game} (h : l ∈ L x) : l.day ≤ x.day :=
  Nat.le_of_lt (mem_L_day_lt h)

theorem mem_R_day_le {x r : Game} (h : r ∈ R x) : r.day ≤ x.day :=
  Nat.le_of_lt (mem_R_day_lt h)

end Game

open Game

/-- Budgeted comparison: `leAtN k x y` computes `x ≤ y` up to budget `k`. -/
noncomputable def leAtN : Nat -> Game -> Game -> Prop
  | 0, _, _ => True
  | Nat.succ k, x, y =>
      (∀ l ∈ x.L, ¬ leAtN k y l) ∧ (∀ r ∈ y.R, ¬ leAtN k r x)

@[simp] theorem leAtN_zero (x y : Game) : leAtN 0 x y := by
  trivial

@[simp] theorem leAtN_succ (k : Nat) (x y : Game) :
    leAtN (k + 1) x y ↔
      (∀ l ∈ x.L, ¬ leAtN k y l) ∧ (∀ r ∈ y.R, ¬ leAtN k r x) := Iff.rfl

/-- Finite-Day order: `x ≤ y` at budget `x.day + y.day`. -/
noncomputable def leN (x y : Game) : Prop :=
  leAtN (x.day + y.day) x y

/-- Strict order derived from `≤` by asymmetry. -/
noncomputable def ltN (x y : Game) : Prop := ¬ leN y x

/-- Classical cut legality for a finite-Day game. -/
noncomputable def legalN (g : Game) : Prop :=
  ∀ l : Game, l ∈ g.L -> ∀ r : Game, r ∈ g.R -> ltN l r

@[simp] theorem legalN_zero : legalN ⟨0, GameN.mk0⟩ := by
  intro l hl
  have hfalse : False := by
    simp [Game.L_zero] at hl
  exact False.elim hfalse

end Surreal
end Numbers
end HeytingLean
