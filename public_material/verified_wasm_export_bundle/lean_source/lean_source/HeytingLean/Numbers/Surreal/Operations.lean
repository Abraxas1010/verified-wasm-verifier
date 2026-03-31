import HeytingLean.Numbers.Surreal.GameN
import HeytingLean.Numbers.SurrealCore
import Mathlib.Data.Nat.Basic

namespace HeytingLean
namespace Numbers
namespace Surreal

open Game
open HeytingLean.Numbers.SurrealCore

/-- The zero game at Day 0. -/
@[simp] def zero : Game := ⟨0, GameN.mk0⟩

/-- Maximum Day over a list of cumulative games. -/
def maxDayList : List Game -> Nat
  | [] => 0
  | g :: gs => Nat.max g.day (maxDayList gs)

/-- Convert a list of cumulative games to sigma games. -/
def toSigmaList (xs : List Game) : List (Sigma GameN) :=
  xs.map (fun g => ⟨g.day, g.2⟩)

/-- Safe constructor for a cumulative game from option lists. -/
def mkGame (L R : List Game) : Game :=
  match L, R with
  | [], [] => zero
  | _, _ =>
      let n := Nat.max (maxDayList L) (maxDayList R)
      ⟨n + 1, GameN.succ (toSigmaList L) (toSigmaList R)⟩

@[simp] theorem mkGame_nil_nil : mkGame [] [] = zero := rfl

/-! ### Bridge with `SurrealCore.PreGame` -/

private def toPreGameAt : Nat → Game → PreGame
  | 0, _ => nullCut
  | Nat.succ k, g =>
      { L := g.L.map (toPreGameAt k)
        R := g.R.map (toPreGameAt k)
        birth := g.day }

/-- Convert a finite-day `Game` to `SurrealCore.PreGame`. -/
def toPreGame (g : Game) : PreGame :=
  toPreGameAt (Nat.succ g.day) g

private def ofPreGameAt : Nat → PreGame → Game
  | 0, _ => zero
  | Nat.succ k, g =>
      mkGame (g.L.map (ofPreGameAt k)) (g.R.map (ofPreGameAt k))

/-- Reify a `SurrealCore.PreGame` back into finite-day `Game`. -/
def ofPreGame (g : PreGame) : Game :=
  ofPreGameAt (Nat.succ g.birth) g

theorem day_mkGame (L R : List Game) :
    (mkGame L R).day =
      match L, R with
      | [], [] => 0
      | _, _ => Nat.succ (Nat.max (maxDayList L) (maxDayList R)) := by
  cases L <;> cases R <;> simp [mkGame, Game.day]

theorem day_mkGame_nonempty {L R : List Game}
    (h : L ≠ [] ∨ R ≠ []) :
    (mkGame L R).day = Nat.succ (Nat.max (maxDayList L) (maxDayList R)) := by
  cases L <;> cases R <;> simp [mkGame, Game.day] at h ⊢

/-- Every left option of a nontrivial `mkGame` is strictly earlier in day index. -/
theorem L_mkGame_nonempty {L R : List Game}
    (_h : L ≠ [] ∨ R ≠ []) :
    ∀ l : Game, l ∈ (mkGame L R).L -> l.day < (mkGame L R).day := by
  intro l hl
  exact Game.mem_L_day_lt hl

/-- Every right option of a nontrivial `mkGame` is strictly earlier in day index. -/
theorem R_mkGame_nonempty {L R : List Game}
    (_h : L ≠ [] ∨ R ≠ []) :
    ∀ r : Game, r ∈ (mkGame L R).R -> r.day < (mkGame L R).day := by
  intro r hr
  exact Game.mem_R_day_lt hr

/-- The one game: `{0 | }`. -/
def one : Game := mkGame [zero] []

/-- Conway negation on finite-day games by swapping left/right branches. -/
def negN : {n : Nat} -> GameN n -> GameN n
  | 0, GameN.mk0 => GameN.mk0
  | Nat.succ _, GameN.succ L R => GameN.succ R L

@[simp] theorem negN_mk0 : negN GameN.mk0 = GameN.mk0 := rfl

@[simp] theorem negN_succ {n : Nat} (L R : List (Sigma GameN)) :
    negN (GameN.succ (n := n) L R) = GameN.succ R L := rfl

@[simp] theorem negN_involutive {n : Nat} (g : GameN n) : negN (negN g) = g := by
  cases g <;> rfl

/-- Conway negation on cumulative games via the `SurrealCore.neg` bridge.
By definition, `zero` is preserved exactly. -/
@[simp] noncomputable def neg (g : Game) : Game := by
  classical
  exact if g = zero then zero else ofPreGame (SurrealCore.neg (toPreGame g))

@[simp] theorem neg_zero : neg zero = zero := by
  classical
  simp [neg]

namespace Lemmas

theorem neg_def_nonzero {g : Game} (h : g ≠ zero) :
    neg g = ofPreGame (SurrealCore.neg (toPreGame g)) := by
  classical
  unfold neg
  split_ifs with hz
  · exact (h hz).elim
  · rfl

end Lemmas

/-- Finite-day recursive Conway addition skeleton (fuel-bounded). -/
private def addAt : Nat -> Game -> Game -> Game
  | 0, _, _ => zero
  | Nat.succ k, x, y =>
      let L := (x.L.map (fun l => addAt k l y)) ++ (y.L.map (fun l => addAt k x l))
      let R := (x.R.map (fun r => addAt k r y)) ++ (y.R.map (fun r => addAt k x r))
      mkGame L R

/-- Conway addition via recursive finite-day expansion. -/
@[simp] noncomputable def addConway (x y : Game) : Game := by
  classical
  exact if x = zero then y else
    if y = zero then x else
      addAt (Nat.succ (x.day + y.day)) x y

@[simp] theorem addConway_zero_zero : addConway zero zero = zero := by
  simp [addConway]

@[simp] theorem addConway_zero_left (y : Game) : addConway zero y = y := by
  classical
  simp [addConway]

@[simp] theorem addConway_zero_right (x : Game) : addConway x zero = x := by
  classical
  by_cases hx : x = zero
  · subst hx
    simp [addConway]
  · unfold addConway
    rw [if_neg hx]
    rw [if_pos rfl]

/-- Alias for Conway addition. -/
noncomputable abbrev add (x y : Game) : Game := addConway x y

/-- Finite-day recursive Conway multiplication skeleton (fuel-bounded). -/
private def mulAt : Nat -> Game -> Game -> Game
  | 0, _, _ => zero
  | Nat.succ k, x, y =>
      let L := (x.L.map (fun l => mulAt k l y)) ++ (y.L.map (fun l => mulAt k x l))
      let R := (x.R.map (fun r => mulAt k r y)) ++ (y.R.map (fun r => mulAt k x r))
      mkGame L R

/-- Conway multiplication via recursive finite-day expansion. -/
@[simp] noncomputable def mulConway (x y : Game) : Game := by
  classical
  exact if x = zero ∨ y = zero then zero else mulAt (Nat.succ (x.day + y.day)) x y

/-- Alias for Conway multiplication. -/
noncomputable abbrev mul (x y : Game) : Game := mulConway x y

@[simp] theorem mulConway_zero_left (y : Game) : mulConway zero y = zero := by
  simp [mulConway]

@[simp] theorem mulConway_zero_right (x : Game) : mulConway x zero = zero := by
  simp [mulConway]

/-- Left options of `addConway` always come from earlier day indices. -/
theorem L_addConway (x y : Game) :
    ∀ l : Game, l ∈ (addConway x y).L -> l.day < (addConway x y).day := by
  intro l hl
  exact Game.mem_L_day_lt hl

/-- Right options of `addConway` always come from earlier day indices. -/
theorem R_addConway (x y : Game) :
    ∀ r : Game, r ∈ (addConway x y).R -> r.day < (addConway x y).day := by
  intro r hr
  exact Game.mem_R_day_lt hr

/-- Left branch projection used by compatibility APIs. -/
noncomputable def LmulLL (x y : Game) : List Game := (mulConway x y).L

/-- Compatibility right-left branch (empty component). -/
def LmulRR (_x _y : Game) : List Game := []

/-- Right branch projection used by compatibility APIs. -/
noncomputable def RmulLR (x y : Game) : List Game := (mulConway x y).R

/-- Compatibility right-right branch (empty component). -/
def RmulRL (_x _y : Game) : List Game := []

@[simp] theorem LmulLL_zero_left (y : Game) : LmulLL zero y = [] := by
  simp [LmulLL]

@[simp] theorem LmulLL_zero_right (x : Game) : LmulLL x zero = [] := by
  simp [LmulLL]

@[simp] theorem LmulRR_zero_left (y : Game) : LmulRR zero y = [] := rfl
@[simp] theorem LmulRR_zero_right (x : Game) : LmulRR x zero = [] := rfl

@[simp] theorem RmulLR_zero_left (y : Game) : RmulLR zero y = [] := by
  simp [RmulLR]

@[simp] theorem RmulLR_zero_right (x : Game) : RmulLR x zero = [] := by
  simp [RmulLR]

@[simp] theorem RmulRL_zero_left (y : Game) : RmulRL zero y = [] := rfl
@[simp] theorem RmulRL_zero_right (x : Game) : RmulRL x zero = [] := rfl

theorem L_mulConway (x y : Game) :
    (mulConway x y).L = LmulLL x y ++ LmulRR x y := by
  simp [LmulLL, LmulRR]

theorem R_mulConway (x y : Game) :
    (mulConway x y).R = RmulLR x y ++ RmulRL x y := by
  simp [RmulLR, RmulRL]

/-- Normalization closure: collapse terminal cuts (`{ | }`) to `zero`,
preserve nonterminal games. -/
@[simp] def normalize (g : Game) : Game :=
  match g.L, g.R with
  | [], [] => zero
  | _, _ => g

@[simp] theorem normalize_zero : normalize zero = zero := by
  simp [normalize]

@[simp] theorem normalize_idem (x : Game) :
    normalize (normalize x) = normalize x := by
  cases hL : x.L <;> cases hR : x.R <;> simp [normalize, hL, hR]

theorem normalize_terminal (x : Game) (hL : x.L = []) (hR : x.R = []) :
    normalize x = zero := by
  simp [normalize, hL, hR]

theorem normalize_nonterminal (x : Game) (h : x.L ≠ [] ∨ x.R ≠ []) :
    normalize x = x := by
  cases hL : x.L <;> cases hR : x.R <;> simp [normalize, hL, hR] at h ⊢

theorem normalize_add_zero_left (y : Game) :
    normalize (addConway zero y) = normalize y := by
  simp

theorem normalize_add_zero_right (x : Game) :
    normalize (addConway x zero) = normalize x := by
  by_cases hx : x = zero
  · subst hx
    simp
  · have hx0 : x ≠ (⟨0, GameN.mk0⟩ : Game) := by
      simpa [zero] using hx
    simp [hx0]

theorem normalize_mul_zero_left (x : Game) :
    normalize (mulConway zero x) = normalize zero := by
  simp

theorem normalize_mul_zero_right (x : Game) :
    normalize (mulConway x zero) = normalize zero := by
  simp

end Surreal
end Numbers
end HeytingLean
