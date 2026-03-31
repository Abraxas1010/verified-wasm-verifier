import HeytingLean.Numbers.Surreal.PreLegalGame

/-!
# Surreal.StrategyOrder

SN-015 baseline: strategy-order core and disjunctive sum on pre-legal games.
-/

namespace HeytingLean
namespace Numbers
namespace Surreal

open HeytingLean.Numbers.SurrealCore

namespace StrategyOrder

abbrev Game := PreLegalGame

/-- Neutral strategy game. -/
def zero : Game := { L := [], R := [] }

/-- Disjunctive sum (structural pre-legal union of options). -/
def sum (x y : Game) : Game :=
  { L := x.L ++ y.L
    R := x.R ++ y.R }

/-- Birth-based strategy preorder (core executable order signal). -/
def leS (x y : Game) : Prop := x.toPreGame.birth ≤ y.toPreGame.birth

/-- Symmetric closure of `leS`. -/
def eqS (x y : Game) : Prop := leS x y ∧ leS y x

@[simp] theorem leS_refl (x : Game) : leS x x := Nat.le_refl _

theorem leS_trans {x y z : Game} (hxy : leS x y) (hyz : leS y z) : leS x z :=
  Nat.le_trans hxy hyz

@[simp] theorem eqS_refl (x : Game) : eqS x x := ⟨leS_refl x, leS_refl x⟩

theorem eqS_symm {x y : Game} (hxy : eqS x y) : eqS y x := ⟨hxy.2, hxy.1⟩

theorem eqS_trans {x y z : Game} (hxy : eqS x y) (hyz : eqS y z) : eqS x z :=
  ⟨leS_trans hxy.1 hyz.1, leS_trans hyz.2 hxy.2⟩

@[simp] theorem sum_zero_left (x : Game) : sum zero x = x := by
  cases x
  rfl

@[simp] theorem sum_zero_right (x : Game) : sum x zero = x := by
  cases x
  simp [sum, zero]

@[simp] theorem sum_assoc (x y z : Game) : sum (sum x y) z = sum x (sum y z) := by
  cases x
  cases y
  cases z
  simp [sum, List.append_assoc]

theorem legalCut_sum_of_cross (x y : Game)
    (hx : PreLegalGame.legalCut x)
    (hy : PreLegalGame.legalCut y)
    (hxy : PreLegalGame.crossLegal x y) :
    PreLegalGame.legalCut (sum x y) := by
  exact PreLegalGame.legalCut_append x y hx hy hxy

theorem contradictory_sum_left (x y : Game)
    (hx : PreLegalGame.contradictory x) :
    PreLegalGame.contradictory (sum x y) := by
  exact PreLegalGame.contradictory_append_left x y hx

theorem contradictory_sum_right (x y : Game)
    (hy : PreLegalGame.contradictory y) :
    PreLegalGame.contradictory (sum x y) := by
  exact PreLegalGame.contradictory_append_right x y hy

end StrategyOrder

end Surreal
end Numbers
end HeytingLean
