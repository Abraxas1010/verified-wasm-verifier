import Mathlib.Data.Fintype.Order
import Mathlib.Order.Heyting.Basic

/-!
# Varela ECI

Three-valued extended calculus of indications:

- `unmarked`
- `autonomous`
- `marked`

The carrier is a three-element chain, so it supports a concrete Heyting algebra
presentation where excluded middle fails exactly at the autonomous value.
-/

namespace HeytingLean.Varela

/-- Varela's three indicational values. -/
inductive IndVal : Type
  | unmarked
  | autonomous
  | marked
  deriving DecidableEq, Repr

instance : Fintype IndVal where
  elems := {.unmarked, .autonomous, .marked}
  complete a := by
    cases a <;> simp

namespace IndVal

/-- Rank embedding for the linear order `unmarked < autonomous < marked`. -/
def rank : IndVal → Nat
  | .unmarked => 0
  | .autonomous => 1
  | .marked => 2

theorem rank_injective : Function.Injective rank := by
  intro x y h
  cases x <;> cases y <;> simp [rank] at h
  · rfl
  · rfl
  · rfl

instance : LinearOrder IndVal :=
  LinearOrder.lift' rank rank_injective

instance : OrderBot IndVal where
  bot := .unmarked
  bot_le := by
    intro a
    cases a <;> decide

instance : OrderTop IndVal where
  top := .marked
  le_top := by
    intro a
    cases a <;> decide

instance : BoundedOrder IndVal := ⟨⟩

instance : DistribLattice IndVal := inferInstance

/-- Spencer-Brown/Varela crossing. -/
def cross : IndVal → IndVal
  | .marked => .unmarked
  | .unmarked => .marked
  | .autonomous => .autonomous

/-- Calling/condensation on the chain coincides with join. -/
def call : IndVal → IndVal → IndVal := (· ⊔ ·)

/-- Explicit Heyting implication on the three-element chain. -/
def himp : IndVal → IndVal → IndVal
  | .unmarked, _ => .marked
  | .autonomous, .unmarked => .unmarked
  | .autonomous, _ => .marked
  | .marked, .unmarked => .unmarked
  | .marked, .autonomous => .autonomous
  | .marked, .marked => .marked

instance : HeytingAlgebra IndVal :=
  HeytingAlgebra.ofHImp himp <| by
    intro a b c
    cases a <;> cases b <;> cases c <;> decide

@[simp] theorem cross_unmarked : cross .unmarked = .marked := rfl
@[simp] theorem cross_autonomous : cross .autonomous = .autonomous := rfl
@[simp] theorem cross_marked : cross .marked = .unmarked := rfl

theorem autonomous_fixed : cross .autonomous = .autonomous := rfl

theorem marked_not_fixed : cross .marked ≠ .marked := by decide
theorem unmarked_not_fixed : cross .unmarked ≠ .unmarked := by decide

theorem cross_fixed_iff (x : IndVal) : cross x = x ↔ x = .autonomous := by
  cases x <;> simp [cross]

def crossFixedPoints : Set IndVal := {x | cross x = x}

theorem mem_crossFixedPoints_iff (x : IndVal) :
    x ∈ crossFixedPoints ↔ x = .autonomous := by
  simp [crossFixedPoints, cross_fixed_iff]

@[simp] theorem autonomous_compl : (.autonomous : IndVal)ᶜ = .unmarked := rfl
@[simp] theorem marked_compl : (.marked : IndVal)ᶜ = .unmarked := rfl
@[simp] theorem unmarked_compl : (.unmarked : IndVal)ᶜ = .marked := rfl

theorem autonomous_excluded_middle :
    (.autonomous : IndVal) ⊔ (.autonomous : IndVal)ᶜ = .autonomous := by
  rfl

theorem autonomous_not_classical :
    ¬ ((.autonomous : IndVal) ⊔ (.autonomous : IndVal)ᶜ = (⊤ : IndVal)) := by
  decide

end IndVal

open IndVal

export IndVal (cross call crossFixedPoints autonomous_fixed marked_not_fixed
  unmarked_not_fixed cross_fixed_iff autonomous_not_classical)

end HeytingLean.Varela
