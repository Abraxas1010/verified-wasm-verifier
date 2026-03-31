import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Nucleus
import Mathlib.Tactic.DeriveFintype

/-!
# Five-Element Chain - Computable Implementation

The 5-element chain lattice `{⊥, low, mid, high, ⊤}` with decidable operations.

This is a Heyting algebra (distributive lattice with implication), but **not** a Boolean algebra.

Structure (linear order):

```
    ⊤
    |
   high
    |
   mid
    |
   low
    |
    ⊥
```

All operations are computable and all axioms are discharged via `by decide`.
-/

namespace HeytingLean.Tests.Bridges.FiveComputable

/-- The 5-element chain -/
inductive Five : Type where
  | bot : Five
  | low : Five
  | mid : Five
  | high : Five
  | top : Five
deriving DecidableEq, Repr, Fintype

namespace Five

def toNat : Five → Nat
  | .bot => 0
  | .low => 1
  | .mid => 2
  | .high => 3
  | .top => 4

def fromNat : Nat → Five
  | 0 => .bot
  | 1 => .low
  | 2 => .mid
  | 3 => .high
  | _ => .top

/-- Order relation (as Bool): `x ≤ y` iff `toNat x ≤ toNat y`. -/
def le' (x y : Five) : Bool :=
  decide (toNat x ≤ toNat y)

/-- Meet (infimum): minimum in a chain. -/
def inf' (x y : Five) : Five :=
  fromNat (Nat.min (toNat x) (toNat y))

/-- Join (supremum): maximum in a chain. -/
def sup' (x y : Five) : Five :=
  fromNat (Nat.max (toNat x) (toNat y))

/-- Heyting implication in a chain: `x ⇨ y = ⊤` if `x ≤ y`, else `y`. -/
def himp' (x y : Five) : Five :=
  if le' x y then .top else y

/-- Pseudo-complement: `¬x = x ⇨ ⊥`. -/
def compl' (x : Five) : Five :=
  himp' x .bot

/-- All elements, in order. -/
def all : List Five := [.bot, .low, .mid, .high, .top]

/-- Encode to Int. -/
def toInt : Five → Int
  | .bot => 0
  | .low => 1
  | .mid => 2
  | .high => 3
  | .top => 4

/-- Decode from Int. -/
def ofInt : Int → Option Five
  | 0 => some .bot
  | 1 => some .low
  | 2 => some .mid
  | 3 => some .high
  | 4 => some .top
  | _ => none

end Five

/-! ## Mathlib Instances -/

instance : LE Five where
  le x y := Five.le' x y = true

instance : DecidableRel (α := Five) (· ≤ ·) := fun x y =>
  if h : Five.le' x y = true then isTrue h else isFalse h

instance : LT Five where
  lt x y := x ≤ y ∧ ¬(y ≤ x)

instance : DecidableRel (α := Five) (· < ·) := fun _ _ =>
  inferInstanceAs (Decidable (_ ∧ _))

instance : Preorder Five where
  le_refl := by decide
  le_trans := by decide

instance : PartialOrder Five where
  le_antisymm := by decide

instance : Top Five where
  top := .top

instance : Bot Five where
  bot := .bot

instance : Max Five where
  max := Five.sup'

instance : Min Five where
  min := Five.inf'

instance : SemilatticeInf Five where
  inf := Five.inf'
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide

instance : SemilatticeSup Five where
  sup := Five.sup'
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide

instance : Lattice Five where
  inf := Five.inf'
  sup := Five.sup'
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide

instance : OrderTop Five where
  le_top := by decide

instance : OrderBot Five where
  bot_le := by decide

instance : BoundedOrder Five where
  top := .top
  bot := .bot
  le_top := by decide
  bot_le := by decide

instance : HImp Five where
  himp := Five.himp'

instance : HasCompl Five where
  compl := Five.compl'

instance : HeytingAlgebra Five where
  himp := Five.himp'
  le_himp_iff := by decide
  himp_bot := by decide

/-! ## Sanity Checks -/

-- NOT Boolean: mid ⊔ ¬mid = mid ≠ ⊤
#eval Five.sup' .mid (Five.compl' .mid)  -- mid

end HeytingLean.Tests.Bridges.FiveComputable
