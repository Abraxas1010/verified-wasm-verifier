import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Nucleus
import Mathlib.Tactic.DeriveFintype

/-!
# Boolean Algebra - Computable Implementation

The 2-element Boolean algebra {⊥, ⊤} with decidable operations.
This is the simplest Heyting algebra (and also a Boolean algebra).

## Structure

```
    ⊤
    |
    ⊥
```

A chain of 2 elements where ⊥ < ⊤.
-/

namespace HeytingLean.Tests.Bridges.BoolComputable

/-- The 2-element Boolean algebra -/
inductive Bool2 : Type where
  | bot : Bool2
  | top : Bool2
deriving DecidableEq, Repr, Fintype

namespace Bool2

/-- Order relation -/
def le' : Bool2 → Bool2 → Bool
  | .bot, _ => true
  | .top, .top => true
  | .top, .bot => false

/-- Meet (infimum) -/
def inf' : Bool2 → Bool2 → Bool2
  | .bot, _ => .bot
  | _, .bot => .bot
  | .top, .top => .top

/-- Join (supremum) -/
def sup' : Bool2 → Bool2 → Bool2
  | .top, _ => .top
  | _, .top => .top
  | .bot, .bot => .bot

/-- Heyting implication (same as classical in Boolean algebra) -/
def himp' : Bool2 → Bool2 → Bool2
  | .bot, _ => .top
  | .top, x => x

/-- Complement (negation) -/
def compl' : Bool2 → Bool2
  | .bot => .top
  | .top => .bot

/-- All elements -/
def all : List Bool2 := [.bot, .top]

/-- Encode to Int -/
def toInt : Bool2 → Int
  | .bot => 0
  | .top => 1

/-- Decode from Int -/
def ofInt : Int → Option Bool2
  | 0 => some .bot
  | 1 => some .top
  | _ => none

end Bool2

/-! ## Mathlib Instances -/

instance : LE Bool2 where
  le x y := Bool2.le' x y = true

instance : DecidableRel (α := Bool2) (· ≤ ·) := fun x y =>
  if h : Bool2.le' x y = true then isTrue h else isFalse h

instance : LT Bool2 where
  lt x y := x ≤ y ∧ ¬(y ≤ x)

instance : DecidableRel (α := Bool2) (· < ·) := fun _ _ =>
  inferInstanceAs (Decidable (_ ∧ _))

instance : Preorder Bool2 where
  le_refl := by decide
  le_trans := by decide

instance : PartialOrder Bool2 where
  le_antisymm := by decide

instance : Top Bool2 where
  top := .top

instance : Bot Bool2 where
  bot := .bot

instance : Max Bool2 where
  max := Bool2.sup'

instance : Min Bool2 where
  min := Bool2.inf'

instance : SemilatticeInf Bool2 where
  inf := Bool2.inf'
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide

instance : SemilatticeSup Bool2 where
  sup := Bool2.sup'
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide

instance instLattice : Lattice Bool2 where
  inf := Bool2.inf'
  sup := Bool2.sup'
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide

instance : OrderTop Bool2 where
  le_top := by decide

instance : OrderBot Bool2 where
  bot_le := by decide

instance : BoundedOrder Bool2 where
  top := .top
  bot := .bot
  le_top := by decide
  bot_le := by decide

instance : HImp Bool2 where
  himp := Bool2.himp'

instance : HasCompl Bool2 where
  compl := Bool2.compl'

instance : HeytingAlgebra Bool2 where
  himp := Bool2.himp'
  le_himp_iff := by decide
  himp_bot := by decide

instance : BooleanAlgebra Bool2 where
  le_top := by decide
  bot_le := by decide
  himp := Bool2.himp'
  compl := Bool2.compl'
  inf_compl_le_bot := by decide
  top_le_sup_compl := by decide
  himp_eq := by decide

/-! ## Verification Tests -/

-- Order tests
#eval Bool2.le' .bot .top  -- true
#eval Bool2.le' .top .bot  -- false
#eval Bool2.le' .bot .bot  -- true
#eval Bool2.le' .top .top  -- true

-- Meet tests
#eval Bool2.inf' .bot .top  -- bot
#eval Bool2.inf' .top .bot  -- bot
#eval Bool2.inf' .top .top  -- top

-- Join tests
#eval Bool2.sup' .bot .top  -- top
#eval Bool2.sup' .top .bot  -- top
#eval Bool2.sup' .bot .bot  -- bot

-- Heyting implication tests
#eval Bool2.himp' .bot .top  -- top
#eval Bool2.himp' .top .bot  -- bot
#eval Bool2.himp' .top .top  -- top
#eval Bool2.himp' .bot .bot  -- top

-- Complement tests
#eval Bool2.compl' .bot  -- top
#eval Bool2.compl' .top  -- bot

-- Boolean algebra verification: x ⊔ ¬x = ⊤
#eval Bool2.sup' .bot (Bool2.compl' .bot)  -- top
#eval Bool2.sup' .top (Bool2.compl' .top)  -- top

-- Boolean algebra verification: x ⊓ ¬x = ⊥
#eval Bool2.inf' .bot (Bool2.compl' .bot)  -- bot
#eval Bool2.inf' .top (Bool2.compl' .top)  -- bot

/-! ## Summary

Bool2 is a 2-element Boolean algebra:
- Simplest possible Heyting algebra
- Also a Boolean algebra (excluded middle holds)
- ⊥ ⊔ ¬⊥ = ⊤ and ⊤ ⊔ ¬⊤ = ⊤ (excluded middle)
- x ⊓ ¬x = ⊥ for all x (non-contradiction)

All operations verified by `by decide`.
-/

end HeytingLean.Tests.Bridges.BoolComputable
