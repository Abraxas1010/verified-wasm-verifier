import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Nucleus
import Mathlib.Tactic.DeriveFintype

/-!
# Three-Element Chain - Computable Implementation

The 3-element chain lattice {⊥, mid, ⊤} with decidable operations.
This is a Heyting algebra (distributive lattice with implication).

## Structure

```
    ⊤
    |
   mid
    |
    ⊥
```

A linear chain of 3 elements where ⊥ < mid < ⊤.

## Key Properties

- Linear order (total order)
- Heyting algebra but NOT Boolean algebra
- ¬mid = ⊥ (not mid ∨ ¬mid = ⊤)
- Demonstrates that not all Heyting algebras are Boolean
-/

namespace HeytingLean.Tests.Bridges.ThreeComputable

/-- The 3-element chain -/
inductive Three : Type where
  | bot : Three
  | mid : Three
  | top : Three
deriving DecidableEq, Repr, Fintype

namespace Three

/-- Order relation -/
def le' : Three → Three → Bool
  | .bot, _ => true
  | .mid, .mid => true
  | .mid, .top => true
  | .mid, .bot => false
  | .top, .top => true
  | .top, _ => false

/-- Meet (infimum) - minimum in a chain -/
def inf' : Three → Three → Three
  | .bot, _ => .bot
  | _, .bot => .bot
  | .mid, .mid => .mid
  | .mid, .top => .mid
  | .top, .mid => .mid
  | .top, .top => .top

/-- Join (supremum) - maximum in a chain -/
def sup' : Three → Three → Three
  | .top, _ => .top
  | _, .top => .top
  | .mid, .mid => .mid
  | .mid, .bot => .mid
  | .bot, .mid => .mid
  | .bot, .bot => .bot

/-- Heyting implication: x ⇨ y = max {z | x ⊓ z ≤ y} -/
def himp' : Three → Three → Three
  | .bot, _ => .top      -- ⊥ ⇨ y = ⊤
  | .mid, .bot => .bot   -- mid ⇨ ⊥ = ⊥
  | .mid, .mid => .top   -- mid ⇨ mid = ⊤
  | .mid, .top => .top   -- mid ⇨ ⊤ = ⊤
  | .top, x => x         -- ⊤ ⇨ y = y

/-- Complement (pseudo-complement): ¬x = x ⇨ ⊥ -/
def compl' : Three → Three
  | .bot => .top   -- ¬⊥ = ⊤
  | .mid => .bot   -- ¬mid = ⊥ (NOT top!)
  | .top => .bot   -- ¬⊤ = ⊥

/-- All elements -/
def all : List Three := [.bot, .mid, .top]

/-- Encode to Int -/
def toInt : Three → Int
  | .bot => 0
  | .mid => 1
  | .top => 2

/-- Decode from Int -/
def ofInt : Int → Option Three
  | 0 => some .bot
  | 1 => some .mid
  | 2 => some .top
  | _ => none

end Three

/-! ## Mathlib Instances -/

instance : LE Three where
  le x y := Three.le' x y = true

instance : DecidableRel (α := Three) (· ≤ ·) := fun x y =>
  if h : Three.le' x y = true then isTrue h else isFalse h

instance : LT Three where
  lt x y := x ≤ y ∧ ¬(y ≤ x)

instance : DecidableRel (α := Three) (· < ·) := fun _ _ =>
  inferInstanceAs (Decidable (_ ∧ _))

instance : Preorder Three where
  le_refl := by decide
  le_trans := by decide

instance : PartialOrder Three where
  le_antisymm := by decide

instance : Top Three where
  top := .top

instance : Bot Three where
  bot := .bot

instance : Max Three where
  max := Three.sup'

instance : Min Three where
  min := Three.inf'

instance : SemilatticeInf Three where
  inf := Three.inf'
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide

instance : SemilatticeSup Three where
  sup := Three.sup'
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide

instance instLattice : Lattice Three where
  inf := Three.inf'
  sup := Three.sup'
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide

instance : OrderTop Three where
  le_top := by decide

instance : OrderBot Three where
  bot_le := by decide

instance : BoundedOrder Three where
  top := .top
  bot := .bot
  le_top := by decide
  bot_le := by decide

instance : HImp Three where
  himp := Three.himp'

instance : HasCompl Three where
  compl := Three.compl'

instance : HeytingAlgebra Three where
  himp := Three.himp'
  le_himp_iff := by decide
  himp_bot := by decide

/-! ## Verification Tests -/

-- Order tests (linear chain)
#eval Three.le' .bot .mid  -- true
#eval Three.le' .mid .top  -- true
#eval Three.le' .bot .top  -- true
#eval Three.le' .top .bot  -- false
#eval Three.le' .mid .bot  -- false

-- Meet tests (minimum)
#eval Three.inf' .bot .mid  -- bot
#eval Three.inf' .mid .top  -- mid
#eval Three.inf' .bot .top  -- bot
#eval Three.inf' .mid .mid  -- mid

-- Join tests (maximum)
#eval Three.sup' .bot .mid  -- mid
#eval Three.sup' .mid .top  -- top
#eval Three.sup' .bot .top  -- top
#eval Three.sup' .mid .mid  -- mid

-- Heyting implication tests
#eval Three.himp' .bot .top  -- top
#eval Three.himp' .mid .bot  -- bot
#eval Three.himp' .mid .mid  -- top
#eval Three.himp' .mid .top  -- top
#eval Three.himp' .top .bot  -- bot
#eval Three.himp' .top .mid  -- mid
#eval Three.himp' .top .top  -- top

-- Complement tests
#eval Three.compl' .bot  -- top
#eval Three.compl' .mid  -- bot (NOT Boolean!)
#eval Three.compl' .top  -- bot

-- NOT Boolean: mid ⊔ ¬mid ≠ ⊤
#eval Three.sup' .mid (Three.compl' .mid)  -- mid (NOT top!)

-- This shows Three is NOT a Boolean algebra:
-- mid ⊔ ¬mid = mid ⊔ ⊥ = mid ≠ ⊤

-- But it IS a valid Heyting algebra (verified by instance)
-- Verification: le_himp_iff holds
-- x ≤ y ⇨ z  iff  x ⊓ y ≤ z

/-! ## Summary

Three is a 3-element chain Heyting algebra:
- Linear order: ⊥ < mid < ⊤
- Heyting algebra with valid implication
- NOT a Boolean algebra: mid ⊔ ¬mid = mid ≠ ⊤
- Demonstrates "middle" values in intuitionistic logic

All operations verified by `by decide`.
-/

end HeytingLean.Tests.Bridges.ThreeComputable
