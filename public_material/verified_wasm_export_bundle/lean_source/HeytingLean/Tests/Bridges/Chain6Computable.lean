import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Nucleus
import Mathlib.Tactic.DeriveFintype

/-!
# Chain6 - Computable Implementation

The 6-element chain lattice `{⊥, e1, e2, e3, e4, ⊤}` with decidable operations.

This is a Heyting algebra (distributive lattice with implication), but **not** a Boolean algebra.
All operations are computable and all axioms are discharged via `by decide`.
-/

namespace HeytingLean.Tests.Bridges.Chain6Computable

/-- The 6-element chain -/
inductive Chain6 : Type where
  | bot : Chain6
  | e1 : Chain6
  | e2 : Chain6
  | e3 : Chain6
  | e4 : Chain6
  | top : Chain6
deriving DecidableEq, Repr, Fintype

namespace Chain6

def rank : Chain6 → Nat
  | .bot => 0
  | .e1 => 1
  | .e2 => 2
  | .e3 => 3
  | .e4 => 4
  | .top => 5

def fromRank : Nat → Chain6
  | 0 => .bot
  | 1 => .e1
  | 2 => .e2
  | 3 => .e3
  | 4 => .e4
  | _ => .top

/-- Order relation (as Bool): `x ≤ y` iff `rank x ≤ rank y`. -/
def le' (x y : Chain6) : Bool :=
  decide (rank x ≤ rank y)

/-- Meet (infimum): minimum in a chain. -/
def inf' (x y : Chain6) : Chain6 :=
  fromRank (Nat.min (rank x) (rank y))

/-- Join (supremum): maximum in a chain. -/
def sup' (x y : Chain6) : Chain6 :=
  fromRank (Nat.max (rank x) (rank y))

/-- Heyting implication in a chain: `x ⇨ y = ⊤` if `x ≤ y`, else `y`. -/
def himp' (x y : Chain6) : Chain6 :=
  if le' x y then .top else y

/-- Pseudo-complement: `¬x = x ⇨ ⊥`. -/
def compl' (x : Chain6) : Chain6 :=
  himp' x .bot

/-- All elements, in order. -/
def all : List Chain6 := [.bot, .e1, .e2, .e3, .e4, .top]

/-- Encode to Int. -/
def toInt : Chain6 → Int
  | .bot => 0
  | .e1 => 1
  | .e2 => 2
  | .e3 => 3
  | .e4 => 4
  | .top => 5

/-- Decode from Int. -/
def ofInt : Int → Option Chain6
  | 0 => some .bot
  | 1 => some .e1
  | 2 => some .e2
  | 3 => some .e3
  | 4 => some .e4
  | 5 => some .top
  | _ => none

end Chain6

/-! ## Mathlib Instances -/

instance : LE Chain6 where
  le x y := Chain6.le' x y = true

instance : DecidableRel (α := Chain6) (· ≤ ·) := fun x y =>
  if h : Chain6.le' x y = true then isTrue h else isFalse h

instance : LT Chain6 where
  lt x y := x ≤ y ∧ ¬(y ≤ x)

instance : DecidableRel (α := Chain6) (· < ·) := fun _ _ =>
  inferInstanceAs (Decidable (_ ∧ _))

instance : Preorder Chain6 where
  le_refl := by decide
  le_trans := by decide

instance : PartialOrder Chain6 where
  le_antisymm := by decide

instance : Top Chain6 where
  top := .top

instance : Bot Chain6 where
  bot := .bot

instance : Max Chain6 where
  max := Chain6.sup'

instance : Min Chain6 where
  min := Chain6.inf'

instance : SemilatticeInf Chain6 where
  inf := Chain6.inf'
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide

instance : SemilatticeSup Chain6 where
  sup := Chain6.sup'
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide

instance : Lattice Chain6 where
  inf := Chain6.inf'
  sup := Chain6.sup'
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide

instance : OrderTop Chain6 where
  le_top := by decide

instance : OrderBot Chain6 where
  bot_le := by decide

instance : BoundedOrder Chain6 where
  top := .top
  bot := .bot
  le_top := by decide
  bot_le := by decide

instance : HImp Chain6 where
  himp := Chain6.himp'

instance : HasCompl Chain6 where
  compl := Chain6.compl'

instance : HeytingAlgebra Chain6 where
  himp := Chain6.himp'
  le_himp_iff := by decide
  himp_bot := by decide

/-! ## Sanity Check -/

-- NOT Boolean: e2 ⊔ ¬e2 = e2 ≠ ⊤
#eval Chain6.sup' .e2 (Chain6.compl' .e2)  -- e2

end HeytingLean.Tests.Bridges.Chain6Computable

