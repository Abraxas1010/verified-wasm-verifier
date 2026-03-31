import Mathlib.Data.List.FinRange
import Mathlib.Order.Nucleus

/-!
# Fin Chains - Computable Heyting Algebras (Fixed Sizes)

For the chain ladder (`chain7..chain15`), we use the standard carrier `Fin n` (finite linear order)
and define the Heyting implication:

`x ⇨ y = ⊤` if `x ≤ y`, else `y`.

All “proof anchor” theorems are discharged via `by decide` for each fixed `n`.
-/

namespace HeytingLean.Tests.Bridges.FinChainComputable

private def mkChainHimp {n : Nat} [NeZero n] (x y : Fin n) : Fin n :=
  if x ≤ y then (⊤ : Fin n) else y

private def mkChainCompl {n : Nat} [NeZero n] (x : Fin n) : Fin n :=
  mkChainHimp x (⊥ : Fin n)

private def mkChainAll (n : Nat) : List (Fin n) :=
  List.finRange n

private def mkChainToInt {n : Nat} (x : Fin n) : Int :=
  Int.ofNat x.val

private def mkChainLe {n : Nat} (x y : Fin n) : Bool :=
  decide (x ≤ y)

private def mkChainInf {n : Nat} (x y : Fin n) : Fin n :=
  min x y

private def mkChainSup {n : Nat} (x y : Fin n) : Fin n :=
  max x y

/-! ## Chain7 -/

abbrev Chain7 := Fin 7

namespace Chain7
def all : List Chain7 := mkChainAll 7
def toInt (x : Chain7) : Int := mkChainToInt x
def le' (x y : Chain7) : Bool := mkChainLe x y
def inf' (x y : Chain7) : Chain7 := mkChainInf x y
def sup' (x y : Chain7) : Chain7 := mkChainSup x y
def himp' (x y : Chain7) : Chain7 := mkChainHimp x y
def compl' (x : Chain7) : Chain7 := mkChainCompl x

instance : HImp Chain7 where himp := himp'
instance : HasCompl Chain7 where compl := compl'

instance : HeytingAlgebra Chain7 where
  himp := himp'
  le_himp_iff := by decide
  himp_bot := by decide

theorem le_himp_iff_decide : ∀ a b c : Chain7, a ≤ b ⇨ c ↔ a ⊓ b ≤ c := by
  decide

theorem himp_bot_decide : ∀ a : Chain7, a ⇨ ⊥ = aᶜ := by
  decide
end Chain7

/-! ## Chain8 -/

abbrev Chain8 := Fin 8

namespace Chain8
def all : List Chain8 := mkChainAll 8
def toInt (x : Chain8) : Int := mkChainToInt x
def le' (x y : Chain8) : Bool := mkChainLe x y
def inf' (x y : Chain8) : Chain8 := mkChainInf x y
def sup' (x y : Chain8) : Chain8 := mkChainSup x y
def himp' (x y : Chain8) : Chain8 := mkChainHimp x y
def compl' (x : Chain8) : Chain8 := mkChainCompl x

instance : HImp Chain8 where himp := himp'
instance : HasCompl Chain8 where compl := compl'

instance : HeytingAlgebra Chain8 where
  himp := himp'
  le_himp_iff := by decide
  himp_bot := by decide

theorem le_himp_iff_decide : ∀ a b c : Chain8, a ≤ b ⇨ c ↔ a ⊓ b ≤ c := by
  decide

theorem himp_bot_decide : ∀ a : Chain8, a ⇨ ⊥ = aᶜ := by
  decide
end Chain8

/-! ## Chain9 -/

abbrev Chain9 := Fin 9

namespace Chain9
def all : List Chain9 := mkChainAll 9
def toInt (x : Chain9) : Int := mkChainToInt x
def le' (x y : Chain9) : Bool := mkChainLe x y
def inf' (x y : Chain9) : Chain9 := mkChainInf x y
def sup' (x y : Chain9) : Chain9 := mkChainSup x y
def himp' (x y : Chain9) : Chain9 := mkChainHimp x y
def compl' (x : Chain9) : Chain9 := mkChainCompl x

instance : HImp Chain9 where himp := himp'
instance : HasCompl Chain9 where compl := compl'

instance : HeytingAlgebra Chain9 where
  himp := himp'
  le_himp_iff := by decide
  himp_bot := by decide

theorem le_himp_iff_decide : ∀ a b c : Chain9, a ≤ b ⇨ c ↔ a ⊓ b ≤ c := by
  decide

theorem himp_bot_decide : ∀ a : Chain9, a ⇨ ⊥ = aᶜ := by
  decide
end Chain9

/-! ## Chain10 -/

abbrev Chain10 := Fin 10

namespace Chain10
def all : List Chain10 := mkChainAll 10
def toInt (x : Chain10) : Int := mkChainToInt x
def le' (x y : Chain10) : Bool := mkChainLe x y
def inf' (x y : Chain10) : Chain10 := mkChainInf x y
def sup' (x y : Chain10) : Chain10 := mkChainSup x y
def himp' (x y : Chain10) : Chain10 := mkChainHimp x y
def compl' (x : Chain10) : Chain10 := mkChainCompl x

instance : HImp Chain10 where himp := himp'
instance : HasCompl Chain10 where compl := compl'

instance : HeytingAlgebra Chain10 where
  himp := himp'
  le_himp_iff := by decide
  himp_bot := by decide

theorem le_himp_iff_decide : ∀ a b c : Chain10, a ≤ b ⇨ c ↔ a ⊓ b ≤ c := by
  decide

theorem himp_bot_decide : ∀ a : Chain10, a ⇨ ⊥ = aᶜ := by
  decide
end Chain10

/-! ## Chain11 -/

abbrev Chain11 := Fin 11

namespace Chain11
def all : List Chain11 := mkChainAll 11
def toInt (x : Chain11) : Int := mkChainToInt x
def le' (x y : Chain11) : Bool := mkChainLe x y
def inf' (x y : Chain11) : Chain11 := mkChainInf x y
def sup' (x y : Chain11) : Chain11 := mkChainSup x y
def himp' (x y : Chain11) : Chain11 := mkChainHimp x y
def compl' (x : Chain11) : Chain11 := mkChainCompl x

instance : HImp Chain11 where himp := himp'
instance : HasCompl Chain11 where compl := compl'

instance : HeytingAlgebra Chain11 where
  himp := himp'
  le_himp_iff := by decide
  himp_bot := by decide

theorem le_himp_iff_decide : ∀ a b c : Chain11, a ≤ b ⇨ c ↔ a ⊓ b ≤ c := by
  decide

theorem himp_bot_decide : ∀ a : Chain11, a ⇨ ⊥ = aᶜ := by
  decide
end Chain11

/-! ## Chain12 -/

abbrev Chain12 := Fin 12

namespace Chain12
def all : List Chain12 := mkChainAll 12
def toInt (x : Chain12) : Int := mkChainToInt x
def le' (x y : Chain12) : Bool := mkChainLe x y
def inf' (x y : Chain12) : Chain12 := mkChainInf x y
def sup' (x y : Chain12) : Chain12 := mkChainSup x y
def himp' (x y : Chain12) : Chain12 := mkChainHimp x y
def compl' (x : Chain12) : Chain12 := mkChainCompl x

instance : HImp Chain12 where himp := himp'
instance : HasCompl Chain12 where compl := compl'

instance : HeytingAlgebra Chain12 where
  himp := himp'
  le_himp_iff := by decide
  himp_bot := by decide

theorem le_himp_iff_decide : ∀ a b c : Chain12, a ≤ b ⇨ c ↔ a ⊓ b ≤ c := by
  decide

theorem himp_bot_decide : ∀ a : Chain12, a ⇨ ⊥ = aᶜ := by
  decide
end Chain12

/-! ## Chain13 -/

abbrev Chain13 := Fin 13

namespace Chain13
def all : List Chain13 := mkChainAll 13
def toInt (x : Chain13) : Int := mkChainToInt x
def le' (x y : Chain13) : Bool := mkChainLe x y
def inf' (x y : Chain13) : Chain13 := mkChainInf x y
def sup' (x y : Chain13) : Chain13 := mkChainSup x y
def himp' (x y : Chain13) : Chain13 := mkChainHimp x y
def compl' (x : Chain13) : Chain13 := mkChainCompl x

instance : HImp Chain13 where himp := himp'
instance : HasCompl Chain13 where compl := compl'

instance : HeytingAlgebra Chain13 where
  himp := himp'
  le_himp_iff := by decide
  himp_bot := by decide

theorem le_himp_iff_decide : ∀ a b c : Chain13, a ≤ b ⇨ c ↔ a ⊓ b ≤ c := by
  decide

theorem himp_bot_decide : ∀ a : Chain13, a ⇨ ⊥ = aᶜ := by
  decide
end Chain13

/-! ## Chain14 -/

abbrev Chain14 := Fin 14

namespace Chain14
def all : List Chain14 := mkChainAll 14
def toInt (x : Chain14) : Int := mkChainToInt x
def le' (x y : Chain14) : Bool := mkChainLe x y
def inf' (x y : Chain14) : Chain14 := mkChainInf x y
def sup' (x y : Chain14) : Chain14 := mkChainSup x y
def himp' (x y : Chain14) : Chain14 := mkChainHimp x y
def compl' (x : Chain14) : Chain14 := mkChainCompl x

instance : HImp Chain14 where himp := himp'
instance : HasCompl Chain14 where compl := compl'

instance : HeytingAlgebra Chain14 where
  himp := himp'
  le_himp_iff := by decide
  himp_bot := by decide

theorem le_himp_iff_decide : ∀ a b c : Chain14, a ≤ b ⇨ c ↔ a ⊓ b ≤ c := by
  decide

theorem himp_bot_decide : ∀ a : Chain14, a ⇨ ⊥ = aᶜ := by
  decide
end Chain14

/-! ## Chain15 -/

abbrev Chain15 := Fin 15

namespace Chain15
def all : List Chain15 := mkChainAll 15
def toInt (x : Chain15) : Int := mkChainToInt x
def le' (x y : Chain15) : Bool := mkChainLe x y
def inf' (x y : Chain15) : Chain15 := mkChainInf x y
def sup' (x y : Chain15) : Chain15 := mkChainSup x y
def himp' (x y : Chain15) : Chain15 := mkChainHimp x y
def compl' (x : Chain15) : Chain15 := mkChainCompl x

instance : HImp Chain15 where himp := himp'
instance : HasCompl Chain15 where compl := compl'

instance : HeytingAlgebra Chain15 where
  himp := himp'
  le_himp_iff := by decide
  himp_bot := by decide

theorem le_himp_iff_decide : ∀ a b c : Chain15, a ≤ b ⇨ c ↔ a ⊓ b ≤ c := by
  decide

theorem himp_bot_decide : ∀ a : Chain15, a ⇨ ⊥ = aᶜ := by
  decide
end Chain15

end HeytingLean.Tests.Bridges.FinChainComputable
