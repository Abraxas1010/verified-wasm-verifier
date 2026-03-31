import HeytingLean.PerspectivalPlenum.ReReentryTower

namespace HeytingLean
namespace PerspectivalPlenum
namespace StrictRatchet

universe u

/-- Explicit stage labels for the non-destructive strict ratchet lane. -/
inductive StrictLevel where
  | L0
  | L1
  | L2
  deriving DecidableEq, Repr

namespace StrictLevel

/-- Numeric rank used for stage ordering proofs. -/
def rank : StrictLevel → Nat
  | .L0 => 0
  | .L1 => 1
  | .L2 => 2

instance : LE StrictLevel where
  le a b := rank a ≤ rank b

instance : LT StrictLevel where
  lt a b := rank a < rank b

@[simp] theorem rank_L0 : rank .L0 = 0 := rfl
@[simp] theorem rank_L1 : rank .L1 = 1 := rfl
@[simp] theorem rank_L2 : rank .L2 = 2 := rfl

@[simp] theorem le_refl (ℓ : StrictLevel) : ℓ ≤ ℓ := by
  cases ℓ <;> decide

theorem le_trans {a b c : StrictLevel} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  Nat.le_trans hab hbc

@[simp] theorem L0_le_L1 : StrictLevel.L0 ≤ StrictLevel.L1 := by decide
@[simp] theorem L1_le_L2 : StrictLevel.L1 ≤ StrictLevel.L2 := by decide
@[simp] theorem L0_le_L2 : StrictLevel.L0 ≤ StrictLevel.L2 := by decide
@[simp] theorem L0_lt_L1 : StrictLevel.L0 < StrictLevel.L1 := by decide
@[simp] theorem L1_lt_L2 : StrictLevel.L1 < StrictLevel.L2 := by decide
@[simp] theorem L0_lt_L2 : StrictLevel.L0 < StrictLevel.L2 := by decide

end StrictLevel

/-- Stage object in the strict ratchet lane: level label + resulting nucleus. -/
structure StrictStage (α : Type u) [Order.Frame α] where
  level : StrictLevel
  nucleus : Nucleus α

namespace StrictStage

variable {α : Type u} [Order.Frame α]

/-- Stage 0: base ontology nucleus. -/
def base (J : Nucleus α) : StrictStage α where
  level := .L0
  nucleus := J

/-- Stage 1: first witness-level upgrade by one ratchet step. -/
def witness (S : RatchetStep α) (J : Nucleus α) : StrictStage α where
  level := .L1
  nucleus := S J

/-- Stage 2: plenum-level upgrade by finite stratification. -/
def plenum (steps : List (RatchetStep α)) (J : Nucleus α) : StrictStage α where
  level := .L2
  nucleus := RatchetTower.stratify J steps

/-- Level-only preorder for staged reasoning. -/
def precedes (A B : StrictStage α) : Prop :=
  A.level ≤ B.level

/-- Strict stage precedence used for separation witnesses. -/
def strictlyPrecedes (A B : StrictStage α) : Prop :=
  A.level < B.level

@[simp] theorem base_precedes_witness (S : RatchetStep α) (J : Nucleus α) :
    precedes (base J) (witness S J) := by
  simp [precedes, base, witness]

@[simp] theorem witness_precedes_plenum (S : RatchetStep α)
    (steps : List (RatchetStep α)) (J : Nucleus α) :
    precedes (witness S J) (plenum steps J) := by
  simp [precedes, witness, plenum]

@[simp] theorem base_strictly_precedes_plenum (steps : List (RatchetStep α)) (J : Nucleus α) :
    strictlyPrecedes (base J) (plenum steps J) := by
  simp [strictlyPrecedes, base, plenum]

@[simp] theorem base_nucleus (J : Nucleus α) :
    (base J).nucleus = J := rfl

@[simp] theorem witness_nucleus (S : RatchetStep α) (J : Nucleus α) :
    (witness S J).nucleus = S J := rfl

@[simp] theorem plenum_nucleus (steps : List (RatchetStep α)) (J : Nucleus α) :
    (plenum steps J).nucleus = RatchetTower.stratify J steps := rfl

end StrictStage

end StrictRatchet
end PerspectivalPlenum
end HeytingLean
