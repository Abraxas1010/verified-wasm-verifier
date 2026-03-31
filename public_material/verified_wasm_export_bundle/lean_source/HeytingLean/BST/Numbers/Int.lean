import Mathlib

/-!
# BST.Numbers.Int

Exact bounded integers with checked operations.
-/

namespace HeytingLean.BST

structure IntB (k : ℕ) where
  val : Int
  isBounded : Int.natAbs val ≤ k
  deriving Repr, DecidableEq

namespace IntB

def ofInt? (k : ℕ) (z : Int) : Option (IntB k) :=
  if h : Int.natAbs z ≤ k then some ⟨z, h⟩ else none

def zero (k : ℕ) : IntB k :=
  ⟨0, by simp⟩

def checkedNeg {k : ℕ} (z : IntB k) : IntB k :=
  ⟨-z.val, by simpa using z.isBounded⟩

def checkedAdd {k : ℕ} (a b : IntB k) : Option (IntB k) :=
  ofInt? k (a.val + b.val)

def checkedSub {k : ℕ} (a b : IntB k) : Option (IntB k) :=
  ofInt? k (a.val - b.val)

def checkedMul {k : ℕ} (a b : IntB k) : Option (IntB k) :=
  ofInt? k (a.val * b.val)

@[simp] theorem ofInt?_isSome_iff {k : ℕ} {z : Int} :
    (ofInt? k z).isSome = true ↔ Int.natAbs z ≤ k := by
  unfold ofInt?
  by_cases h : Int.natAbs z ≤ k <;> simp [h]

@[simp] theorem checkedNeg_val {k : ℕ} (z : IntB k) :
    (checkedNeg z).val = -z.val :=
  rfl

end IntB

end HeytingLean.BST
