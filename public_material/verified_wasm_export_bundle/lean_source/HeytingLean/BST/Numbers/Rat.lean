import Mathlib
import HeytingLean.BST.Numbers.Int

/-!
# BST.Numbers.Rat

Exact bounded rationals, represented by normalized `Rat` values whose numerator
and denominator stay within the chosen bound.
-/

namespace HeytingLean.BST

structure RatB (k : ℕ) where
  val : Rat
  num_bound : Int.natAbs val.num ≤ k
  den_bound : val.den ≤ k
  deriving Repr, DecidableEq

namespace RatB

def ofRat? (k : ℕ) (q : Rat) : Option (RatB k) :=
  if hNum : Int.natAbs q.num ≤ k then
    if hDen : q.den ≤ k then
      some ⟨q, hNum, hDen⟩
    else
      none
  else
    none

def ofInt? (k : ℕ) (z : Int) : Option (RatB k) :=
  ofRat? k z

def checkedNeg {k : ℕ} (q : RatB k) : RatB k :=
  ⟨-q.val, by simpa using q.num_bound, by simpa using q.den_bound⟩

def checkedAdd {k : ℕ} (a b : RatB k) : Option (RatB k) :=
  ofRat? k (a.val + b.val)

def checkedSub {k : ℕ} (a b : RatB k) : Option (RatB k) :=
  ofRat? k (a.val - b.val)

def checkedMul {k : ℕ} (a b : RatB k) : Option (RatB k) :=
  ofRat? k (a.val * b.val)

@[simp] theorem ofRat?_isSome_iff {k : ℕ} {q : Rat} :
    (ofRat? k q).isSome = true ↔ Int.natAbs q.num ≤ k ∧ q.den ≤ k := by
  unfold ofRat?
  by_cases hNum : Int.natAbs q.num ≤ k <;> by_cases hDen : q.den ≤ k <;> simp [hNum, hDen]

@[simp] theorem checkedNeg_val {k : ℕ} (q : RatB k) :
    (checkedNeg q).val = -q.val :=
  rfl

end RatB

end HeytingLean.BST
