import Mathlib

/-!
# BST.Numbers.Nat

Exact bounded naturals with checked operations.
-/

namespace HeytingLean.BST

abbrev NatB (k : ℕ) := Fin (k + 1)

namespace NatB

def toNat {k : ℕ} (n : NatB k) : ℕ := n.1

def ofNat? (k n : ℕ) : Option (NatB k) :=
  if h : n ≤ k then
    some ⟨n, by simpa using Nat.lt_succ_of_le h⟩
  else
    none

def checkedAdd {k : ℕ} (a b : NatB k) : Option (NatB k) :=
  ofNat? k (a.1 + b.1)

def checkedMul {k : ℕ} (a b : NatB k) : Option (NatB k) :=
  ofNat? k (a.1 * b.1)

@[simp] theorem ofNat?_isSome_iff {k n : ℕ} :
    (ofNat? k n).isSome = true ↔ n ≤ k := by
  unfold ofNat?
  by_cases h : n ≤ k <;> simp [h]

@[simp] theorem toNat_mk {k n : ℕ} (h : n < k + 1) :
    toNat (⟨n, h⟩ : NatB k) = n :=
  rfl

end NatB

end HeytingLean.BST
