import Mathlib

namespace HeytingLean.HeytingVeil.SpecLib

open scoped BigOperators

/-
Lean specification building blocks used by `heytingveil generate`.
These primitives are intentionally small and composable.
-/

def absInt (x : Int) : Int :=
  Int.ofNat (Int.natAbs x)

def maxInt (a b : Int) : Int :=
  max a b

def minInt (a b : Int) : Int :=
  min a b

def clampInt (lo hi x : Int) : Int :=
  maxInt lo (minInt hi x)

def add1Int (x : Int) : Int :=
  x + 1

def add2Int (x y : Int) : Int :=
  x + y

def subInt (x y : Int) : Int :=
  x - y

def mulInt (x y : Int) : Int :=
  x * y

def squareInt (x : Int) : Int :=
  x * x

def boolToInt (b : Bool) : Int :=
  if b then 1 else 0

def intToBool (z : Int) : Bool :=
  z != 0

def guardedSelect (cond : Bool) (t e : Int) : Int :=
  if cond then t else e

def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo n + (n + 1)

def triangular (n : Nat) : Nat :=
  n * (n + 1) / 2

def isEven (n : Nat) : Bool :=
  n % 2 = 0

def isOdd (n : Nat) : Bool :=
  !isEven n

def safeDiv (x y : Int) : Int :=
  if y = 0 then 0 else x / y

def bounded (lo hi x : Int) : Prop :=
  lo <= x ∧ x <= hi

def saturatingAdd (lo hi x y : Int) : Int :=
  clampInt lo hi (x + y)

def max3Int (a b c : Int) : Int :=
  maxInt (maxInt a b) c

def min3Int (a b c : Int) : Int :=
  minInt (minInt a b) c

theorem absInt_nonneg (x : Int) : 0 <= absInt x := by
  simp [absInt]

theorem maxInt_left (a b : Int) : a <= maxInt a b := by
  simp [maxInt]

theorem maxInt_right (a b : Int) : b <= maxInt a b := by
  simp [maxInt]

theorem minInt_left (a b : Int) : minInt a b <= a := by
  simp [minInt]

theorem minInt_right (a b : Int) : minInt a b <= b := by
  simp [minInt]

theorem clampInt_ge_lo (lo hi x : Int) : lo <= clampInt lo hi x := by
  simp [clampInt, maxInt, minInt]

theorem clampInt_le_hi (lo hi x : Int) (hlohi : lo <= hi) : clampInt lo hi x <= hi := by
  unfold clampInt maxInt minInt
  exact max_le hlohi (min_le_left _ _)

theorem clampInt_bounded (lo hi x : Int) (hlohi : lo <= hi) :
    bounded lo hi (clampInt lo hi x) := by
  constructor
  · exact clampInt_ge_lo lo hi x
  · exact clampInt_le_hi lo hi x hlohi

theorem add1Int_spec (x : Int) : add1Int x = x + 1 := by
  rfl

theorem add2Int_comm (x y : Int) : add2Int x y = add2Int y x := by
  simp [add2Int, Int.add_comm]

theorem squareInt_nonneg (x : Int) : 0 <= squareInt x := by
  simpa [squareInt, pow_two] using (sq_nonneg x)

theorem boolToInt_true : boolToInt true = 1 := by
  rfl

theorem boolToInt_false : boolToInt false = 0 := by
  rfl

theorem intToBool_zero : intToBool 0 = false := by
  simp [intToBool]

theorem guardedSelect_true (x y : Int) : guardedSelect true x y = x := by
  simp [guardedSelect]

theorem guardedSelect_false (x y : Int) : guardedSelect false x y = y := by
  simp [guardedSelect]

theorem sumTo_zero : sumTo 0 = 0 := by
  rfl

theorem sumTo_succ (n : Nat) : sumTo (n + 1) = sumTo n + (n + 1) := by
  rfl

theorem sumTo_step_ge (n : Nat) : sumTo n <= sumTo (n + 1) := by
  simp [sumTo]

theorem triangular_def (n : Nat) : triangular n = n * (n + 1) / 2 := by
  rfl

theorem sumTo_eq_sum_range (n : Nat) : sumTo n = (∑ i ∈ Finset.range (n + 1), i) := by
  induction n with
  | zero =>
      simp [sumTo]
  | succ n ih =>
      calc
        sumTo (n + 1) = sumTo n + (n + 1) := by simp [sumTo]
        _ = (∑ i ∈ Finset.range (n + 1), i) + (n + 1) := by simp [ih]
        _ = (∑ i ∈ Finset.range (n + 2), i) := by
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
            (Finset.sum_range_succ (fun i => i) (n + 1)).symm

theorem sumTo_eq_triangular (n : Nat) : sumTo n = triangular n := by
  rw [triangular, sumTo_eq_sum_range]
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using (Finset.sum_range_id (n + 1))

theorem sumTo_eq_closed_form (n : Nat) : sumTo n = n * (n + 1) / 2 := by
  simpa [triangular] using sumTo_eq_triangular n

theorem safeDiv_zero (x : Int) : safeDiv x 0 = 0 := by
  simp [safeDiv]

theorem safeDiv_nonzero (x y : Int) (hy : y ≠ 0) : safeDiv x y = x / y := by
  simp [safeDiv, hy]

theorem max3_ge_left (a b c : Int) : a <= max3Int a b c := by
  unfold max3Int maxInt
  exact le_trans (le_max_left _ _) (le_max_left _ _)

theorem min3_le_left (a b c : Int) : min3Int a b c <= a := by
  unfold min3Int minInt
  exact le_trans (min_le_left _ _) (min_le_left _ _)

end HeytingLean.HeytingVeil.SpecLib
