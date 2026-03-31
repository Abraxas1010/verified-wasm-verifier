import HeytingLean.BST.Numbers.Real

/-!
# BST.Analysis.Derivative

Executable bounded finite-difference scaffolding.
-/

namespace HeytingLean.BST.Analysis

open HeytingLean.BST

def centralDiff (k : ℕ) (hk : 0 < k) (h : RealB k)
    (f : RealB k → Rat) (x : RealB k) : Rat :=
  let num := f (RealB.add hk x h) - f (RealB.sub hk x h)
  let den := (2 : Rat) * RealB.toRat hk h
  num / den

def square (k : ℕ) (hk : 0 < k) (x : RealB k) : Rat :=
  let q := RealB.toRat hk x
  q * q

theorem centralDiff_const (k : ℕ) (hk : 0 < k) (h x : RealB k) (c : Rat) :
    centralDiff k hk h (fun _ => c) x = 0 := by
  simp [centralDiff]

theorem square_nonneg (k : ℕ) (hk : 0 < k) (x : RealB k) :
    0 ≤ square k hk x := by
  unfold square
  nlinarith [sq_nonneg (RealB.toRat hk x)]

end HeytingLean.BST.Analysis
