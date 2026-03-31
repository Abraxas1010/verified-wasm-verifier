import HeytingLean.BST.Numbers.Real

/-!
# BST.Analysis.Delta

Finite-grid delta spikes.
-/

namespace HeytingLean.BST.Analysis

open HeytingLean.BST

def finiteDelta {k : ℕ} (hk : 0 < k) (h : RealB k) (x : RealB k) : Rat :=
  if x = RealB.default k then
    1 / RealB.toRat hk h
  else 0

theorem finiteDelta_nonneg {k : ℕ} (hk : 0 < k) (h : RealB k)
    (hh : 0 < RealB.toRat hk h) (x : RealB k) :
    0 ≤ finiteDelta hk h x := by
  unfold finiteDelta
  by_cases hx : x = RealB.default k
  · simp [hx]
    positivity
  · simp [hx]

end HeytingLean.BST.Analysis
