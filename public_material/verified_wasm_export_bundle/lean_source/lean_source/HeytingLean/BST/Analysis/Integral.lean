import HeytingLean.BST.Numbers.Real

/-!
# BST.Analysis.Integral

Finite-sum integration scaffolding for the first BST slice.
-/

namespace HeytingLean.BST.Analysis

open HeytingLean.BST

def riemannSum (k : ℕ) (_hk : 0 < k)
    (step : Rat) (pts : List (RealB k)) (f : RealB k → Rat) : Rat :=
  step * (pts.map f).sum

def midpointAverage (k : ℕ) (hk : 0 < k)
    (pts : List (RealB k)) (f : RealB k → Rat) : Rat :=
  if _h : pts.length = 0 then
    0
  else
    riemannSum k hk ((1 : Rat) / pts.length) pts f

@[simp] theorem riemannSum_nil (k : ℕ) (hk : 0 < k) (step : Rat) (f : RealB k → Rat) :
    riemannSum k hk step [] f = 0 := by
  simp [riemannSum]

theorem riemannSum_add (k : ℕ) (hk : 0 < k) (step : Rat)
    (pts : List (RealB k)) (f g : RealB k → Rat) :
    riemannSum k hk step pts (fun x => f x + g x) =
      riemannSum k hk step pts f + riemannSum k hk step pts g := by
  induction pts with
  | nil =>
      simp [riemannSum]
  | cons x xs ih =>
      simp [riemannSum, mul_add, add_assoc, add_left_comm]

@[simp] theorem midpointAverage_nil (k : ℕ) (hk : 0 < k) (f : RealB k → Rat) :
    midpointAverage k hk [] f = 0 := by
  simp [midpointAverage]

end HeytingLean.BST.Analysis
