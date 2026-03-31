import HeytingLean.BST.Numbers.Vector

/-!
# BST.Analysis.Symplectic

Bounded symplectic stepping schemes over `BVector`.
-/

namespace HeytingLean.BST.Analysis

open HeytingLean.BST

def symplecticEuler {k n : ℕ} (hk : 0 < k)
    (dH_dq dH_dp : BVector k n → BVector k n)
    (dt : RealB k) (q p : BVector k n) :
    BVector k n × BVector k n :=
  let pNew := BVector.sub hk p (BVector.smul hk (RealB.toRat hk dt) (dH_dq q))
  let qNew := BVector.add hk q (BVector.smul hk (RealB.toRat hk dt) (dH_dp pNew))
  (qNew, pNew)

def stoermerVerlet {k n : ℕ} (hk : 0 < k)
    (dH_dq dH_dp : BVector k n → BVector k n)
    (dt : RealB k) (q p : BVector k n) :
    BVector k n × BVector k n :=
  let halfDt := RealB.toRat hk dt / 2
  let pHalf := BVector.sub hk p (BVector.smul hk halfDt (dH_dq q))
  let qNew := BVector.add hk q (BVector.smul hk (RealB.toRat hk dt) (dH_dp pHalf))
  let pNew := BVector.sub hk pHalf (BVector.smul hk halfDt (dH_dq qNew))
  (qNew, pNew)

def symplecticEulerSteps {k n : ℕ} (hk : 0 < k)
    (dH_dq dH_dp : BVector k n → BVector k n)
    (dt : RealB k) : ℕ → BVector k n × BVector k n → BVector k n × BVector k n
  | 0, state => state
  | m + 1, state =>
      symplecticEulerSteps hk dH_dq dH_dp dt m
        (symplecticEuler hk dH_dq dH_dp dt state.1 state.2)

@[simp] theorem symplecticEuler_zero_dt {k n : ℕ} (hk : 0 < k)
    (dH_dq dH_dp : BVector k n → BVector k n) (q p : BVector k n) :
    symplecticEuler hk dH_dq dH_dp (RealB.default k) q p = (q, p) := by
  simp [symplecticEuler]

@[simp] theorem stoermerVerlet_zero_dt {k n : ℕ} (hk : 0 < k)
    (dH_dq dH_dp : BVector k n → BVector k n) (q p : BVector k n) :
    stoermerVerlet hk dH_dq dH_dp (RealB.default k) q p = (q, p) := by
  simp [stoermerVerlet]

end HeytingLean.BST.Analysis
