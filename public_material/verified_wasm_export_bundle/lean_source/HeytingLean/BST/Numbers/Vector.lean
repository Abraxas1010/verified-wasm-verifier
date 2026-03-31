import HeytingLean.BST.Numbers.Real

/-!
# BST.Numbers.Vector

Finite vectors whose entries live on the `RealB` grid, with exact `Rat`
intermediate computations for aggregate operations.
-/

namespace HeytingLean.BST

abbrev BVector (k : ℕ) (n : ℕ) := Fin n → RealB k

namespace BVector

def default (k n : ℕ) : BVector k n := fun _ => RealB.default k

def ofFn {k n : ℕ} (f : Fin n → RealB k) : BVector k n := f

def toRatVec {k : ℕ} (hk : 0 < k) {n : ℕ} (v : BVector k n) : Fin n → Rat :=
  fun i => RealB.toRat hk (v i)

def dot {k : ℕ} (hk : 0 < k) {n : ℕ} (v w : BVector k n) : Rat :=
  Finset.sum Finset.univ (fun i => RealB.toRat hk (v i) * RealB.toRat hk (w i))

def add {k : ℕ} (hk : 0 < k) {n : ℕ} (v w : BVector k n) : BVector k n :=
  fun i => RealB.add hk (v i) (w i)

def smul {k : ℕ} (hk : 0 < k) {n : ℕ} (c : Rat) (v : BVector k n) : BVector k n :=
  fun i => RealB.round hk (c * RealB.toRat hk (v i))

def sub {k : ℕ} (hk : 0 < k) {n : ℕ} (v w : BVector k n) : BVector k n :=
  fun i => RealB.sub hk (v i) (w i)

def normSq {k : ℕ} (hk : 0 < k) {n : ℕ} (v : BVector k n) : Rat :=
  dot hk v v

theorem dot_self_nonneg {k : ℕ} (hk : 0 < k) {n : ℕ} (v : BVector k n) :
    0 ≤ dot hk v v := by
  unfold dot
  refine Finset.sum_nonneg ?_
  intro i _
  nlinarith [sq_nonneg (RealB.toRat hk (v i))]

@[simp] theorem dot_default_left {k : ℕ} (hk : 0 < k) {n : ℕ} (v : BVector k n) :
    dot hk (default k n) v = 0 := by
  unfold dot default
  simp [RealB.toRat_default]

@[simp] theorem add_default_right {k : ℕ} (hk : 0 < k) {n : ℕ} (v : BVector k n) :
    add hk v (default k n) = v := by
  funext i
  simp [add, default]

@[simp] theorem smul_zero {k : ℕ} (hk : 0 < k) {n : ℕ} (v : BVector k n) :
    smul hk 0 v = default k n := by
  funext i
  simp [smul, default]

@[simp] theorem sub_default_right {k : ℕ} (hk : 0 < k) {n : ℕ} (v : BVector k n) :
    sub hk v (default k n) = v := by
  funext i
  simp [sub, default]

@[simp] theorem sub_self {k : ℕ} (hk : 0 < k) {n : ℕ} (v : BVector k n) :
    sub hk v v = default k n := by
  funext i
  simp [sub, default]

end BVector

end HeytingLean.BST
