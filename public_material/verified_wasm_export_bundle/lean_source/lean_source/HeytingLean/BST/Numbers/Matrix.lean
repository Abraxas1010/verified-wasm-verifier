import HeytingLean.BST.Numbers.Vector

/-!
# BST.Numbers.Matrix

Rat-valued matrices acting on `BVector`s. Matrix entries stay exact; rounding is
only applied at the vector-storage boundary.
-/

namespace HeytingLean.BST

abbrev BMatrix (_k : ℕ) (m n : ℕ) := Fin m → Fin n → Rat

namespace BMatrix

def zero (_k : ℕ) (m n : ℕ) : BMatrix _k m n := fun _ _ => 0

def identity (k : ℕ) (n : ℕ) : BMatrix k n n :=
  fun i j => if i = j then 1 else 0

def transpose {k : ℕ} {m n : ℕ} (A : BMatrix k m n) : BMatrix k n m :=
  fun j i => A i j

def mulVec {k : ℕ} (hk : 0 < k) {m n : ℕ}
    (A : BMatrix k m n) (v : BVector k n) : Fin m → Rat :=
  fun i => Finset.sum Finset.univ (fun j => A i j * RealB.toRat hk (v j))

def mulVecRound {k : ℕ} (hk : 0 < k) {m n : ℕ}
    (A : BMatrix k m n) (v : BVector k n) : BVector k m :=
  fun i => RealB.round hk (mulVec hk A v i)

def isSymmetric {k : ℕ} {n : ℕ} (A : BMatrix k n n) : Prop :=
  ∀ i j, A i j = A j i

@[simp] theorem transpose_transpose {k : ℕ} {m n : ℕ} (A : BMatrix k m n) :
    transpose (transpose A) = A := by
  funext i j
  rfl

theorem identity_mulVec {k : ℕ} (hk : 0 < k) {n : ℕ} (v : BVector k n) :
    mulVecRound hk (identity k n) v = v := by
  funext i
  have hmul : mulVec hk (identity k n) v i = RealB.toRat hk (v i) := by
    unfold mulVec identity
    simp
  unfold mulVecRound
  rw [hmul]
  exact RealB.round_eq_self hk (v i)

theorem isSymmetric_identity (k n : ℕ) : isSymmetric (identity k n) := by
  intro i j
  by_cases h : i = j
  · subst h
    simp [identity]
  · have h' : ¬ j = i := by
      intro hji
      exact h hji.symm
    simp [identity, h, h']

end BMatrix

end HeytingLean.BST
