import HeytingLean.BST.Numbers.Matrix

/-!
# BST.Analysis.Laplacian

Finite periodic one-dimensional Laplacian with exact rational coefficients.
-/

namespace HeytingLean.BST.Analysis

open HeytingLean.BST

def forwardIndex (N : ℕ) (hN : 0 < N) (i : Fin N) : Fin N :=
  ⟨(i.val + 1) % N, Nat.mod_lt _ hN⟩

def backwardIndex (N : ℕ) (hN : 0 < N) (i : Fin N) : Fin N :=
  ⟨(i.val + (N - 1)) % N, Nat.mod_lt _ hN⟩

theorem forwardIndex_val (N : ℕ) (hN : 0 < N) (i : Fin N) :
    (forwardIndex N hN i).val = (i.val + 1) % N :=
  rfl

theorem backwardIndex_val (N : ℕ) (hN : 0 < N) (i : Fin N) :
    (backwardIndex N hN i).val = (i.val + (N - 1)) % N :=
  rfl

theorem backwardIndex_succ (N : ℕ) (hN : 0 < N) (i : Fin N) :
    ((backwardIndex N hN i).val + 1) % N = i.val := by
  rcases i with ⟨i, hi⟩
  rw [backwardIndex_val]
  by_cases hi0 : i = 0
  · subst hi0
    change ((0 + (N - 1)) % N + 1) % N = 0
    have hlt : N - 1 < N := Nat.sub_lt (Nat.pos_of_ne_zero (Nat.ne_of_gt hN)) (by decide)
    have hsum : N - 1 + 1 = N := by
      omega
    simp [Nat.mod_eq_of_lt hlt, hsum]
  · have hip : 0 < i := Nat.pos_iff_ne_zero.mpr hi0
    have hpred : i + (N - 1) = N + (i - 1) := by
      omega
    rw [hpred, Nat.add_mod]
    have hlt : i - 1 < N := by omega
    simp [Nat.mod_eq_of_lt hlt]
    have hsucc : i - 1 + 1 = i := by
      omega
    rw [hsucc, Nat.mod_eq_of_lt hi]

theorem forwardIndex_backward (N : ℕ) (hN : 0 < N) (i : Fin N) :
    forwardIndex N hN (backwardIndex N hN i) = i := by
  apply Fin.ext
  unfold forwardIndex
  simpa using backwardIndex_succ N hN i

theorem backwardIndex_forward (N : ℕ) (hN : 0 < N) (i : Fin N) :
    backwardIndex N hN (forwardIndex N hN i) = i := by
  apply Fin.ext
  rcases i with ⟨i, hi⟩
  unfold backwardIndex forwardIndex
  dsimp
  have hstep : (((i + 1) % N) + (N - 1)) % N = i := by
    by_cases hlast : i + 1 = N
    · have hi' : i = N - 1 := by omega
      rw [hlast]
      have hlt : N - 1 < N := Nat.sub_lt (Nat.pos_of_ne_zero (Nat.ne_of_gt hN)) (by decide)
      simp [hi', Nat.mod_eq_of_lt hlt]
    · have hlt : i + 1 < N := by omega
      rw [Nat.mod_eq_of_lt hlt]
      have hsum : i + 1 + (N - 1) = N + i := by
        omega
      rw [hsum, Nat.add_mod]
      simp [Nat.mod_eq_of_lt hi]
  simpa using hstep

def laplacian1D (k N : ℕ) (hk : 0 < k) (hN : 0 < N) (h : RealB k) : BMatrix k N N :=
  let hRat := RealB.toRat hk h
  let hSq := hRat * hRat
  fun i j =>
    let forward : Rat := if j = forwardIndex N hN i then 1 else 0
    let backward : Rat := if j = backwardIndex N hN i then 1 else 0
    let diagonal : Rat := if i = j then 2 else 0
    (forward + backward - diagonal) / hSq

theorem laplacian1D_symmetric (k N : ℕ) (hk : 0 < k) (hN : 0 < N) (h : RealB k) :
    BMatrix.isSymmetric (laplacian1D k N hk hN h) := by
  intro i j
  have hforward :
      (j = forwardIndex N hN i) ↔ (i = backwardIndex N hN j) := by
    constructor
    · intro hij
      subst j
      exact (backwardIndex_forward N hN i).symm
    · intro hij
      subst i
      exact (forwardIndex_backward N hN j).symm
  have hbackward :
      (j = backwardIndex N hN i) ↔ (i = forwardIndex N hN j) := by
    constructor
    · intro hij
      subst j
      exact (forwardIndex_backward N hN i).symm
    · intro hij
      subst i
      exact (backwardIndex_forward N hN j).symm
  unfold laplacian1D
  simp [hforward, hbackward, eq_comm, add_comm, sub_eq_add_neg]

theorem laplacian1D_constant_kernel (k N : ℕ) (hk : 0 < k) (hN : 0 < N) (h : RealB k)
    (c : RealB k) :
    BMatrix.mulVec hk (laplacian1D k N hk hN h) (fun _ => c) = fun _ => (0 : Rat) := by
  funext i
  have hforward :
      Finset.sum Finset.univ
        (fun j : Fin N => if j = forwardIndex N hN i then (1 : Rat) else 0) = 1 := by
    classical
    simpa using Finset.sum_ite_eq' Finset.univ (forwardIndex N hN i) (fun _ => (1 : Rat))
  have hbackward :
      Finset.sum Finset.univ
        (fun j : Fin N => if j = backwardIndex N hN i then (1 : Rat) else 0) = 1 := by
    classical
    simpa using Finset.sum_ite_eq' Finset.univ (backwardIndex N hN i) (fun _ => (1 : Rat))
  have hdiag :
      Finset.sum Finset.univ
        (fun j : Fin N => if i = j then (2 : Rat) else 0) = 2 := by
    classical
    have : Finset.sum Finset.univ (fun j : Fin N => if j = i then (2 : Rat) else 0) = 2 := by
      simpa using Finset.sum_ite_eq' Finset.univ i (fun _ => (2 : Rat))
    simpa [eq_comm] using this
  unfold BMatrix.mulVec laplacian1D
  let cRat : Rat := RealB.toRat hk c
  let hSq : Rat := RealB.toRat hk h * RealB.toRat hk h
  let term : Fin N → Rat :=
    fun j =>
      ((if j = forwardIndex N hN i then (1 : Rat) else 0) +
          (if j = backwardIndex N hN i then (1 : Rat) else 0) -
          if i = j then (2 : Rat) else 0) / hSq
  have hterm :
      Finset.sum Finset.univ term = (((1 : Rat) + 1 - 2) / hSq) := by
    unfold term
    rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib, hforward, hbackward, hdiag]
  calc
    Finset.sum Finset.univ (fun j => term j * cRat) = (Finset.sum Finset.univ term) * cRat := by
      simp [Finset.sum_mul]
    _ =
      cRat * (((1 : Rat) + 1 - 2) / hSq) := by
          rw [hterm, mul_comm]
    _ = 0 := by
          ring

end HeytingLean.BST.Analysis
