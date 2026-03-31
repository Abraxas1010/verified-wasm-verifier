import HeytingLean.BST.Numbers.Transcendental

/-!
# BST.Physics.StatMech.Markov

Finite probability distributions, doubly stochastic transitions, and bounded
Shannon entropy.
-/

namespace HeytingLean.BST.Physics.StatMech

open HeytingLean.BST
open HeytingLean.BST.BoundedTranscendental

structure ProbDist (k : ℕ) (n : ℕ) where
  weights : Fin n → Rat
  nonneg : ∀ i, 0 ≤ weights i
  sum_one : Finset.sum Finset.univ weights = 1

structure DoublyStochastic (n : ℕ) where
  mat : Fin n → Fin n → Rat
  nonneg : ∀ i j, 0 ≤ mat i j
  row_sum : ∀ i, Finset.sum Finset.univ (fun j => mat i j) = 1
  col_sum : ∀ j, Finset.sum Finset.univ (fun i => mat i j) = 1

def applyTransition {k n : ℕ} (p : ProbDist k n) (T : DoublyStochastic n) :
    Fin n → Rat :=
  fun j => Finset.sum Finset.univ (fun i => p.weights i * T.mat i j)

def shannonEntropy (k : ℕ) {n : ℕ} (p : ProbDist k n) (terms : ℕ) : Rat :=
  -(Finset.sum Finset.univ (fun i =>
    let pi := p.weights i
    if pi = 0 then 0 else pi * boundedLn pi terms))

theorem weight_le_one {k n : ℕ} (p : ProbDist k n) (i : Fin n) :
    p.weights i ≤ 1 := by
  have hrest :
      0 ≤ Finset.sum (Finset.univ.erase i) (fun j => p.weights j) := by
    exact Finset.sum_nonneg (fun j _ => p.nonneg j)
  have hsum :
      Finset.sum Finset.univ (fun j => p.weights j) =
        p.weights i + Finset.sum (Finset.univ.erase i) (fun j => p.weights j) := by
    have hi_mem : i ∈ (Finset.univ : Finset (Fin n)) := by simp
    simpa [add_comm, add_left_comm, add_assoc] using
      (Finset.add_sum_erase (s := Finset.univ) (a := i) (f := fun j => p.weights j) hi_mem).symm
  have hi_le_sum : p.weights i ≤ Finset.sum Finset.univ (fun j => p.weights j) := by
    rw [hsum]
    linarith
  simpa [p.sum_one] using hi_le_sum

theorem applyTransition_nonneg {k n : ℕ} (p : ProbDist k n) (T : DoublyStochastic n) (j : Fin n) :
    0 ≤ applyTransition p T j := by
  unfold applyTransition
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (p.nonneg i) (T.nonneg i j))

theorem applyTransition_sum_one {k n : ℕ} (p : ProbDist k n) (T : DoublyStochastic n) :
    Finset.sum Finset.univ (applyTransition p T) = 1 := by
  classical
  unfold applyTransition
  rw [Finset.sum_comm]
  calc
    Finset.sum Finset.univ (fun i => Finset.sum Finset.univ (fun j => p.weights i * T.mat i j))
        = Finset.sum Finset.univ (fun i => p.weights i * Finset.sum Finset.univ (fun j => T.mat i j)) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
    _ = Finset.sum Finset.univ (fun i => p.weights i * 1) := by
            simp [T.row_sum]
    _ = 1 := by
            simp [p.sum_one]

theorem shannonEntropy_nonneg (k : ℕ) {n : ℕ} (p : ProbDist k n) (terms : ℕ) :
    0 ≤ shannonEntropy k p terms := by
  have hterm :
      ∀ i : Fin n,
        (let pi := p.weights i
         if pi = 0 then 0 else pi * boundedLn pi terms) ≤ 0 := by
    intro i
    by_cases hpi : p.weights i = 0
    · simp [hpi]
    · have hpi0 : 0 < p.weights i := lt_of_le_of_ne (p.nonneg i) (Ne.symm hpi)
      have hpi1 : p.weights i ≤ 1 := weight_le_one p i
      have hln : boundedLn (p.weights i) terms ≤ 0 :=
        boundedLn_nonpos_of_pos_le_one hpi0 hpi1 terms
      simp [hpi]
      exact mul_nonpos_of_nonneg_of_nonpos (p.nonneg i) hln
  have hsum :
      Finset.sum Finset.univ
        (fun i =>
          let pi := p.weights i
          if pi = 0 then 0 else pi * boundedLn pi terms) ≤ 0 := by
    exact Finset.sum_nonpos (fun i _ => hterm i)
  unfold shannonEntropy
  linarith

end HeytingLean.BST.Physics.StatMech
