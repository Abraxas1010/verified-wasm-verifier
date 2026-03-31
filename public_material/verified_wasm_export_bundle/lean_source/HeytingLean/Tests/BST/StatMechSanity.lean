import HeytingLean.BST.Physics

namespace HeytingLean.Tests.BST.StatMechSanity

open HeytingLean.BST
open HeytingLean.BST.Analysis
open HeytingLean.BST.Physics.StatMech

lemma hN3 : 0 < 3 := by decide

def neighbors3 (i : Fin 3) : Finset (Fin 3) :=
  {forwardIndex 3 hN3 i, backwardIndex 3 hN3 i}

def uniform2 : ProbDist 1 2 where
  weights := fun _ => (1 : Rat) / 2
  nonneg := by
    intro i
    norm_num
  sum_one := by
    native_decide

def idTransition2 : DoublyStochastic 2 where
  mat := fun i j => if i = j then 1 else 0
  nonneg := by
    intro i j
    by_cases h : i = j <;> simp [h]
  row_sum := by
    intro i
    fin_cases i <;> native_decide
  col_sum := by
    intro j
    fin_cases j <;> native_decide

def boolEnsemble : CanonicalEnsemble Bool where
  H := fun _ => 0
  β := 1
  β_pos := by norm_num

example : magnetization (allUp 3) = 1 := by
  exact allUp_magnetization 3 hN3

example :
    isingHamiltonian 1 0 neighbors3 (flipState (allDown 3)) =
      isingHamiltonian 1 0 neighbors3 (allDown 3) := by
  exact isingHamiltonian_flip_symmetry 1 neighbors3 (allDown 3)

example : Finset.sum Finset.univ (applyTransition uniform2 idTransition2) = 1 := by
  exact applyTransition_sum_one uniform2 idTransition2

example : 0 ≤ shannonEntropy 1 uniform2 5 := by
  exact shannonEntropy_nonneg 1 uniform2 5

example : partitionFunction boolEnsemble 1 = 2 := by
  native_decide

example : boltzmannWeight boolEnsemble 1 false = (1 : Rat) / 2 := by
  native_decide

example : Finset.sum Finset.univ (fun ω => boltzmannWeight boolEnsemble 1 ω) = 1 := by
  have hZ : partitionFunction boolEnsemble 1 ≠ 0 := by
    native_decide
  exact boltzmannWeight_sum_one boolEnsemble 1 hZ

end HeytingLean.Tests.BST.StatMechSanity
