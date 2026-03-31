import HeytingLean.BST.Numbers.Transcendental

/-!
# BST.Physics.StatMech.Ising

Finite Ising spins with exact rational Hamiltonians.
-/

namespace HeytingLean.BST.Physics.StatMech

open HeytingLean.BST

abbrev IsingState (N : ℕ) := Fin N → Bool

def spinValue (b : Bool) : Rat := if b then 1 else -1

def flipState {N : ℕ} (σ : IsingState N) : IsingState N := fun i => !(σ i)

def isingHamiltonian {N : ℕ} (J h_field : Rat)
    (neighbors : Fin N → Finset (Fin N)) (σ : IsingState N) : Rat :=
  let coupling := Finset.sum Finset.univ (fun i =>
    Finset.sum (neighbors i) (fun j => spinValue (σ i) * spinValue (σ j)))
  let field := Finset.sum Finset.univ (fun i => spinValue (σ i))
  (-J * coupling / 2) - h_field * field

def allUp (N : ℕ) : IsingState N := fun _ => true

def allDown (N : ℕ) : IsingState N := fun _ => false

def magnetization {N : ℕ} (σ : IsingState N) : Rat :=
  Finset.sum Finset.univ (fun i => spinValue (σ i)) / N

@[simp] theorem spinValue_true : spinValue true = 1 := by
  simp [spinValue]

@[simp] theorem spinValue_false : spinValue false = -1 := by
  simp [spinValue]

theorem spinValue_flip (b : Bool) : spinValue (!b) = -spinValue b := by
  cases b <;> simp [spinValue]

theorem allUp_magnetization (N : ℕ) (hN : 0 < N) :
    magnetization (allUp N) = 1 := by
  unfold magnetization allUp
  simp
  field_simp [show (N : Rat) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hN)]

theorem allDown_magnetization (N : ℕ) (hN : 0 < N) :
    magnetization (allDown N) = -1 := by
  unfold magnetization allDown
  simp
  field_simp [show (N : Rat) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hN)]

theorem isingHamiltonian_flip_symmetry {N : ℕ} (J : Rat)
    (neighbors : Fin N → Finset (Fin N)) (σ : IsingState N) :
    isingHamiltonian J 0 neighbors (flipState σ) =
    isingHamiltonian J 0 neighbors σ := by
  unfold isingHamiltonian flipState
  simp [spinValue_flip]

end HeytingLean.BST.Physics.StatMech
