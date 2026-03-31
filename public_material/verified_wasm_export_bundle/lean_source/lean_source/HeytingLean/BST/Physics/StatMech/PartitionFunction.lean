import HeytingLean.BST.Numbers.Transcendental

/-!
# BST.Physics.StatMech.PartitionFunction

Finite canonical ensembles with bounded exponential weights.
-/

namespace HeytingLean.BST.Physics.StatMech

open HeytingLean.BST
open HeytingLean.BST.BoundedTranscendental

structure CanonicalEnsemble (Ω : Type*) [Fintype Ω] where
  H : Ω → Rat
  β : Rat
  β_pos : 0 < β

def partitionFunction {Ω : Type*} [Fintype Ω]
    (ens : CanonicalEnsemble Ω) (terms : ℕ) : Rat :=
  Finset.sum Finset.univ (fun ω => boundedExp (-ens.β * ens.H ω) terms)

def boltzmannWeight {Ω : Type*} [Fintype Ω]
    (ens : CanonicalEnsemble Ω) (terms : ℕ) (ω : Ω) : Rat :=
  boundedExp (-ens.β * ens.H ω) terms / partitionFunction ens terms

def averageEnergy {Ω : Type*} [Fintype Ω]
    (ens : CanonicalEnsemble Ω) (terms : ℕ) : Rat :=
  let Z := partitionFunction ens terms
  if Z = 0 then 0
  else Finset.sum Finset.univ (fun ω =>
    ens.H ω * boundedExp (-ens.β * ens.H ω) terms) / Z

def energyVariance {Ω : Type*} [Fintype Ω]
    (ens : CanonicalEnsemble Ω) (terms : ℕ) : Rat :=
  let Z := partitionFunction ens terms
  if Z = 0 then 0
  else
    let avgE := averageEnergy ens terms
    let avgE2 := Finset.sum Finset.univ (fun ω =>
      ens.H ω ^ 2 * boundedExp (-ens.β * ens.H ω) terms) / Z
    avgE2 - avgE ^ 2

theorem partitionFunction_pos {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (ens : CanonicalEnsemble Ω) (terms : ℕ) (ht : 0 < terms) :
    0 < partitionFunction ens terms := by
  classical
  let ω0 : Ω := Classical.choice ‹Nonempty Ω›
  have hnonneg :
      ∀ ω : Ω, 0 ≤ boundedExp (-ens.β * ens.H ω) terms := by
    intro ω
    exact le_of_lt (boundedExp_pos _ _ ht)
  have hω0 : 0 < boundedExp (-ens.β * ens.H ω0) terms :=
    boundedExp_pos _ _ ht
  unfold partitionFunction
  have hsum :
      Finset.sum Finset.univ (fun ω => boundedExp (-ens.β * ens.H ω) terms) =
        boundedExp (-ens.β * ens.H ω0) terms +
          Finset.sum (Finset.univ.erase ω0) (fun ω => boundedExp (-ens.β * ens.H ω) terms) := by
    have hω0_mem : ω0 ∈ (Finset.univ : Finset Ω) := by simp
    simpa [add_comm, add_left_comm, add_assoc] using
      (Finset.add_sum_erase
        (s := Finset.univ) (a := ω0)
        (f := fun ω => boundedExp (-ens.β * ens.H ω) terms) hω0_mem).symm
  have hrest :
      0 ≤ Finset.sum (Finset.univ.erase ω0) (fun ω => boundedExp (-ens.β * ens.H ω) terms) := by
    exact Finset.sum_nonneg (fun ω _ => hnonneg ω)
  rw [hsum]
  linarith

theorem boltzmannWeight_sum_one {Ω : Type*} [Fintype Ω]
    (ens : CanonicalEnsemble Ω) (terms : ℕ)
    (hZ : partitionFunction ens terms ≠ 0) :
    Finset.sum Finset.univ (fun ω => boltzmannWeight ens terms ω) = 1 := by
  unfold boltzmannWeight
  rw [← Finset.sum_div]
  rw [partitionFunction]
  exact div_self hZ

end HeytingLean.BST.Physics.StatMech
