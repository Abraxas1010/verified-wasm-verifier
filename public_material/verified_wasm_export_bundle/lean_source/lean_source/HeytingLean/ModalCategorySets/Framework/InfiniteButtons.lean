import HeytingLean.ModalCategorySets.Framework.InfinitePartitionElimination
import Mathlib.Tactic

namespace HeytingLean.ModalCategorySets.Framework

open scoped Classical
open HeytingLean.ModalCategorySets.Framework.Equality

universe u

namespace Buttons

def leftVar (i : Nat) : Var := 2 * i
def rightVar (i : Nat) : Var := 2 * i + 1

def leftFin {n : Nat} (i : Fin n) : Fin (2 * n) :=
  Fin.mk (leftVar i.1) (by
    dsimp [leftVar]
    omega)

def rightFin {n : Nat} (i : Fin n) : Fin (2 * n) :=
  Fin.mk (rightVar i.1) (by
    dsimp [rightVar]
    omega)

def pairEq (i : Nat) : EqAssertion :=
  .atomEq (leftVar i) (rightVar i)

def pairIndex {n : Nat} (v : Fin (2 * n)) : Fin n :=
  Fin.mk (v.1 / 2) (by
    have hv := v.2
    omega)

def patternCode (n : Nat) (s : Finset (Fin n)) : Fin (2 * n) → Fin n ⊕ Fin (2 * n) :=
  fun v => if pairIndex v ∈ s then Sum.inl (pairIndex v) else Sum.inr v

def patternPartition (n : Nat) (s : Finset (Fin n)) : FinPartition (2 * n) where
  r a b := patternCode n s a = patternCode n s b
  iseqv := by
    refine Equivalence.mk ?_ ?_ ?_
    · intro a
      rfl
    · intro a b h
      exact h.symm
    · intro a b c hab hbc
      exact hab.trans hbc

@[simp] theorem pairIndex_leftFin {n : Nat} (i : Fin n) :
    pairIndex (leftFin i) = i := by
  apply Fin.ext
  change leftVar i.1 / 2 = i.1
  simp [leftVar]

@[simp] theorem pairIndex_rightFin {n : Nat} (i : Fin n) :
    pairIndex (rightFin i) = i := by
  apply Fin.ext
  change (2 * i.1 + 1) / 2 = i.1
  simpa [Nat.bit_val] using (Nat.bit_div_two true i.1)

theorem leftFin_ne_rightFin {n : Nat} (i : Fin n) :
    leftFin i ≠ rightFin i := by
  intro hEq
  have hVal : 2 * i.1 = 2 * i.1 + 1 := by
    have hVal' : leftVar i.1 = rightVar i.1 := congrArg Fin.val hEq
    unfold leftVar rightVar at hVal'
    exact hVal'
  exact (Nat.two_mul_ne_two_mul_add_one (n := i.1) (m := i.1)) hVal

@[simp] theorem patternPartition_pair_eq_iff {n : Nat} (s : Finset (Fin n)) (i : Fin n) :
    (patternPartition n s).r (leftFin i) (rightFin i) ↔ i ∈ s := by
  change patternCode n s (leftFin i) = patternCode n s (rightFin i) ↔ i ∈ s
  dsimp [patternCode]
  rw [pairIndex_leftFin]
  rw [pairIndex_rightFin]
  by_cases hi : i ∈ s
  · simp [hi]
  · constructor
    · intro h
      simp [hi] at h
      exact False.elim ((leftFin_ne_rightFin i) h)
    · intro h
      exact False.elim (hi h)

theorem refines_from_discretePartition {n : Nat} (Q : FinPartition n) :
    Refines (discretePartition n) Q := by
  intro i j hij
  change i = j at hij
  cases hij
  exact Q.refl i

theorem realizedPartition_eq_discrete_of_injective {α : Type u} {n : Nat}
    (ρ : Valuation α) (hInj : Function.Injective (fun i : Fin n => ρ i.1)) :
    realizedPartition ρ n = discretePartition n := by
  ext i j
  change ρ i.1 = ρ j.1 ↔ i = j
  constructor
  · intro hEq
    exact hInj hEq
  · intro hij
    cases hij
    rfl

@[simp] theorem infinitePartitionWitnessValuation_leftVar {n : Nat}
    (P : FinPartition (2 * n)) (i : Fin n) :
    infinitePartitionWitnessValuation P (leftVar i.1) =
      Sum.inl (partitionTuple P (leftFin i)) := by
  exact bindTuple_lt (ρ := fun _ => Sum.inr 0)
    (xs := fun j => Sum.inl (partitionTuple P j))
    (v := leftVar i.1)
    (by
      dsimp [leftVar]
      omega)

@[simp] theorem infinitePartitionWitnessValuation_rightVar {n : Nat}
    (P : FinPartition (2 * n)) (i : Fin n) :
    infinitePartitionWitnessValuation P (rightVar i.1) =
      Sum.inl (partitionTuple P (rightFin i)) := by
  exact bindTuple_lt (ρ := fun _ => Sum.inr 0)
    (xs := fun j => Sum.inl (partitionTuple P j))
    (v := rightVar i.1)
    (by
      dsimp [rightVar]
      omega)

@[simp] theorem infinitePartitionWitnessValuationLift_leftVar {n : Nat}
    (P : FinPartition (2 * n)) (i : Fin n) :
    infinitePartitionWitnessValuationLift P (leftVar i.1) =
      ULift.up (Sum.inl (partitionTuple P (leftFin i))) := by
  unfold infinitePartitionWitnessValuationLift
  rw [infinitePartitionWitnessValuation_leftVar]

@[simp] theorem infinitePartitionWitnessValuationLift_rightVar {n : Nat}
    (P : FinPartition (2 * n)) (i : Fin n) :
    infinitePartitionWitnessValuationLift P (rightVar i.1) =
      ULift.up (Sum.inl (partitionTuple P (rightFin i))) := by
  unfold infinitePartitionWitnessValuationLift
  rw [infinitePartitionWitnessValuation_rightVar]

theorem pairEq_holds_witness_iff {n : Nat} (s : Finset (Fin n)) (i : Fin n) :
    HoldsInfAll (infinitePartitionWitnessValuationLift (patternPartition n s))
      (pairEq i.1) ↔ i ∈ s := by
  have hPure : Equality.IsPure (pairEq i.1) := by trivial
  rw [holdsInfAll_pure_iff_holds _ hPure]
  change infinitePartitionWitnessValuationLift (patternPartition n s) (leftVar i.1) =
      infinitePartitionWitnessValuationLift (patternPartition n s) (rightVar i.1) ↔ i ∈ s
  rw [infinitePartitionWitnessValuationLift_leftVar (patternPartition n s) i]
  rw [infinitePartitionWitnessValuationLift_rightVar (patternPartition n s) i]
  constructor
  · intro h
    apply (patternPartition_pair_eq_iff s i).mp
    apply Quotient.exact
    exact Sum.inl.inj (ULift.up.inj h)
  · intro hi
    exact congrArg (fun q => ULift.up (Sum.inl q))
      (Quot.sound ((patternPartition_pair_eq_iff s i).mpr hi))

theorem pairEq_usesOnlyLT {n : Nat} (i : Fin n) :
    Equality.UsesOnlyLT (2 * n) (pairEq i.1) := by
  change leftVar i.1 < 2 * n ∧ rightVar i.1 < 2 * n
  have hi : i.1 < n := i.2
  constructor
  · dsimp [leftVar]
    exact Nat.mul_lt_mul_of_pos_left hi (by decide)
  · dsimp [rightVar]
    have hsucc : i.1 + 1 ≤ n := Nat.succ_le_of_lt hi
    have hmul : 2 * (i.1 + 1) ≤ 2 * n := Nat.mul_le_mul_left 2 hsucc
    have hlt : 2 * i.1 + 1 < 2 * (i.1 + 1) := by omega
    exact lt_of_lt_of_le hlt hmul

theorem allFunctions_pattern_holds_iff {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat}
    (hInj : Function.Injective (fun i : Fin (2 * n) => ρ i.1))
    (s : Finset (Fin n)) (i : Fin n) :
    let hRef : Refines (realizedPartition ρ (2 * n)) (patternPartition n s) := by
      rw [realizedPartition_eq_discrete_of_injective ρ hInj]
      exact refines_from_discretePartition (patternPartition n s)
    let σ : Valuation (ULift (InfinitePartitionWitnessWorld (patternPartition n s))) :=
      fun k => ULift.up (allFunctionsInfiniteCoarseningMap ρ hRef (ρ k))
    HoldsInfAll σ (pairEq i.1) ↔ i ∈ s := by
  intro hRef σ
  have hPart :
      realizedPartition σ (2 * n) = patternPartition n s := by
    change realizedPartition
      (fun k => ULift.up (allFunctionsInfiniteCoarseningMap ρ hRef (ρ k))) (2 * n) =
        patternPartition n s
    rw [realizedPartition_ulift]
    exact realizedPartition_allFunctionsInfiniteCoarseningMap ρ hRef
  exact (holdsInfAll_of_realizedPartition_eq
      (ρ := σ)
      (σ := infinitePartitionWitnessValuationLift (patternPartition n s))
      (n := 2 * n)
      (φ := pairEq i.1)
      (hUses := pairEq_usesOnlyLT (n := n) i)
      (hPart := hPart.trans (realizedPartition_infinitePartitionWitnessValuationLift (patternPartition n s)).symm)).trans
    (pairEq_holds_witness_iff s i)

theorem surjections_pattern_holds_iff {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat}
    (hInj : Function.Injective (fun i : Fin (2 * n) => ρ i.1))
    (s : Finset (Fin n)) (i : Fin n) :
    let hRef : Refines (realizedPartition ρ (2 * n)) (patternPartition n s) := by
      rw [realizedPartition_eq_discrete_of_injective ρ hInj]
      exact refines_from_discretePartition (patternPartition n s)
    let σ : Valuation (InfiniteSurjCoarseningWorld ρ (patternPartition n s)) :=
      fun k => surjectionInfiniteCoarseningMap ρ hRef (ρ k)
    HoldsInfSurj σ (pairEq i.1) ↔ i ∈ s := by
  intro hRef σ
  have hPart :
      realizedPartition σ (2 * n) = patternPartition n s :=
    realizedPartition_surjectionInfiniteCoarseningMap ρ hRef
  exact (holdsInfSurj_of_realizedPartition_eq
      (ρ := σ)
      (σ := infinitePartitionWitnessValuationLift (patternPartition n s))
      (n := 2 * n)
      (φ := pairEq i.1)
      (hUses := pairEq_usesOnlyLT (n := n) i)
      (hPart := hPart.trans (realizedPartition_infinitePartitionWitnessValuationLift (patternPartition n s)).symm)).trans
    (pairEq_holds_witness_iff s i)

theorem allFunctions_button_unpushed_at_root {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat}
    (hInj : Function.Injective (fun i : Fin (2 * n) => ρ i.1))
    (i : Fin n) :
    ¬ HoldsInfAll ρ (pairEq i.1) := by
  rw [holdsInfAll_pure_iff_holds (ρ := ρ) (φ := pairEq i.1) (by trivial)]
  intro hEq
  change ρ (leftVar i.1) = ρ (rightVar i.1) at hEq
  have hFinEq : leftFin i = rightFin i := by
    change ρ ((leftFin i).1) = ρ ((rightFin i).1) at hEq
    apply hInj
    exact hEq
  have hVal : 2 * i.1 = 2 * i.1 + 1 := by
    have hVal' : leftVar i.1 = rightVar i.1 := congrArg Fin.val hFinEq
    unfold leftVar rightVar at hVal'
    exact hVal'
  exact (Nat.two_mul_ne_two_mul_add_one (n := i.1) (m := i.1)) hVal

theorem surjections_button_unpushed_at_root {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat}
    (hInj : Function.Injective (fun i : Fin (2 * n) => ρ i.1))
    (i : Fin n) :
    ¬ HoldsInfSurj ρ (pairEq i.1) := by
  rw [holdsInfSurj_pure_iff_holds (ρ := ρ) (φ := pairEq i.1) (by trivial)]
  intro hEq
  change ρ (leftVar i.1) = ρ (rightVar i.1) at hEq
  have hFinEq : leftFin i = rightFin i := by
    change ρ ((leftFin i).1) = ρ ((rightFin i).1) at hEq
    apply hInj
    exact hEq
  have hVal : 2 * i.1 = 2 * i.1 + 1 := by
    have hVal' : leftVar i.1 = rightVar i.1 := congrArg Fin.val hFinEq
    unfold leftVar rightVar at hVal'
    exact hVal'
  exact (Nat.two_mul_ne_two_mul_add_one (n := i.1) (m := i.1)) hVal

def prefixInjective {α : Type u} (ρ : Valuation α) (n : Nat) : Prop :=
  Function.Injective (fun i : Fin n => ρ i.1)

def ButtonPatternAll {β : Type u} [Infinite β] {n : Nat}
    (σ : Valuation β) (s : Finset (Fin n)) : Prop :=
  ∀ i, HoldsInfAll σ (pairEq i.1) ↔ i ∈ s

def ButtonPatternSurj {β : Type u} [Infinite β] {n : Nat}
    (σ : Valuation β) (s : Finset (Fin n)) : Prop :=
  ∀ i, HoldsInfSurj σ (pairEq i.1) ↔ i ∈ s

structure AllButtonPatternWitness {α : Type u} [Infinite α] (ρ : Valuation α)
    {n : Nat} (s : Finset (Fin n)) where
  β : Type u
  hβ : Infinite β
  f : α → β
  pattern : @ButtonPatternAll β hβ _ (fun k => f (ρ k)) s

structure SurjButtonPatternWitness {α : Type u} [Infinite α] (ρ : Valuation α)
    {n : Nat} (s : Finset (Fin n)) where
  β : Type u
  hβ : Infinite β
  f : α → β
  hsurj : Function.Surjective f
  pattern : @ButtonPatternSurj β hβ _ (fun k => f (ρ k)) s

theorem prefixInjective_nat (n : Nat) :
    prefixInjective (fun k : Nat => k) n := by
  intro i j h
  exact Fin.ext h

theorem exists_allFunctions_button_pattern {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat}
    (hInj : prefixInjective ρ (2 * n))
    (s : Finset (Fin n)) :
    Nonempty (AllButtonPatternWitness (ρ := ρ) (s := s)) := by
  let hRef : Refines (realizedPartition ρ (2 * n)) (patternPartition n s) := by
    rw [realizedPartition_eq_discrete_of_injective ρ hInj]
    exact refines_from_discretePartition (patternPartition n s)
  let β : Type u := ULift (InfinitePartitionWitnessWorld (patternPartition n s))
  let hβ : Infinite β := inferInstance
  let f : α → β := fun a => ULift.up (allFunctionsInfiniteCoarseningMap ρ hRef a)
  refine Nonempty.intro ?_
  refine AllButtonPatternWitness.mk β hβ f ?_
  intro i
  dsimp [f]
  exact allFunctions_pattern_holds_iff (ρ := ρ) (hInj := hInj) s i

theorem exists_surjections_button_pattern {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat}
    (hInj : prefixInjective ρ (2 * n))
    (s : Finset (Fin n)) :
    Nonempty (SurjButtonPatternWitness (ρ := ρ) (s := s)) := by
  let hRef : Refines (realizedPartition ρ (2 * n)) (patternPartition n s) := by
    rw [realizedPartition_eq_discrete_of_injective ρ hInj]
    exact refines_from_discretePartition (patternPartition n s)
  let β : Type u := InfiniteSurjCoarseningWorld ρ (patternPartition n s)
  let hβ : Infinite β := inferInstance
  let f : α → β := surjectionInfiniteCoarseningMap ρ hRef
  refine Nonempty.intro ?_
  refine SurjButtonPatternWitness.mk β hβ f ?_ ?_
  · simpa [f] using surjectionInfiniteCoarseningMap_surjective ρ hRef
  · intro i
    dsimp [f]
    exact surjections_pattern_holds_iff (ρ := ρ) (hInj := hInj) s i

theorem nat_admits_allFunctions_button_pattern {n : Nat} (s : Finset (Fin n)) :
    Nonempty (AllButtonPatternWitness (ρ := fun k : Nat => k) (s := s)) :=
  exists_allFunctions_button_pattern (ρ := fun k : Nat => k)
    (hInj := prefixInjective_nat (2 * n))
    s

theorem nat_admits_surjections_button_pattern {n : Nat} (s : Finset (Fin n)) :
    Nonempty (SurjButtonPatternWitness (ρ := fun k : Nat => k) (s := s)) :=
  exists_surjections_button_pattern (ρ := fun k : Nat => k)
    (hInj := prefixInjective_nat (2 * n))
    s

end Buttons

end HeytingLean.ModalCategorySets.Framework
