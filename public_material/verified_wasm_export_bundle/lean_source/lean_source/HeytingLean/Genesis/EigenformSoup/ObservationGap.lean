import Mathlib

/-!
# Genesis.EigenformSoup.ObservationGap

Observation-gap contracts (`j(P) ≤ P`) and runtime numeric proxies.
-/

namespace HeytingLean.Genesis.EigenformSoup

/-- Order-theoretic observation-gap predicate (`j(P) ≤ P`). -/
def ObservationGap {α : Type*} [Preorder α] (j : α → α) (P : α) : Prop :=
  j P ≤ P

/-- Numeric observation-gap proxy (`expected - observed`). -/
def observationGapNat (expected observed : Nat) : Nat :=
  expected - observed

theorem observationGapNat_eq_zero_of_ge
    {expected observed : Nat} (h : expected ≤ observed) :
    observationGapNat expected observed = 0 := by
  simp [observationGapNat, Nat.sub_eq_zero_of_le h]

theorem observationGapNat_pos_of_lt
    {expected observed : Nat} (h : observed < expected) :
    0 < observationGapNat expected observed := by
  simpa [observationGapNat] using Nat.sub_pos_of_lt h

/-- Mean observation-gap proxy over finite samples (Nat floor division). -/
def meanObservationGapNat (xs : List Nat) : Nat :=
  if _h : xs.length = 0 then
    0
  else
    xs.foldl (· + ·) 0 / xs.length

theorem meanObservationGapNat_nil :
    meanObservationGapNat [] = 0 := by
  simp [meanObservationGapNat]

theorem meanObservationGapNat_nonneg (xs : List Nat) :
    0 ≤ meanObservationGapNat xs := by
  exact Nat.zero_le _

end HeytingLean.Genesis.EigenformSoup
