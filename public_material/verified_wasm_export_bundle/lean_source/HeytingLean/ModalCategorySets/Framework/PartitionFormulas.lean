import HeytingLean.ModalCategorySets.Framework.FiniteStateFrames
import HeytingLean.ModalCategorySets.Framework.FiniteTranslation

namespace HeytingLean.ModalCategorySets.Framework

open scoped Classical
open HeytingLean.ModalCategorySets.Framework.Equality

universe u

/-- All ordered pairs of distinct variables among the first `n` positions. -/
def orderedDistinctPairs (n : Nat) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun i =>
    (List.finRange n).filterMap fun j =>
      if _ : i ≠ j then some (Prod.mk i j) else none

@[simp] theorem mem_orderedDistinctPairs {n : Nat} {i j : Fin n} :
    Prod.mk i j ∈ orderedDistinctPairs n ↔ i ≠ j := by
  simp [orderedDistinctPairs]

/-- Equality conjunction for a list of `Fin n` pairs. -/
def eqPairsFormulaFin {n : Nat} (pairs : List (Fin n × Fin n)) : EqAssertion :=
  eqPairsFormula (pairs.map fun p => Prod.mk p.1.1 p.2.1)

/-- Disequality conjunction for a list of `Fin n` pairs. -/
def neqPairsFormulaFin {n : Nat} (pairs : List (Fin n × Fin n)) : EqAssertion :=
  neqPairsFormula (pairs.map fun p => Prod.mk p.1.1 p.2.1)

theorem holds_eqPairsFormulaFin_iff {admits : Accessibility} {α : Type u} {n : Nat}
    (ρ : Valuation α) (pairs : List (Fin n × Fin n)) :
    Holds admits ρ (eqPairsFormulaFin pairs) ↔
      ∀ p, p ∈ pairs → ρ p.1.1 = ρ p.2.1 := by
  constructor
  · intro h p hp
    exact
      (HeytingLean.ModalCategorySets.Framework.Equality.holds_eqPairsFormula_iff
        (admits := admits) (ρ := ρ)
        (pairs := pairs.map fun q => Prod.mk q.1.1 q.2.1)).mp
        (by simpa [eqPairsFormulaFin] using h)
        (Prod.mk p.1.1 p.2.1)
        (List.mem_map.mpr (Exists.intro p (And.intro hp rfl)))
  · intro h
    refine
      (HeytingLean.ModalCategorySets.Framework.Equality.holds_eqPairsFormula_iff
        (admits := admits) (ρ := ρ)
        (pairs := pairs.map fun q => Prod.mk q.1.1 q.2.1)).mpr ?_
    intro q hq
    rcases List.mem_map.mp hq with ⟨r, hr, hrEq⟩
    cases hrEq
    exact h r hr

theorem holds_neqPairsFormulaFin_iff {admits : Accessibility} {α : Type u} {n : Nat}
    (ρ : Valuation α) (pairs : List (Fin n × Fin n)) :
    Holds admits ρ (neqPairsFormulaFin pairs) ↔
      ∀ p, p ∈ pairs → ρ p.1.1 ≠ ρ p.2.1 := by
  constructor
  · intro h p hp
    exact
      (HeytingLean.ModalCategorySets.Framework.Equality.holds_neqPairsFormula_iff
        (admits := admits) (ρ := ρ)
        (pairs := pairs.map fun q => Prod.mk q.1.1 q.2.1)).mp
        (by simpa [neqPairsFormulaFin] using h)
        (Prod.mk p.1.1 p.2.1)
        (List.mem_map.mpr (Exists.intro p (And.intro hp rfl)))
  · intro h
    refine
      (HeytingLean.ModalCategorySets.Framework.Equality.holds_neqPairsFormula_iff
        (admits := admits) (ρ := ρ)
        (pairs := pairs.map fun q => Prod.mk q.1.1 q.2.1)).mpr ?_
    intro q hq
    rcases List.mem_map.mp hq with ⟨r, hr, hrEq⟩
    cases hrEq
    exact h r hr

/-- The equality pairs forced by a partition on the first `n` variables. -/
noncomputable def partitionEqPairs {n : Nat} (P : FinPartition n) : List (Fin n × Fin n) :=
  (orderedDistinctPairs n).filter fun p => P.r p.1 p.2

/-- The disequality pairs forced by a partition on the first `n` variables. -/
noncomputable def partitionNeqPairs {n : Nat} (P : FinPartition n) : List (Fin n × Fin n) :=
  (orderedDistinctPairs n).filter fun p => ¬ P.r p.1 p.2

/-- Canonical partition formula attached to a finite partition of the first `n` variables. -/
noncomputable def partitionFormulaOf {n : Nat} (P : FinPartition n) : EqAssertion :=
  EqAssertion.conj (eqPairsFormulaFin (partitionEqPairs P)) (neqPairsFormulaFin (partitionNeqPairs P))

/-- The partition realized by the first `n` variables of a valuation. -/
def realizedPartition {α : Type u} (ρ : Valuation α) (n : Nat) : FinPartition n :=
  kernelPartition fun i : Fin n => ρ i.1

@[simp] theorem mem_partitionEqPairs {n : Nat} {P : FinPartition n} {p : Fin n × Fin n} :
    p ∈ partitionEqPairs P ↔ p ∈ orderedDistinctPairs n ∧ P.r p.1 p.2 := by
  simp [partitionEqPairs]

@[simp] theorem mem_partitionNeqPairs {n : Nat} {P : FinPartition n} {p : Fin n × Fin n} :
    p ∈ partitionNeqPairs P ↔ p ∈ orderedDistinctPairs n ∧ ¬ P.r p.1 p.2 := by
  simp [partitionNeqPairs]

theorem holds_partitionFormulaOf_iff_realizedPartition {admits : Accessibility} {α : Type u}
    (ρ : Valuation α) {n : Nat} (P : FinPartition n) :
    Holds admits ρ (partitionFormulaOf P) ↔ realizedPartition ρ n = P := by
  constructor
  · rintro ⟨hEq, hNeq⟩
    ext i j
    change (realizedPartition ρ n).r i j ↔ P.r i j
    by_cases hij : i = j
    · subst hij
      constructor
      · intro _
        exact P.refl i
      · intro _
        rfl
    · constructor
      · intro hijEq
        by_contra hP
        have hmem : Prod.mk i j ∈ partitionNeqPairs P := by
          exact mem_partitionNeqPairs.mpr (And.intro ((mem_orderedDistinctPairs).2 hij) hP)
        have hijEq' : ρ i.1 = ρ j.1 := by
          change ρ i.1 = ρ j.1
          exact hijEq
        have hNeqij :
            ρ i.1 ≠ ρ j.1 :=
          (holds_neqPairsFormulaFin_iff (ρ := ρ) (pairs := partitionNeqPairs P)).mp hNeq
            (Prod.mk i j) hmem
        exact hNeqij hijEq'
      · intro hP
        have hmem : Prod.mk i j ∈ partitionEqPairs P := by
          exact mem_partitionEqPairs.mpr (And.intro ((mem_orderedDistinctPairs).2 hij) hP)
        have hEqij : ρ i.1 = ρ j.1 :=
          (holds_eqPairsFormulaFin_iff (ρ := ρ) (pairs := partitionEqPairs P)).mp hEq
            (Prod.mk i j) hmem
        change ρ i.1 = ρ j.1
        exact hEqij
  · intro hP
    have hEq :
        Holds admits ρ (eqPairsFormulaFin (partitionEqPairs P)) :=
      (holds_eqPairsFormulaFin_iff (ρ := ρ) (pairs := partitionEqPairs P)).mpr <| by
        intro p hp
        have hpRel : P.r p.1 p.2 := (mem_partitionEqPairs.mp hp).2
        have hReal : (realizedPartition ρ n).r p.1 p.2 := by simpa [hP] using hpRel
        change ρ p.1.1 = ρ p.2.1 at hReal
        exact hReal
    have hNeq :
        Holds admits ρ (neqPairsFormulaFin (partitionNeqPairs P)) :=
      (holds_neqPairsFormulaFin_iff (ρ := ρ) (pairs := partitionNeqPairs P)).mpr <| by
        intro p hp
        have hpRel : ¬ P.r p.1 p.2 := (mem_partitionNeqPairs.mp hp).2
        intro hEq
        apply hpRel
        have hReal : (realizedPartition ρ n).r p.1 p.2 := by
          change ρ p.1.1 = ρ p.2.1
          exact hEq
        simpa [hP] using hReal
    simpa [partitionFormulaOf] using And.intro hEq hNeq

theorem holds_partitionFormulaOf_realizedPartition {admits : Accessibility} {α : Type u}
    (ρ : Valuation α) (n : Nat) :
    Holds admits ρ (partitionFormulaOf (realizedPartition ρ n)) := by
  exact (holds_partitionFormulaOf_iff_realizedPartition (admits := admits)
    (ρ := ρ) (P := realizedPartition ρ n)).mpr rfl

theorem partitionFormulaOf_injective {admits : Accessibility} {α : Type u}
    {ρ : Valuation α} {n : Nat} {P Q : FinPartition n}
    (hP : Holds admits ρ (partitionFormulaOf P))
    (hQ : Holds admits ρ (partitionFormulaOf Q)) :
    P = Q := by
  rw [← (holds_partitionFormulaOf_iff_realizedPartition (admits := admits) (ρ := ρ) (P := P)).mp hP]
  rw [← (holds_partitionFormulaOf_iff_realizedPartition (admits := admits) (ρ := ρ) (P := Q)).mp hQ]

end HeytingLean.ModalCategorySets.Framework
