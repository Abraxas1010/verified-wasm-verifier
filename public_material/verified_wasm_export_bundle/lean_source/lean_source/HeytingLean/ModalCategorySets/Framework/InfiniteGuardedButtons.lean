import HeytingLean.ModalCategorySets.Framework.InfiniteButtons

namespace HeytingLean.ModalCategorySets.Framework

open scoped Classical
open HeytingLean.ModalCategorySets.Framework.Equality

universe u

namespace Buttons

/-- The paper's cross-wiring guard: some equality appears across two different parameter-pairs. -/
def crossWiringAtoms (n : Nat) : List EqAssertion :=
  (orderedDistinctPairs n).flatMap fun p =>
    EqAssertion.atomEq (leftVar p.1.1) (leftVar p.2.1) ::
      EqAssertion.atomEq (leftVar p.1.1) (rightVar p.2.1) ::
        EqAssertion.atomEq (rightVar p.1.1) (rightVar p.2.1) ::
          []

/-- The cross-wiring guard `ρ(\bar u,\bar v)` from the paper. -/
def crossWiring (n : Nat) : EqAssertion :=
  Equality.disjList (crossWiringAtoms n)

/-- Equality pattern saying one ordered pair is cross-wired. -/
def CrossWiredPair {α : Type u} (ρ : Valuation α) {n : Nat} (p : Fin n × Fin n) : Prop :=
  (ρ (leftVar p.1.1) = ρ (leftVar p.2.1)) ∨
    ((ρ (leftVar p.1.1) = ρ (rightVar p.2.1)) ∨
      (ρ (rightVar p.1.1) = ρ (rightVar p.2.1)))

/-- Semantic predicate matching the paper's cross-wiring guard. -/
def CrossWiredAt {α : Type u} (ρ : Valuation α) (n : Nat) : Prop :=
  Exists fun p : (Fin n × Fin n) => p.1 ≠ p.2 ∧ CrossWiredPair ρ p

/-- The guarded button family used in the paper's upper-bound proof. -/
def guardedButton {n : Nat} (i : Fin n) : EqAssertion :=
  .disj (pairEq i.1) (crossWiring n)

theorem isPure_crossWiring (n : Nat) :
    Equality.IsPure (crossWiring n) := by
  unfold crossWiring crossWiringAtoms
  apply isPure_disjList
  intro φ hφ
  rcases List.mem_flatMap.mp hφ with ⟨p, -, hp⟩
  simp at hp
  rcases hp with rfl | rfl | rfl <;> trivial

theorem holds_crossWiring_iff {admits : Accessibility} {α : Type u}
    (ρ : Valuation α) (n : Nat) :
    Holds admits ρ (crossWiring n) ↔ CrossWiredAt ρ n := by
  unfold crossWiring
  constructor
  · intro h
    rcases (Equality.holds_disjList_iff (ρ := ρ) (crossWiringAtoms n)).mp h with
      ⟨φ, hφ, hholds⟩
    unfold crossWiringAtoms at hφ
    rcases List.mem_flatMap.mp hφ with ⟨p, hp, hmem⟩
    have hpNe : p.1 ≠ p.2 := (mem_orderedDistinctPairs.mp hp)
    simp at hmem
    rcases hmem with rfl | rfl | rfl
    · have hEq : ρ (leftVar p.1.1) = ρ (leftVar p.2.1) := by simpa using hholds
      exact Exists.intro p (And.intro hpNe (Or.inl hEq))
    · have hEq : ρ (leftVar p.1.1) = ρ (rightVar p.2.1) := by simpa using hholds
      exact Exists.intro p (And.intro hpNe (Or.inr (Or.inl hEq)))
    · have hEq : ρ (rightVar p.1.1) = ρ (rightVar p.2.1) := by simpa using hholds
      exact Exists.intro p (And.intro hpNe (Or.inr (Or.inr hEq)))
  · intro hCross
    rcases hCross with ⟨p, hpNe, hEq | hEq | hEq⟩
    · refine (Equality.holds_disjList_iff (ρ := ρ) (crossWiringAtoms n)).mpr ?_
      refine Exists.intro (EqAssertion.atomEq (leftVar p.1.1) (leftVar p.2.1)) ?_
      refine And.intro ?_ ?_
      · unfold crossWiringAtoms
        refine List.mem_flatMap.mpr ?_
        refine Exists.intro p ?_
        refine And.intro ((mem_orderedDistinctPairs).2 hpNe) ?_
        simp
      · exact hEq
    · refine (Equality.holds_disjList_iff (ρ := ρ) (crossWiringAtoms n)).mpr ?_
      refine Exists.intro (EqAssertion.atomEq (leftVar p.1.1) (rightVar p.2.1)) ?_
      refine And.intro ?_ ?_
      · unfold crossWiringAtoms
        refine List.mem_flatMap.mpr ?_
        refine Exists.intro p ?_
        refine And.intro ((mem_orderedDistinctPairs).2 hpNe) ?_
        simp
      · exact hEq
    · refine (Equality.holds_disjList_iff (ρ := ρ) (crossWiringAtoms n)).mpr ?_
      refine Exists.intro (EqAssertion.atomEq (rightVar p.1.1) (rightVar p.2.1)) ?_
      refine And.intro ?_ ?_
      · unfold crossWiringAtoms
        refine List.mem_flatMap.mpr ?_
        refine Exists.intro p ?_
        refine And.intro ((mem_orderedDistinctPairs).2 hpNe) ?_
        simp
      · exact hEq

theorem patternPartition_rel_false_of_pairIndex_ne {n : Nat} (s : Finset (Fin n))
    {a b : Fin (2 * n)} (hab : pairIndex a ≠ pairIndex b) :
    ¬ (patternPartition n s).r a b := by
  unfold patternPartition
  change patternCode n s a = patternCode n s b → False
  by_cases ha : pairIndex a ∈ s <;> by_cases hb : pairIndex b ∈ s
  · intro hEq
    have hpa : patternCode n s a = Sum.inl (pairIndex a) := by
      unfold patternCode
      rw [if_pos ha]
    have hpb : patternCode n s b = Sum.inl (pairIndex b) := by
      unfold patternCode
      rw [if_pos hb]
    have hEq' : (Sum.inl (pairIndex a) : Fin n ⊕ Fin (2 * n)) = Sum.inl (pairIndex b) := by
      exact hpa.symm.trans (hEq.trans hpb)
    have hIdx : pairIndex a = pairIndex b := Sum.inl.inj hEq'
    exact hab hIdx
  · intro hEq
    have hpa : patternCode n s a = Sum.inl (pairIndex a) := by
      unfold patternCode
      rw [if_pos ha]
    have hpb : patternCode n s b = Sum.inr b := by
      unfold patternCode
      rw [if_neg hb]
    have hImpossible : (Sum.inl (pairIndex a) : Fin n ⊕ Fin (2 * n)) = Sum.inr b := by
      exact hpa.symm.trans (hEq.trans hpb)
    cases hImpossible
  · intro hEq
    have hpa : patternCode n s a = Sum.inr a := by
      unfold patternCode
      rw [if_neg ha]
    have hpb : patternCode n s b = Sum.inl (pairIndex b) := by
      unfold patternCode
      rw [if_pos hb]
    have hImpossible : (Sum.inr a : Fin n ⊕ Fin (2 * n)) = Sum.inl (pairIndex b) := by
      exact hpa.symm.trans (hEq.trans hpb)
    cases hImpossible
  · intro hEq
    have hpa : patternCode n s a = Sum.inr a := by
      unfold patternCode
      rw [if_neg ha]
    have hpb : patternCode n s b = Sum.inr b := by
      unfold patternCode
      rw [if_neg hb]
    have hEq' : (Sum.inr a : Fin n ⊕ Fin (2 * n)) = Sum.inr b := by
      exact hpa.symm.trans (hEq.trans hpb)
    have habEq : a = b := Sum.inr.inj hEq'
    exact hab (congrArg pairIndex habEq)

theorem patternPartition_refines_of_subset {n : Nat} {s t : Finset (Fin n)}
    (hst : s ⊆ t) :
    Refines (patternPartition n s) (patternPartition n t) := by
  intro a b hab
  change patternCode n s a = patternCode n s b at hab
  change patternCode n t a = patternCode n t b
  by_cases ha : pairIndex a ∈ s
  · by_cases hb : pairIndex b ∈ s
    ·
      have hpa : patternCode n s a = Sum.inl (pairIndex a) := by
        unfold patternCode
        rw [if_pos ha]
      have hpb : patternCode n s b = Sum.inl (pairIndex b) := by
        unfold patternCode
        rw [if_pos hb]
      have hEq : (Sum.inl (pairIndex a) : Fin n ⊕ Fin (2 * n)) = Sum.inl (pairIndex b) := by
        exact hpa.symm.trans (hab.trans hpb)
      have hat : pairIndex a ∈ t := hst ha
      have hbt : pairIndex b ∈ t := hst hb
      have hta : patternCode n t a = Sum.inl (pairIndex a) := by
        unfold patternCode
        exact if_pos hat
      have htb : patternCode n t b = Sum.inl (pairIndex b) := by
        unfold patternCode
        exact if_pos hbt
      exact hta.trans (hEq.trans htb.symm)
    ·
      have hpa : patternCode n s a = Sum.inl (pairIndex a) := by
        unfold patternCode
        rw [if_pos ha]
      have hpb : patternCode n s b = Sum.inr b := by
        unfold patternCode
        rw [if_neg hb]
      have hImpossible : (Sum.inl (pairIndex a) : Fin n ⊕ Fin (2 * n)) = Sum.inr b := by
        exact hpa.symm.trans (hab.trans hpb)
      cases hImpossible
  · by_cases hb : pairIndex b ∈ s
    ·
      have hpa : patternCode n s a = Sum.inr a := by
        unfold patternCode
        rw [if_neg ha]
      have hpb : patternCode n s b = Sum.inl (pairIndex b) := by
        unfold patternCode
        rw [if_pos hb]
      have hImpossible : (Sum.inr a : Fin n ⊕ Fin (2 * n)) = Sum.inl (pairIndex b) := by
        exact hpa.symm.trans (hab.trans hpb)
      cases hImpossible
    ·
      have hpa : patternCode n s a = Sum.inr a := by
        unfold patternCode
        rw [if_neg ha]
      have hpb : patternCode n s b = Sum.inr b := by
        unfold patternCode
        rw [if_neg hb]
      have hEq : (Sum.inr a : Fin n ⊕ Fin (2 * n)) = Sum.inr b := by
        exact hpa.symm.trans (hab.trans hpb)
      have habEq : a = b := Sum.inr.inj hEq
      subst b
      rfl

theorem leftFin_ne_leftFin_of_ne {n : Nat} {j k : Fin n} (hjk : j ≠ k) :
    leftFin j ≠ leftFin k := by
  intro h
  exact hjk (pairIndex_leftFin j ▸ pairIndex_leftFin k ▸ congrArg pairIndex h)

theorem rightFin_ne_rightFin_of_ne {n : Nat} {j k : Fin n} (hjk : j ≠ k) :
    rightFin j ≠ rightFin k := by
  intro h
  exact hjk (pairIndex_rightFin j ▸ pairIndex_rightFin k ▸ congrArg pairIndex h)

theorem leftFin_ne_rightFin_any {n : Nat} (j k : Fin n) :
    leftFin j ≠ rightFin k := by
  intro h
  have hVal : 2 * j.1 = 2 * k.1 + 1 := congrArg Fin.val h
  omega

theorem crossWiring_false_of_realizedPartition_eq_pattern_holds
    {admits : Accessibility} {α : Type u} (ρ : Valuation α) {n : Nat} (s : Finset (Fin n))
    (hPart : realizedPartition ρ (2 * n) = patternPartition n s) :
    ¬ Holds admits ρ (crossWiring n) := by
  intro hCross
  rcases (holds_crossWiring_iff (admits := admits) (ρ := ρ) n).mp hCross with
    ⟨p, hpNe, hEq | hEq | hEq⟩
  · have hRel : (realizedPartition ρ (2 * n)).r (leftFin p.1) (leftFin p.2) := by
      change ρ ((leftFin p.1).1) = ρ ((leftFin p.2).1)
      simpa using hEq
    have : (patternPartition n s).r (leftFin p.1) (leftFin p.2) := by simpa [hPart] using hRel
    have hPairIdx : pairIndex (leftFin p.1) ≠ pairIndex (leftFin p.2) := by
      simpa using hpNe
    exact patternPartition_rel_false_of_pairIndex_ne s hPairIdx this
  · have hRel : (realizedPartition ρ (2 * n)).r (leftFin p.1) (rightFin p.2) := by
      change ρ ((leftFin p.1).1) = ρ ((rightFin p.2).1)
      simpa using hEq
    have : (patternPartition n s).r (leftFin p.1) (rightFin p.2) := by simpa [hPart] using hRel
    have hPairIdx : pairIndex (leftFin p.1) ≠ pairIndex (rightFin p.2) := by
      simpa using hpNe
    exact patternPartition_rel_false_of_pairIndex_ne s hPairIdx this
  · have hRel : (realizedPartition ρ (2 * n)).r (rightFin p.1) (rightFin p.2) := by
      change ρ ((rightFin p.1).1) = ρ ((rightFin p.2).1)
      simpa using hEq
    have : (patternPartition n s).r (rightFin p.1) (rightFin p.2) := by simpa [hPart] using hRel
    have hPairIdx : pairIndex (rightFin p.1) ≠ pairIndex (rightFin p.2) := by
      simpa using hpNe
    exact patternPartition_rel_false_of_pairIndex_ne s hPairIdx this

theorem crossWiring_false_of_realizedPartition_eq_pattern
    {α : Type u} [Infinite α] (ρ : Valuation α) {n : Nat} (s : Finset (Fin n))
    (hPart : realizedPartition ρ (2 * n) = patternPartition n s) :
    ¬ HoldsInfAll ρ (crossWiring n) := by
  intro hCross
  exact crossWiring_false_of_realizedPartition_eq_pattern_holds
    (admits := allAccessibility) (ρ := ρ) (s := s) hPart
    ((holdsInfAll_pure_iff_holds (ρ := ρ) (φ := crossWiring n)
      (isPure_crossWiring n)).mp hCross)

theorem guardedButton_holds_of_realizedPartition_eq_pattern
    {α : Type u} [Infinite α] (ρ : Valuation α) {n : Nat} (s : Finset (Fin n))
    (i : Fin n)
    (hPart : realizedPartition ρ (2 * n) = patternPartition n s) :
    HoldsInfAll ρ (guardedButton i) ↔ i ∈ s := by
  have hPair :
      HoldsInfAll ρ (pairEq i.1) ↔ i ∈ s := by
    rw [holdsInfAll_pure_iff_holds (ρ := ρ) (φ := pairEq i.1) (by trivial)]
    have hRel :
        (realizedPartition ρ (2 * n)).r (leftFin i) (rightFin i) ↔ i ∈ s := by
      rw [hPart]
      exact patternPartition_pair_eq_iff s i
    have hEqRel :
        (ρ (leftVar i.1) = ρ (rightVar i.1)) ↔
          (realizedPartition ρ (2 * n)).r (leftFin i) (rightFin i) := by
      rfl
    exact hEqRel.trans hRel
  have hCrossFalse := crossWiring_false_of_realizedPartition_eq_pattern
    (ρ := ρ) (n := n) (s := s) hPart
  show (HoldsInfAll ρ (pairEq i.1) ∨ HoldsInfAll ρ (crossWiring n)) ↔ i ∈ s
  simpa [guardedButton] using
    Iff.intro
      (fun h =>
        match h with
        | Or.inl hPairTrue => hPair.mp hPairTrue
        | Or.inr hCross => False.elim (hCrossFalse hCross))
      (fun hi => Or.inl (hPair.mpr hi))

theorem guardedButton_holds_of_realizedPartition_eq_pattern_surj
    {α : Type u} [Infinite α] (ρ : Valuation α) {n : Nat} (s : Finset (Fin n))
    (i : Fin n)
    (hPart : realizedPartition ρ (2 * n) = patternPartition n s) :
    HoldsInfSurj ρ (guardedButton i) ↔ i ∈ s := by
  have hPair :
      HoldsInfSurj ρ (pairEq i.1) ↔ i ∈ s := by
    rw [holdsInfSurj_pure_iff_holds (ρ := ρ) (φ := pairEq i.1) (by trivial)]
    have hRel :
        (realizedPartition ρ (2 * n)).r (leftFin i) (rightFin i) ↔ i ∈ s := by
      rw [hPart]
      exact patternPartition_pair_eq_iff s i
    have hEqRel :
        (ρ (leftVar i.1) = ρ (rightVar i.1)) ↔
          (realizedPartition ρ (2 * n)).r (leftFin i) (rightFin i) := by
      rfl
    exact hEqRel.trans hRel
  have hCrossFalse :
      ¬ HoldsInfSurj ρ (crossWiring n) := by
    intro hCross
    exact crossWiring_false_of_realizedPartition_eq_pattern_holds
      (admits := surjectiveAccessibility) (ρ := ρ) (s := s) hPart
      ((holdsInfSurj_pure_iff_holds (ρ := ρ) (φ := crossWiring n)
        (isPure_crossWiring n)).mp hCross)
  show (HoldsInfSurj ρ (pairEq i.1) ∨ HoldsInfSurj ρ (crossWiring n)) ↔ i ∈ s
  simpa [guardedButton] using
    Iff.intro
      (fun h =>
        match h with
        | Or.inl hPairTrue => hPair.mp hPairTrue
        | Or.inr hCross => False.elim (hCrossFalse hCross))
      (fun hi => Or.inl (hPair.mpr hi))

theorem holdsInfAll_crossWiring_map {α β : Type u} [Infinite α] [Infinite β]
    (ρ : Valuation α) (f : α → β) {n : Nat} :
    HoldsInfAll ρ (crossWiring n) →
      HoldsInfAll (fun i => f (ρ i)) (crossWiring n) := by
  intro h
  have h' :
      Holds allAccessibility ρ (crossWiring n) :=
    (holdsInfAll_pure_iff_holds (ρ := ρ) (φ := crossWiring n)
      (isPure_crossWiring n)).mp h
  have hCross : CrossWiredAt ρ n :=
    (holds_crossWiring_iff (ρ := ρ) n).mp h'
  have hCrossMap : CrossWiredAt (fun i => f (ρ i)) n := by
    rcases hCross with ⟨p, hpNe, hEq | hEq | hEq⟩
    · exact Exists.intro p (And.intro hpNe (Or.inl (congrArg f hEq)))
    · exact Exists.intro p (And.intro hpNe (Or.inr (Or.inl (congrArg f hEq))))
    · exact Exists.intro p (And.intro hpNe (Or.inr (Or.inr (congrArg f hEq))))
  have hMap :
      Holds allAccessibility (fun i => f (ρ i)) (crossWiring n) :=
    (holds_crossWiring_iff (ρ := fun i => f (ρ i)) n).mpr hCrossMap
  exact (holdsInfAll_pure_iff_holds (ρ := fun i => f (ρ i)) (φ := crossWiring n)
    (isPure_crossWiring n)).mpr hMap

theorem holdsInfSurj_crossWiring_map {α β : Type u} [Infinite α] [Infinite β]
    (ρ : Valuation α) (f : α → β) {n : Nat} :
    HoldsInfSurj ρ (crossWiring n) →
      HoldsInfSurj (fun i => f (ρ i)) (crossWiring n) := by
  intro h
  have h' :
      Holds surjectiveAccessibility ρ (crossWiring n) :=
    (holdsInfSurj_pure_iff_holds (ρ := ρ) (φ := crossWiring n)
      (isPure_crossWiring n)).mp h
  have hCross : CrossWiredAt ρ n :=
    (holds_crossWiring_iff (admits := surjectiveAccessibility) (ρ := ρ) n).mp h'
  have hCrossMap : CrossWiredAt (fun i => f (ρ i)) n := by
    rcases hCross with ⟨p, hpNe, hEq | hEq | hEq⟩
    · exact Exists.intro p (And.intro hpNe (Or.inl (congrArg f hEq)))
    · exact Exists.intro p (And.intro hpNe (Or.inr (Or.inl (congrArg f hEq))))
    · exact Exists.intro p (And.intro hpNe (Or.inr (Or.inr (congrArg f hEq))))
  have hMap :
      Holds surjectiveAccessibility (fun i => f (ρ i)) (crossWiring n) :=
    (holds_crossWiring_iff (admits := surjectiveAccessibility)
      (ρ := fun i => f (ρ i)) n).mpr hCrossMap
  exact (holdsInfSurj_pure_iff_holds (ρ := fun i => f (ρ i)) (φ := crossWiring n)
    (isPure_crossWiring n)).mpr hMap

theorem holdsInfAll_pairEq_map {α β : Type u} [Infinite α] [Infinite β]
    (ρ : Valuation α) (f : α → β) (i : Nat) :
    HoldsInfAll ρ (pairEq i) → HoldsInfAll (fun k => f (ρ k)) (pairEq i) := by
  intro h
  rw [holdsInfAll_pure_iff_holds (ρ := ρ) (φ := pairEq i) (by trivial)] at h
  rw [holdsInfAll_pure_iff_holds (ρ := fun k => f (ρ k)) (φ := pairEq i) (by trivial)]
  exact congrArg f h

theorem holdsInfSurj_pairEq_map {α β : Type u} [Infinite α] [Infinite β]
    (ρ : Valuation α) (f : α → β) (i : Nat) :
    HoldsInfSurj ρ (pairEq i) → HoldsInfSurj (fun k => f (ρ k)) (pairEq i) := by
  intro h
  rw [holdsInfSurj_pure_iff_holds (ρ := ρ) (φ := pairEq i) (by trivial)] at h
  rw [holdsInfSurj_pure_iff_holds (ρ := fun k => f (ρ k)) (φ := pairEq i) (by trivial)]
  exact congrArg f h

theorem holdsInfAll_guardedButton_persistent {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat} (i : Fin n) :
    HoldsInfAll ρ (guardedButton i) →
      HoldsInfAll ρ (.boxQ (guardedButton i)) := by
  intro h β hβ f hf
  rcases h with hPair | hCross
  · exact Or.inl (holdsInfAll_pairEq_map ρ f i.1 hPair)
  · exact Or.inr (holdsInfAll_crossWiring_map ρ f hCross)

theorem holdsInfSurj_guardedButton_persistent {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat} (i : Fin n) :
    HoldsInfSurj ρ (guardedButton i) →
      HoldsInfSurj ρ (.boxQ (guardedButton i)) := by
  intro h β hβ f hf
  rcases h with hPair | hCross
  · exact Or.inl (holdsInfSurj_pairEq_map ρ f i.1 hPair)
  · exact Or.inr (holdsInfSurj_crossWiring_map ρ f hCross)

def GuardedButtonPatternAll {β : Type u} [Infinite β] {n : Nat}
    (σ : Valuation β) (s : Finset (Fin n)) : Prop :=
  ∀ i, HoldsInfAll σ (guardedButton i) ↔ i ∈ s

def GuardedButtonPatternSurj {β : Type u} [Infinite β] {n : Nat}
    (σ : Valuation β) (s : Finset (Fin n)) : Prop :=
  ∀ i, HoldsInfSurj σ (guardedButton i) ↔ i ∈ s

structure AllGuardedButtonPatternWitness {α : Type u} [Infinite α] (ρ : Valuation α)
    {n : Nat} (s : Finset (Fin n)) where
  β : Type u
  hβ : Infinite β
  f : α → β
  pattern : @GuardedButtonPatternAll β hβ _ (fun k => f (ρ k)) s

structure SurjGuardedButtonPatternWitness {α : Type u} [Infinite α] (ρ : Valuation α)
    {n : Nat} (s : Finset (Fin n)) where
  β : Type u
  hβ : Infinite β
  f : α → β
  hsurj : Function.Surjective f
  pattern : @GuardedButtonPatternSurj β hβ _ (fun k => f (ρ k)) s

theorem eq_leftFin_or_rightFin {n : Nat} (v : Fin (2 * n)) :
    v = leftFin (pairIndex v) ∨ v = rightFin (pairIndex v) := by
  rcases Nat.mod_two_eq_zero_or_one v.1 with hmod | hmod
  · left
    apply Fin.ext
    change v.1 = 2 * (v.1 / 2)
    omega
  · right
    apply Fin.ext
    change v.1 = 2 * (v.1 / 2) + 1
    omega

theorem crossWiring_false_of_guardedPattern_not_top_all
    {α : Type u} [Infinite α] (ρ : Valuation α) {n : Nat} (s : Finset (Fin n))
    (hPattern : GuardedButtonPatternAll ρ s) (hNotTop : s ≠ Finset.univ) :
    ¬ HoldsInfAll ρ (crossWiring n) := by
  classical
  have hMissing : Exists (fun i : Fin n => i ∉ s) := by
    by_contra hNoMissing
    apply hNotTop
    apply Finset.eq_univ_iff_forall.mpr
    intro i
    by_contra hi
    exact hNoMissing (Exists.intro i hi)
  rcases hMissing with ⟨i, hi⟩
  intro hCross
  have hGuard : HoldsInfAll ρ (guardedButton i) := by
    simpa [guardedButton] using
      (Or.inr hCross : HoldsInfAll ρ (pairEq i.1) ∨ HoldsInfAll ρ (crossWiring n))
  exact hi ((hPattern i).mp hGuard)

theorem crossWiring_false_of_guardedPattern_not_top_surj
    {α : Type u} [Infinite α] (ρ : Valuation α) {n : Nat} (s : Finset (Fin n))
    (hPattern : GuardedButtonPatternSurj ρ s) (hNotTop : s ≠ Finset.univ) :
    ¬ HoldsInfSurj ρ (crossWiring n) := by
  classical
  have hMissing : Exists (fun i : Fin n => i ∉ s) := by
    by_contra hNoMissing
    apply hNotTop
    apply Finset.eq_univ_iff_forall.mpr
    intro i
    by_contra hi
    exact hNoMissing (Exists.intro i hi)
  rcases hMissing with ⟨i, hi⟩
  intro hCross
  have hGuard : HoldsInfSurj ρ (guardedButton i) := by
    simpa [guardedButton] using
      (Or.inr hCross : HoldsInfSurj ρ (pairEq i.1) ∨ HoldsInfSurj ρ (crossWiring n))
  exact hi ((hPattern i).mp hGuard)

theorem pairEq_holds_iff_of_guardedPattern_not_top_all
    {α : Type u} [Infinite α] (ρ : Valuation α) {n : Nat} (s : Finset (Fin n))
    (hPattern : GuardedButtonPatternAll ρ s) (hNotTop : s ≠ Finset.univ)
    (i : Fin n) :
    HoldsInfAll ρ (pairEq i.1) ↔ i ∈ s := by
  have hCrossFalse := crossWiring_false_of_guardedPattern_not_top_all
    (ρ := ρ) (s := s) hPattern hNotTop
  constructor
  · intro hPair
    have hGuard : HoldsInfAll ρ (guardedButton i) := by
      simpa [guardedButton] using
        (Or.inl hPair : HoldsInfAll ρ (pairEq i.1) ∨ HoldsInfAll ρ (crossWiring n))
    exact (hPattern i).mp hGuard
  · intro hi
    have hGuard : HoldsInfAll ρ (guardedButton i) := (hPattern i).mpr hi
    rcases (show HoldsInfAll ρ (pairEq i.1) ∨ HoldsInfAll ρ (crossWiring n) from by
      simpa [guardedButton] using hGuard) with hPair | hCross
    · exact hPair
    · exact False.elim (hCrossFalse hCross)

theorem pairEq_holds_iff_of_guardedPattern_not_top_surj
    {α : Type u} [Infinite α] (ρ : Valuation α) {n : Nat} (s : Finset (Fin n))
    (hPattern : GuardedButtonPatternSurj ρ s) (hNotTop : s ≠ Finset.univ)
    (i : Fin n) :
    HoldsInfSurj ρ (pairEq i.1) ↔ i ∈ s := by
  have hCrossFalse := crossWiring_false_of_guardedPattern_not_top_surj
    (ρ := ρ) (s := s) hPattern hNotTop
  constructor
  · intro hPair
    have hGuard : HoldsInfSurj ρ (guardedButton i) := by
      simpa [guardedButton] using
        (Or.inl hPair : HoldsInfSurj ρ (pairEq i.1) ∨ HoldsInfSurj ρ (crossWiring n))
    exact (hPattern i).mp hGuard
  · intro hi
    have hGuard : HoldsInfSurj ρ (guardedButton i) := (hPattern i).mpr hi
    rcases (show HoldsInfSurj ρ (pairEq i.1) ∨ HoldsInfSurj ρ (crossWiring n) from by
      simpa [guardedButton] using hGuard) with hPair | hCross
    · exact hPair
    · exact False.elim (hCrossFalse hCross)

theorem holdsInfAll_crossWiring_of_left_left_eq
    {α : Type u} [Infinite α] (ρ : Valuation α) {n : Nat}
    {i j : Fin n} (hij : i ≠ j)
    (hEq : ρ (leftVar i.1) = ρ (leftVar j.1)) :
    HoldsInfAll ρ (crossWiring n) := by
  have hCross : CrossWiredAt ρ n := by
    refine Exists.intro (Prod.mk i j) ?_
    exact And.intro hij (Or.inl hEq)
  exact (holdsInfAll_pure_iff_holds (ρ := ρ) (φ := crossWiring n) (isPure_crossWiring n)).mpr
    ((holds_crossWiring_iff (ρ := ρ) n).mpr hCross)

theorem holdsInfAll_crossWiring_of_left_right_eq
    {α : Type u} [Infinite α] (ρ : Valuation α) {n : Nat}
    {i j : Fin n} (hij : i ≠ j)
    (hEq : ρ (leftVar i.1) = ρ (rightVar j.1)) :
    HoldsInfAll ρ (crossWiring n) := by
  have hCross : CrossWiredAt ρ n := by
    refine Exists.intro (Prod.mk i j) ?_
    exact And.intro hij (Or.inr (Or.inl hEq))
  exact (holdsInfAll_pure_iff_holds (ρ := ρ) (φ := crossWiring n) (isPure_crossWiring n)).mpr
    ((holds_crossWiring_iff (ρ := ρ) n).mpr hCross)

theorem holdsInfAll_crossWiring_of_right_right_eq
    {α : Type u} [Infinite α] (ρ : Valuation α) {n : Nat}
    {i j : Fin n} (hij : i ≠ j)
    (hEq : ρ (rightVar i.1) = ρ (rightVar j.1)) :
    HoldsInfAll ρ (crossWiring n) := by
  have hCross : CrossWiredAt ρ n := by
    refine Exists.intro (Prod.mk i j) ?_
    exact And.intro hij (Or.inr (Or.inr hEq))
  exact (holdsInfAll_pure_iff_holds (ρ := ρ) (φ := crossWiring n) (isPure_crossWiring n)).mpr
    ((holds_crossWiring_iff (ρ := ρ) n).mpr hCross)

theorem holdsInfSurj_crossWiring_of_left_left_eq
    {α : Type u} [Infinite α] (ρ : Valuation α) {n : Nat}
    {i j : Fin n} (hij : i ≠ j)
    (hEq : ρ (leftVar i.1) = ρ (leftVar j.1)) :
    HoldsInfSurj ρ (crossWiring n) := by
  have hCross : CrossWiredAt ρ n := by
    refine Exists.intro (Prod.mk i j) ?_
    exact And.intro hij (Or.inl hEq)
  exact (holdsInfSurj_pure_iff_holds (ρ := ρ) (φ := crossWiring n) (isPure_crossWiring n)).mpr
    ((holds_crossWiring_iff (admits := surjectiveAccessibility) (ρ := ρ) n).mpr hCross)

theorem holdsInfSurj_crossWiring_of_left_right_eq
    {α : Type u} [Infinite α] (ρ : Valuation α) {n : Nat}
    {i j : Fin n} (hij : i ≠ j)
    (hEq : ρ (leftVar i.1) = ρ (rightVar j.1)) :
    HoldsInfSurj ρ (crossWiring n) := by
  have hCross : CrossWiredAt ρ n := by
    refine Exists.intro (Prod.mk i j) ?_
    exact And.intro hij (Or.inr (Or.inl hEq))
  exact (holdsInfSurj_pure_iff_holds (ρ := ρ) (φ := crossWiring n) (isPure_crossWiring n)).mpr
    ((holds_crossWiring_iff (admits := surjectiveAccessibility) (ρ := ρ) n).mpr hCross)

theorem holdsInfSurj_crossWiring_of_right_right_eq
    {α : Type u} [Infinite α] (ρ : Valuation α) {n : Nat}
    {i j : Fin n} (hij : i ≠ j)
    (hEq : ρ (rightVar i.1) = ρ (rightVar j.1)) :
    HoldsInfSurj ρ (crossWiring n) := by
  have hCross : CrossWiredAt ρ n := by
    refine Exists.intro (Prod.mk i j) ?_
    exact And.intro hij (Or.inr (Or.inr hEq))
  exact (holdsInfSurj_pure_iff_holds (ρ := ρ) (φ := crossWiring n) (isPure_crossWiring n)).mpr
    ((holds_crossWiring_iff (admits := surjectiveAccessibility) (ρ := ρ) n).mpr hCross)

theorem realizedPartition_rel_false_of_pairIndex_ne_of_not_crossWiring_all
    {α : Type u} [Infinite α] (ρ : Valuation α) {n : Nat}
    (hCrossFalse : ¬ HoldsInfAll ρ (crossWiring n))
    {a b : Fin (2 * n)} (hab : pairIndex a ≠ pairIndex b) :
    ¬ (realizedPartition ρ (2 * n)).r a b := by
  change ρ a.1 = ρ b.1 → False
  let i : Fin n := pairIndex a
  let j : Fin n := pairIndex b
  have hij : i ≠ j := by
    show pairIndex a ≠ pairIndex b
    exact hab
  rcases eq_leftFin_or_rightFin a with ha | ha
  · rcases eq_leftFin_or_rightFin b with hb | hb
    · intro hEq
      have haVal : a.1 = leftVar (pairIndex a).1 := congrArg Fin.val ha
      have hbVal : b.1 = leftVar (pairIndex b).1 := congrArg Fin.val hb
      have hEq' : ρ (leftVar i.1) = ρ (leftVar j.1) := by
        calc
          ρ (leftVar i.1) = ρ a.1 := by
            dsimp [i]
            rw [haVal]
          _ = ρ b.1 := hEq
          _ = ρ (leftVar j.1) := by
            dsimp [j]
            rw [hbVal]
      exact hCrossFalse (holdsInfAll_crossWiring_of_left_left_eq
        (ρ := ρ) (i := i) (j := j) hij hEq')
    · intro hEq
      have haVal : a.1 = leftVar (pairIndex a).1 := congrArg Fin.val ha
      have hbVal : b.1 = rightVar (pairIndex b).1 := congrArg Fin.val hb
      have hEq' : ρ (leftVar i.1) = ρ (rightVar j.1) := by
        calc
          ρ (leftVar i.1) = ρ a.1 := by
            dsimp [i]
            rw [haVal]
          _ = ρ b.1 := hEq
          _ = ρ (rightVar j.1) := by
            dsimp [j]
            rw [hbVal]
      exact hCrossFalse (holdsInfAll_crossWiring_of_left_right_eq
        (ρ := ρ) (i := i) (j := j) hij hEq')
  · rcases eq_leftFin_or_rightFin b with hb | hb
    · intro hEq
      have haVal : a.1 = rightVar (pairIndex a).1 := congrArg Fin.val ha
      have hbVal : b.1 = leftVar (pairIndex b).1 := congrArg Fin.val hb
      have hEq' : ρ (leftVar j.1) = ρ (rightVar i.1) := by
        calc
          ρ (leftVar j.1) = ρ b.1 := by
            dsimp [j]
            rw [hbVal]
          _ = ρ a.1 := hEq.symm
          _ = ρ (rightVar i.1) := by
            dsimp [i]
            rw [haVal]
      exact hCrossFalse (holdsInfAll_crossWiring_of_left_right_eq
        (ρ := ρ) (i := j) (j := i) hij.symm hEq')
    · intro hEq
      have haVal : a.1 = rightVar (pairIndex a).1 := congrArg Fin.val ha
      have hbVal : b.1 = rightVar (pairIndex b).1 := congrArg Fin.val hb
      have hEq' : ρ (rightVar i.1) = ρ (rightVar j.1) := by
        calc
          ρ (rightVar i.1) = ρ a.1 := by
            dsimp [i]
            rw [haVal]
          _ = ρ b.1 := hEq
          _ = ρ (rightVar j.1) := by
            dsimp [j]
            rw [hbVal]
      exact hCrossFalse (holdsInfAll_crossWiring_of_right_right_eq
        (ρ := ρ) (i := i) (j := j) hij hEq')

theorem realizedPartition_rel_false_of_pairIndex_ne_of_not_crossWiring_surj
    {α : Type u} [Infinite α] (ρ : Valuation α) {n : Nat}
    (hCrossFalse : ¬ HoldsInfSurj ρ (crossWiring n))
    {a b : Fin (2 * n)} (hab : pairIndex a ≠ pairIndex b) :
    ¬ (realizedPartition ρ (2 * n)).r a b := by
  change ρ a.1 = ρ b.1 → False
  let i : Fin n := pairIndex a
  let j : Fin n := pairIndex b
  have hij : i ≠ j := by
    show pairIndex a ≠ pairIndex b
    exact hab
  rcases eq_leftFin_or_rightFin a with ha | ha
  · rcases eq_leftFin_or_rightFin b with hb | hb
    · intro hEq
      have haVal : a.1 = leftVar (pairIndex a).1 := congrArg Fin.val ha
      have hbVal : b.1 = leftVar (pairIndex b).1 := congrArg Fin.val hb
      have hEq' : ρ (leftVar i.1) = ρ (leftVar j.1) := by
        calc
          ρ (leftVar i.1) = ρ a.1 := by
            dsimp [i]
            rw [haVal]
          _ = ρ b.1 := hEq
          _ = ρ (leftVar j.1) := by
            dsimp [j]
            rw [hbVal]
      exact hCrossFalse (holdsInfSurj_crossWiring_of_left_left_eq
        (ρ := ρ) (i := i) (j := j) hij hEq')
    · intro hEq
      have haVal : a.1 = leftVar (pairIndex a).1 := congrArg Fin.val ha
      have hbVal : b.1 = rightVar (pairIndex b).1 := congrArg Fin.val hb
      have hEq' : ρ (leftVar i.1) = ρ (rightVar j.1) := by
        calc
          ρ (leftVar i.1) = ρ a.1 := by
            dsimp [i]
            rw [haVal]
          _ = ρ b.1 := hEq
          _ = ρ (rightVar j.1) := by
            dsimp [j]
            rw [hbVal]
      exact hCrossFalse (holdsInfSurj_crossWiring_of_left_right_eq
        (ρ := ρ) (i := i) (j := j) hij hEq')
  · rcases eq_leftFin_or_rightFin b with hb | hb
    · intro hEq
      have haVal : a.1 = rightVar (pairIndex a).1 := congrArg Fin.val ha
      have hbVal : b.1 = leftVar (pairIndex b).1 := congrArg Fin.val hb
      have hEq' : ρ (leftVar j.1) = ρ (rightVar i.1) := by
        calc
          ρ (leftVar j.1) = ρ b.1 := by
            dsimp [j]
            rw [hbVal]
          _ = ρ a.1 := hEq.symm
          _ = ρ (rightVar i.1) := by
            dsimp [i]
            rw [haVal]
      exact hCrossFalse (holdsInfSurj_crossWiring_of_left_right_eq
        (ρ := ρ) (i := j) (j := i) hij.symm hEq')
    · intro hEq
      have haVal : a.1 = rightVar (pairIndex a).1 := congrArg Fin.val ha
      have hbVal : b.1 = rightVar (pairIndex b).1 := congrArg Fin.val hb
      have hEq' : ρ (rightVar i.1) = ρ (rightVar j.1) := by
        calc
          ρ (rightVar i.1) = ρ a.1 := by
            dsimp [i]
            rw [haVal]
          _ = ρ b.1 := hEq
          _ = ρ (rightVar j.1) := by
            dsimp [j]
            rw [hbVal]
      exact hCrossFalse (holdsInfSurj_crossWiring_of_right_right_eq
        (ρ := ρ) (i := i) (j := j) hij hEq')

theorem realizedPartition_pair_eq_iff_of_guardedPattern_not_top_all
    {α : Type u} [Infinite α] (ρ : Valuation α) {n : Nat} (s : Finset (Fin n))
    (hPattern : GuardedButtonPatternAll ρ s) (hNotTop : s ≠ Finset.univ)
    (i : Fin n) :
    (realizedPartition ρ (2 * n)).r (leftFin i) (rightFin i) ↔ i ∈ s := by
  have hPair : HoldsInfAll ρ (pairEq i.1) ↔ i ∈ s :=
    pairEq_holds_iff_of_guardedPattern_not_top_all (ρ := ρ) (s := s) hPattern hNotTop i
  rw [holdsInfAll_pure_iff_holds (ρ := ρ) (φ := pairEq i.1) (by trivial)] at hPair
  simpa [pairEq]

theorem realizedPartition_pair_eq_symm_iff_of_guardedPattern_not_top_all
    {α : Type u} [Infinite α] (ρ : Valuation α) {n : Nat} (s : Finset (Fin n))
    (hPattern : GuardedButtonPatternAll ρ s) (hNotTop : s ≠ Finset.univ)
    (i : Fin n) :
    (realizedPartition ρ (2 * n)).r (rightFin i) (leftFin i) ↔ i ∈ s := by
  constructor
  · intro h
    exact (realizedPartition_pair_eq_iff_of_guardedPattern_not_top_all
      (ρ := ρ) (s := s) hPattern hNotTop i).mp
      ((realizedPartition ρ (2 * n)).symm h)
  · intro hi
    exact (realizedPartition ρ (2 * n)).symm <|
      (realizedPartition_pair_eq_iff_of_guardedPattern_not_top_all
        (ρ := ρ) (s := s) hPattern hNotTop i).mpr hi

theorem patternPartition_pair_eq_symm_iff {n : Nat} (s : Finset (Fin n)) (i : Fin n) :
    (patternPartition n s).r (rightFin i) (leftFin i) ↔ i ∈ s := by
  constructor
  · intro h
    exact (patternPartition_pair_eq_iff s i).mp ((patternPartition n s).symm h)
  · intro hi
    exact (patternPartition n s).symm ((patternPartition_pair_eq_iff s i).mpr hi)

theorem realizedPartition_rel_left_left_of_eq
    {α : Type u} (ρ : Valuation α) {n : Nat} {a b : Fin (2 * n)} {i : Fin n}
    (ha : a = leftFin i) (hb : b = leftFin i) :
    (realizedPartition ρ (2 * n)).r a b := by
  change ρ a.1 = ρ b.1
  have haVal : a.1 = leftVar i.1 := congrArg Fin.val ha
  have hbVal : b.1 = leftVar i.1 := congrArg Fin.val hb
  calc
    ρ a.1 = ρ (leftVar i.1) := by rw [haVal]
    _ = ρ (leftVar i.1) := rfl
    _ = ρ b.1 := by rw [hbVal]

theorem realizedPartition_rel_right_right_of_eq
    {α : Type u} (ρ : Valuation α) {n : Nat} {a b : Fin (2 * n)} {i : Fin n}
    (ha : a = rightFin i) (hb : b = rightFin i) :
    (realizedPartition ρ (2 * n)).r a b := by
  change ρ a.1 = ρ b.1
  have haVal : a.1 = rightVar i.1 := congrArg Fin.val ha
  have hbVal : b.1 = rightVar i.1 := congrArg Fin.val hb
  calc
    ρ a.1 = ρ (rightVar i.1) := by rw [haVal]
    _ = ρ (rightVar i.1) := rfl
    _ = ρ b.1 := by rw [hbVal]

theorem patternPartition_rel_left_left_of_eq {n : Nat} (s : Finset (Fin n))
    {a b : Fin (2 * n)} {i : Fin n}
    (ha : a = leftFin i) (hb : b = leftFin i) :
    (patternPartition n s).r a b := by
  unfold patternPartition
  change patternCode n s a = patternCode n s b
  calc
    patternCode n s a = patternCode n s (leftFin i) := congrArg (patternCode n s) ha
    _ = patternCode n s (leftFin i) := rfl
    _ = patternCode n s b := by
      symm
      exact congrArg (patternCode n s) hb

theorem patternPartition_rel_right_right_of_eq {n : Nat} (s : Finset (Fin n))
    {a b : Fin (2 * n)} {i : Fin n}
    (ha : a = rightFin i) (hb : b = rightFin i) :
    (patternPartition n s).r a b := by
  unfold patternPartition
  change patternCode n s a = patternCode n s b
  calc
    patternCode n s a = patternCode n s (rightFin i) := congrArg (patternCode n s) ha
    _ = patternCode n s (rightFin i) := rfl
    _ = patternCode n s b := by
      symm
      exact congrArg (patternCode n s) hb

theorem patternPartition_rel_left_right_iff_of_eq {n : Nat} (s : Finset (Fin n))
    {a b : Fin (2 * n)} {i : Fin n}
    (ha : a = leftFin i) (hb : b = rightFin i) :
    (patternPartition n s).r a b ↔ i ∈ s := by
  unfold patternPartition
  change patternCode n s a = patternCode n s b ↔ i ∈ s
  have haCode : patternCode n s a = patternCode n s (leftFin i) :=
    congrArg (patternCode n s) ha
  have hbCode : patternCode n s b = patternCode n s (rightFin i) :=
    congrArg (patternCode n s) hb
  constructor
  · intro h
    have hPair : patternCode n s (leftFin i) = patternCode n s (rightFin i) := by
      calc
        patternCode n s (leftFin i) = patternCode n s a := haCode.symm
        _ = patternCode n s b := h
        _ = patternCode n s (rightFin i) := hbCode
    exact (patternPartition_pair_eq_iff s i).mp hPair
  · intro hi
    have hPair : patternCode n s (leftFin i) = patternCode n s (rightFin i) :=
      (patternPartition_pair_eq_iff s i).mpr hi
    calc
      patternCode n s a = patternCode n s (leftFin i) := haCode
      _ = patternCode n s (rightFin i) := hPair
      _ = patternCode n s b := hbCode.symm

theorem patternPartition_rel_right_left_iff_of_eq {n : Nat} (s : Finset (Fin n))
    {a b : Fin (2 * n)} {i : Fin n}
    (ha : a = rightFin i) (hb : b = leftFin i) :
    (patternPartition n s).r a b ↔ i ∈ s := by
  unfold patternPartition
  change patternCode n s a = patternCode n s b ↔ i ∈ s
  have haCode : patternCode n s a = patternCode n s (rightFin i) :=
    congrArg (patternCode n s) ha
  have hbCode : patternCode n s b = patternCode n s (leftFin i) :=
    congrArg (patternCode n s) hb
  constructor
  · intro h
    have hPair : patternCode n s (rightFin i) = patternCode n s (leftFin i) := by
      calc
        patternCode n s (rightFin i) = patternCode n s a := haCode.symm
        _ = patternCode n s b := h
        _ = patternCode n s (leftFin i) := hbCode
    exact (patternPartition_pair_eq_symm_iff s i).mp hPair
  · intro hi
    have hPair : patternCode n s (rightFin i) = patternCode n s (leftFin i) :=
      (patternPartition_pair_eq_symm_iff s i).mpr hi
    calc
      patternCode n s a = patternCode n s (rightFin i) := haCode
      _ = patternCode n s (leftFin i) := hPair
      _ = patternCode n s b := hbCode.symm

theorem realizedPartition_rel_left_right_iff_of_guardedPattern_not_top_all
    {α : Type u} [Infinite α] (ρ : Valuation α) {n : Nat} (s : Finset (Fin n))
    (hPattern : GuardedButtonPatternAll ρ s) (hNotTop : s ≠ Finset.univ)
    {a b : Fin (2 * n)} {i : Fin n}
    (ha : a = leftFin i) (hb : b = rightFin i) :
    (realizedPartition ρ (2 * n)).r a b ↔ i ∈ s := by
  change ρ a.1 = ρ b.1 ↔ i ∈ s
  have haVal : a.1 = leftVar i.1 := congrArg Fin.val ha
  have hbVal : b.1 = rightVar i.1 := congrArg Fin.val hb
  constructor
  · intro h
    have hPair : ρ (leftVar i.1) = ρ (rightVar i.1) := by
      calc
        ρ (leftVar i.1) = ρ a.1 := by rw [haVal]
        _ = ρ b.1 := h
        _ = ρ (rightVar i.1) := by rw [hbVal]
    exact (realizedPartition_pair_eq_iff_of_guardedPattern_not_top_all
      (ρ := ρ) (s := s) hPattern hNotTop i).mp hPair
  · intro hi
    have hPair : ρ (leftVar i.1) = ρ (rightVar i.1) :=
      (realizedPartition_pair_eq_iff_of_guardedPattern_not_top_all
        (ρ := ρ) (s := s) hPattern hNotTop i).mpr hi
    calc
      ρ a.1 = ρ (leftVar i.1) := by rw [haVal]
      _ = ρ (rightVar i.1) := hPair
      _ = ρ b.1 := by rw [hbVal]

theorem realizedPartition_rel_right_left_iff_of_guardedPattern_not_top_all
    {α : Type u} [Infinite α] (ρ : Valuation α) {n : Nat} (s : Finset (Fin n))
    (hPattern : GuardedButtonPatternAll ρ s) (hNotTop : s ≠ Finset.univ)
    {a b : Fin (2 * n)} {i : Fin n}
    (ha : a = rightFin i) (hb : b = leftFin i) :
    (realizedPartition ρ (2 * n)).r a b ↔ i ∈ s := by
  change ρ a.1 = ρ b.1 ↔ i ∈ s
  have haVal : a.1 = rightVar i.1 := congrArg Fin.val ha
  have hbVal : b.1 = leftVar i.1 := congrArg Fin.val hb
  constructor
  · intro h
    have hPair : ρ (rightVar i.1) = ρ (leftVar i.1) := by
      calc
        ρ (rightVar i.1) = ρ a.1 := by rw [haVal]
        _ = ρ b.1 := h
        _ = ρ (leftVar i.1) := by rw [hbVal]
    exact (realizedPartition_pair_eq_symm_iff_of_guardedPattern_not_top_all
      (ρ := ρ) (s := s) hPattern hNotTop i).mp hPair
  · intro hi
    have hPair : ρ (rightVar i.1) = ρ (leftVar i.1) :=
      (realizedPartition_pair_eq_symm_iff_of_guardedPattern_not_top_all
        (ρ := ρ) (s := s) hPattern hNotTop i).mpr hi
    calc
      ρ a.1 = ρ (rightVar i.1) := by rw [haVal]
      _ = ρ (leftVar i.1) := hPair
      _ = ρ b.1 := by rw [hbVal]

theorem realizedPartition_eq_pattern_of_guardedPattern_not_top_all
    {α : Type u} [Infinite α] (ρ : Valuation α) {n : Nat} (s : Finset (Fin n))
    (hPattern : GuardedButtonPatternAll ρ s) (hNotTop : s ≠ Finset.univ) :
    realizedPartition ρ (2 * n) = patternPartition n s := by
  have hCrossFalse := crossWiring_false_of_guardedPattern_not_top_all
    (ρ := ρ) (s := s) hPattern hNotTop
  ext a b
  by_cases hIdx : pairIndex a = pairIndex b
  · let i : Fin n := pairIndex a
    have haNorm : a = leftFin i ∨ a = rightFin i := by
      rcases eq_leftFin_or_rightFin a with ha | ha
      · left
        simpa [i] using ha
      · right
        simpa [i] using ha
    have hbNorm : b = leftFin i ∨ b = rightFin i := by
      rcases eq_leftFin_or_rightFin b with hb | hb
      · left
        have hb' : b = leftFin (pairIndex a) := by
          simpa [hIdx] using hb
        simpa [i] using hb'
      · right
        have hb' : b = rightFin (pairIndex a) := by
          simpa [hIdx] using hb
        simpa [i] using hb'
    rcases haNorm with ha | ha <;> rcases hbNorm with hb | hb
    · constructor
      · intro _
        exact patternPartition_rel_left_left_of_eq s ha hb
      · intro _
        exact realizedPartition_rel_left_left_of_eq ρ ha hb
    · exact (realizedPartition_rel_left_right_iff_of_guardedPattern_not_top_all
        (ρ := ρ) (s := s) hPattern hNotTop ha hb).trans
        (patternPartition_rel_left_right_iff_of_eq s ha hb).symm
    · exact (realizedPartition_rel_right_left_iff_of_guardedPattern_not_top_all
        (ρ := ρ) (s := s) hPattern hNotTop ha hb).trans
        (patternPartition_rel_right_left_iff_of_eq s ha hb).symm
    · constructor
      · intro _
        exact patternPartition_rel_right_right_of_eq s ha hb
      · intro _
        exact realizedPartition_rel_right_right_of_eq ρ ha hb
  · constructor
    · intro hRel
      exact False.elim
        (realizedPartition_rel_false_of_pairIndex_ne_of_not_crossWiring_all
          (ρ := ρ) (n := n) hCrossFalse hIdx hRel)
    · intro hRel
      exact False.elim (patternPartition_rel_false_of_pairIndex_ne s hIdx hRel)

theorem realizedPartition_pair_eq_iff_of_guardedPattern_not_top_surj
    {α : Type u} [Infinite α] (ρ : Valuation α) {n : Nat} (s : Finset (Fin n))
    (hPattern : GuardedButtonPatternSurj ρ s) (hNotTop : s ≠ Finset.univ)
    (i : Fin n) :
    (realizedPartition ρ (2 * n)).r (leftFin i) (rightFin i) ↔ i ∈ s := by
  have hPair : HoldsInfSurj ρ (pairEq i.1) ↔ i ∈ s :=
    pairEq_holds_iff_of_guardedPattern_not_top_surj (ρ := ρ) (s := s) hPattern hNotTop i
  rw [holdsInfSurj_pure_iff_holds (ρ := ρ) (φ := pairEq i.1) (by trivial)] at hPair
  simpa [pairEq] using hPair

theorem realizedPartition_pair_eq_symm_iff_of_guardedPattern_not_top_surj
    {α : Type u} [Infinite α] (ρ : Valuation α) {n : Nat} (s : Finset (Fin n))
    (hPattern : GuardedButtonPatternSurj ρ s) (hNotTop : s ≠ Finset.univ)
    (i : Fin n) :
    (realizedPartition ρ (2 * n)).r (rightFin i) (leftFin i) ↔ i ∈ s := by
  constructor
  · intro h
    exact (realizedPartition_pair_eq_iff_of_guardedPattern_not_top_surj
      (ρ := ρ) (s := s) hPattern hNotTop i).mp
      ((realizedPartition ρ (2 * n)).symm h)
  · intro hi
    exact (realizedPartition ρ (2 * n)).symm <|
      (realizedPartition_pair_eq_iff_of_guardedPattern_not_top_surj
        (ρ := ρ) (s := s) hPattern hNotTop i).mpr hi

theorem realizedPartition_rel_left_right_iff_of_guardedPattern_not_top_surj
    {α : Type u} [Infinite α] (ρ : Valuation α) {n : Nat} (s : Finset (Fin n))
    (hPattern : GuardedButtonPatternSurj ρ s) (hNotTop : s ≠ Finset.univ)
    {a b : Fin (2 * n)} {i : Fin n}
    (ha : a = leftFin i) (hb : b = rightFin i) :
    (realizedPartition ρ (2 * n)).r a b ↔ i ∈ s := by
  change ρ a.1 = ρ b.1 ↔ i ∈ s
  have haVal : a.1 = leftVar i.1 := congrArg Fin.val ha
  have hbVal : b.1 = rightVar i.1 := congrArg Fin.val hb
  constructor
  · intro h
    have hPair : ρ (leftVar i.1) = ρ (rightVar i.1) := by
      calc
        ρ (leftVar i.1) = ρ a.1 := by rw [haVal]
        _ = ρ b.1 := h
        _ = ρ (rightVar i.1) := by rw [hbVal]
    exact (realizedPartition_pair_eq_iff_of_guardedPattern_not_top_surj
      (ρ := ρ) (s := s) hPattern hNotTop i).mp hPair
  · intro hi
    have hPair : ρ (leftVar i.1) = ρ (rightVar i.1) :=
      (realizedPartition_pair_eq_iff_of_guardedPattern_not_top_surj
        (ρ := ρ) (s := s) hPattern hNotTop i).mpr hi
    calc
      ρ a.1 = ρ (leftVar i.1) := by rw [haVal]
      _ = ρ (rightVar i.1) := hPair
      _ = ρ b.1 := by rw [hbVal]

theorem realizedPartition_rel_right_left_iff_of_guardedPattern_not_top_surj
    {α : Type u} [Infinite α] (ρ : Valuation α) {n : Nat} (s : Finset (Fin n))
    (hPattern : GuardedButtonPatternSurj ρ s) (hNotTop : s ≠ Finset.univ)
    {a b : Fin (2 * n)} {i : Fin n}
    (ha : a = rightFin i) (hb : b = leftFin i) :
    (realizedPartition ρ (2 * n)).r a b ↔ i ∈ s := by
  change ρ a.1 = ρ b.1 ↔ i ∈ s
  have haVal : a.1 = rightVar i.1 := congrArg Fin.val ha
  have hbVal : b.1 = leftVar i.1 := congrArg Fin.val hb
  constructor
  · intro h
    have hPair : ρ (rightVar i.1) = ρ (leftVar i.1) := by
      calc
        ρ (rightVar i.1) = ρ a.1 := by rw [haVal]
        _ = ρ b.1 := h
        _ = ρ (leftVar i.1) := by rw [hbVal]
    exact (realizedPartition_pair_eq_symm_iff_of_guardedPattern_not_top_surj
      (ρ := ρ) (s := s) hPattern hNotTop i).mp hPair
  · intro hi
    have hPair : ρ (rightVar i.1) = ρ (leftVar i.1) :=
      (realizedPartition_pair_eq_symm_iff_of_guardedPattern_not_top_surj
        (ρ := ρ) (s := s) hPattern hNotTop i).mpr hi
    calc
      ρ a.1 = ρ (rightVar i.1) := by rw [haVal]
      _ = ρ (leftVar i.1) := hPair
      _ = ρ b.1 := by rw [hbVal]

theorem realizedPartition_eq_pattern_of_guardedPattern_not_top_surj
    {α : Type u} [Infinite α] (ρ : Valuation α) {n : Nat} (s : Finset (Fin n))
    (hPattern : GuardedButtonPatternSurj ρ s) (hNotTop : s ≠ Finset.univ) :
    realizedPartition ρ (2 * n) = patternPartition n s := by
  have hCrossFalseSurj := crossWiring_false_of_guardedPattern_not_top_surj
    (ρ := ρ) (s := s) hPattern hNotTop
  ext a b
  by_cases hIdx : pairIndex a = pairIndex b
  · let i : Fin n := pairIndex a
    have haNorm : a = leftFin i ∨ a = rightFin i := by
      rcases eq_leftFin_or_rightFin a with ha | ha
      · left
        simpa [i] using ha
      · right
        simpa [i] using ha
    have hbNorm : b = leftFin i ∨ b = rightFin i := by
      rcases eq_leftFin_or_rightFin b with hb | hb
      · left
        have hb' : b = leftFin (pairIndex a) := by
          simpa [hIdx] using hb
        simpa [i] using hb'
      · right
        have hb' : b = rightFin (pairIndex a) := by
          simpa [hIdx] using hb
        simpa [i] using hb'
    rcases haNorm with ha | ha <;> rcases hbNorm with hb | hb
    · constructor
      · intro _
        exact patternPartition_rel_left_left_of_eq s ha hb
      · intro _
        exact realizedPartition_rel_left_left_of_eq ρ ha hb
    · exact (realizedPartition_rel_left_right_iff_of_guardedPattern_not_top_surj
        (ρ := ρ) (s := s) hPattern hNotTop ha hb).trans
        (patternPartition_rel_left_right_iff_of_eq s ha hb).symm
    · exact (realizedPartition_rel_right_left_iff_of_guardedPattern_not_top_surj
        (ρ := ρ) (s := s) hPattern hNotTop ha hb).trans
        (patternPartition_rel_right_left_iff_of_eq s ha hb).symm
    · constructor
      · intro _
        exact patternPartition_rel_right_right_of_eq s ha hb
      · intro _
        exact realizedPartition_rel_right_right_of_eq ρ ha hb
  · constructor
    · intro hRel
      exact False.elim
        (realizedPartition_rel_false_of_pairIndex_ne_of_not_crossWiring_surj
          (ρ := ρ) (n := n) hCrossFalseSurj hIdx hRel)
    · intro hRel
      exact False.elim (patternPartition_rel_false_of_pairIndex_ne s hIdx hRel)

theorem exists_allFunctions_guardedButton_pattern {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat}
    (hInj : prefixInjective ρ (2 * n))
    (s : Finset (Fin n)) :
    Nonempty (AllGuardedButtonPatternWitness (ρ := ρ) (s := s)) := by
  let hRef : Refines (realizedPartition ρ (2 * n)) (patternPartition n s) := by
    rw [realizedPartition_eq_discrete_of_injective ρ hInj]
    exact refines_from_discretePartition (patternPartition n s)
  let β : Type u := ULift (InfinitePartitionWitnessWorld (patternPartition n s))
  let hβ : Infinite β := inferInstance
  let f : α → β := fun a => ULift.up (allFunctionsInfiniteCoarseningMap ρ hRef a)
  refine ⟨AllGuardedButtonPatternWitness.mk β hβ f ?_⟩
  intro i
  exact guardedButton_holds_of_realizedPartition_eq_pattern
    (ρ := fun k => f (ρ k))
    (s := s)
    (i := i) <| by
      change realizedPartition
        (fun k => ULift.up (allFunctionsInfiniteCoarseningMap ρ hRef (ρ k))) (2 * n) =
          patternPartition n s
      rw [realizedPartition_ulift]
      exact realizedPartition_allFunctionsInfiniteCoarseningMap ρ hRef

theorem exists_surjections_guardedButton_pattern {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat}
    (hInj : prefixInjective ρ (2 * n))
    (s : Finset (Fin n)) :
    Nonempty (SurjGuardedButtonPatternWitness (ρ := ρ) (s := s)) := by
  let hRef : Refines (realizedPartition ρ (2 * n)) (patternPartition n s) := by
    rw [realizedPartition_eq_discrete_of_injective ρ hInj]
    exact refines_from_discretePartition (patternPartition n s)
  let β : Type u := InfiniteSurjCoarseningWorld ρ (patternPartition n s)
  let hβ : Infinite β := inferInstance
  let f : α → β := surjectionInfiniteCoarseningMap ρ hRef
  refine ⟨SurjGuardedButtonPatternWitness.mk β hβ f ?_ ?_⟩
  · simpa [f] using surjectionInfiniteCoarseningMap_surjective ρ hRef
  · intro i
    exact guardedButton_holds_of_realizedPartition_eq_pattern_surj
      (ρ := fun k => f (ρ k))
      (s := s)
      (i := i)
      (hPart := realizedPartition_surjectionInfiniteCoarseningMap ρ hRef)

theorem exists_allFunctions_guardedButton_pattern_above {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat} {s t : Finset (Fin n)}
    (hPart : realizedPartition ρ (2 * n) = patternPartition n s)
    (hst : s ⊆ t) :
    Nonempty (AllGuardedButtonPatternWitness (ρ := ρ) (s := t)) := by
  let hRef : Refines (realizedPartition ρ (2 * n)) (patternPartition n t) := by
    rw [hPart]
    exact patternPartition_refines_of_subset hst
  let β : Type u := ULift (InfinitePartitionWitnessWorld (patternPartition n t))
  let hβ : Infinite β := inferInstance
  let f : α → β := fun a => ULift.up (allFunctionsInfiniteCoarseningMap ρ hRef a)
  refine ⟨AllGuardedButtonPatternWitness.mk β hβ f ?_⟩
  intro i
  exact guardedButton_holds_of_realizedPartition_eq_pattern
    (ρ := fun k => f (ρ k))
    (s := t)
    (i := i) <| by
      change realizedPartition
        (fun k => ULift.up (allFunctionsInfiniteCoarseningMap ρ hRef (ρ k))) (2 * n) =
          patternPartition n t
      rw [realizedPartition_ulift]
      exact realizedPartition_allFunctionsInfiniteCoarseningMap ρ hRef

theorem exists_surjections_guardedButton_pattern_above {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat} {s t : Finset (Fin n)}
    (hPart : realizedPartition ρ (2 * n) = patternPartition n s)
    (hst : s ⊆ t) :
    Nonempty (SurjGuardedButtonPatternWitness (ρ := ρ) (s := t)) := by
  let hRef : Refines (realizedPartition ρ (2 * n)) (patternPartition n t) := by
    rw [hPart]
    exact patternPartition_refines_of_subset hst
  let β : Type u := InfiniteSurjCoarseningWorld ρ (patternPartition n t)
  let hβ : Infinite β := inferInstance
  let f : α → β := surjectionInfiniteCoarseningMap ρ hRef
  refine ⟨SurjGuardedButtonPatternWitness.mk β hβ f ?_ ?_⟩
  · simpa [f] using surjectionInfiniteCoarseningMap_surjective ρ hRef
  · intro i
    exact guardedButton_holds_of_realizedPartition_eq_pattern_surj
      (ρ := fun k => f (ρ k))
      (s := t)
      (i := i)
      (hPart := realizedPartition_surjectionInfiniteCoarseningMap ρ hRef)

theorem canonical_guardedButton_pattern_all {n : Nat} (s : Finset (Fin n)) :
    GuardedButtonPatternAll
      (σ := infinitePartitionWitnessValuationLift (patternPartition n s))
      s := by
  intro i
  exact guardedButton_holds_of_realizedPartition_eq_pattern
    (ρ := infinitePartitionWitnessValuationLift (patternPartition n s))
    (s := s)
    (i := i)
    (hPart := realizedPartition_infinitePartitionWitnessValuationLift
      (patternPartition n s))

theorem canonical_guardedButton_pattern_surj {n : Nat} (s : Finset (Fin n)) :
    GuardedButtonPatternSurj
      (σ := infinitePartitionWitnessValuationLift (patternPartition n s))
      s := by
  intro i
  exact guardedButton_holds_of_realizedPartition_eq_pattern_surj
    (ρ := infinitePartitionWitnessValuationLift (patternPartition n s))
    (s := s)
    (i := i)
    (hPart := realizedPartition_infinitePartitionWitnessValuationLift
      (patternPartition n s))

theorem canonical_allFunctions_guardedButton_pattern_extension {n : Nat}
    {s t : Finset (Fin n)} (hst : s ⊆ t) :
    Nonempty (AllGuardedButtonPatternWitness
      (ρ := infinitePartitionWitnessValuationLift (patternPartition n s))
      (s := t)) := by
  exact exists_allFunctions_guardedButton_pattern_above
    (ρ := infinitePartitionWitnessValuationLift (patternPartition n s))
    (s := s)
    (t := t)
    (hPart := realizedPartition_infinitePartitionWitnessValuationLift
      (patternPartition n s))
    hst

theorem canonical_surjections_guardedButton_pattern_extension {n : Nat}
    {s t : Finset (Fin n)} (hst : s ⊆ t) :
    Nonempty (SurjGuardedButtonPatternWitness
      (ρ := infinitePartitionWitnessValuationLift (patternPartition n s))
      (s := t)) := by
  exact exists_surjections_guardedButton_pattern_above
    (ρ := infinitePartitionWitnessValuationLift (patternPartition n s))
    (s := s)
    (t := t)
    (hPart := realizedPartition_infinitePartitionWitnessValuationLift
      (patternPartition n s))
    hst

theorem allFunctions_guardedButton_unpushed_at_root {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat}
    (hInj : Function.Injective (fun i : Fin (2 * n) => ρ i.1))
    (i : Fin n) :
    ¬ HoldsInfAll ρ (guardedButton i) := by
  intro h
  rcases h with hPair | hCross
  · exact allFunctions_button_unpushed_at_root ρ hInj i hPair
  · have hCross' :
        Holds allAccessibility ρ (crossWiring n) := by
      exact (holdsInfAll_pure_iff_holds (ρ := ρ) (φ := crossWiring n)
        (isPure_crossWiring n)).mp hCross
    rcases (holds_crossWiring_iff (ρ := ρ) n).mp hCross' with
      ⟨p, hpNe, hEq | hEq | hEq⟩
    · have hFinEq : leftFin p.1 = leftFin p.2 := by
        apply hInj
        simpa using hEq
      exact (leftFin_ne_leftFin_of_ne hpNe) hFinEq
    · have hFinEq : leftFin p.1 = rightFin p.2 := by
        apply hInj
        simpa using hEq
      exact (leftFin_ne_rightFin_any p.1 p.2) hFinEq
    · have hFinEq : rightFin p.1 = rightFin p.2 := by
        apply hInj
        simpa using hEq
      exact (rightFin_ne_rightFin_of_ne hpNe) hFinEq

theorem surjections_guardedButton_unpushed_at_root {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat}
    (hInj : Function.Injective (fun i : Fin (2 * n) => ρ i.1))
    (i : Fin n) :
    ¬ HoldsInfSurj ρ (guardedButton i) := by
  intro h
  rcases h with hPair | hCross
  · exact surjections_button_unpushed_at_root ρ hInj i hPair
  · have hCross' :
        Holds surjectiveAccessibility ρ (crossWiring n) := by
      exact (holdsInfSurj_pure_iff_holds (ρ := ρ) (φ := crossWiring n)
        (isPure_crossWiring n)).mp hCross
    rcases (holds_crossWiring_iff (admits := surjectiveAccessibility) (ρ := ρ) n).mp hCross' with
      ⟨p, hpNe, hEq | hEq | hEq⟩
    · have hFinEq : leftFin p.1 = leftFin p.2 := by
        apply hInj
        simpa using hEq
      exact (leftFin_ne_leftFin_of_ne hpNe) hFinEq
    · have hFinEq : leftFin p.1 = rightFin p.2 := by
        apply hInj
        simpa using hEq
      exact (leftFin_ne_rightFin_any p.1 p.2) hFinEq
    · have hFinEq : rightFin p.1 = rightFin p.2 := by
        apply hInj
        simpa using hEq
      exact (rightFin_ne_rightFin_of_ne hpNe) hFinEq

theorem nat_admits_allFunctions_guardedButton_pattern {n : Nat} (s : Finset (Fin n)) :
    Nonempty (AllGuardedButtonPatternWitness (ρ := fun k : Nat => k) (s := s)) :=
  exists_allFunctions_guardedButton_pattern
    (ρ := fun k : Nat => k)
    (hInj := prefixInjective_nat (2 * n))
    s

theorem nat_admits_surjections_guardedButton_pattern {n : Nat} (s : Finset (Fin n)) :
    Nonempty (SurjGuardedButtonPatternWitness (ρ := fun k : Nat => k) (s := s)) :=
  exists_surjections_guardedButton_pattern
    (ρ := fun k : Nat => k)
    (hInj := prefixInjective_nat (2 * n))
    s

theorem nat_guardedButton_is_button_all {n : Nat} (i : Fin n) :
    HoldsInfAll (fun k : Nat => k) (.diaQ (.boxQ (guardedButton i))) := by
  rcases nat_admits_allFunctions_guardedButton_pattern ({i} : Finset (Fin n)) with ⟨w⟩
  letI := w.hβ
  refine Exists.intro w.β ?_
  refine Exists.intro w.hβ ?_
  refine Exists.intro w.f ?_
  refine And.intro trivial ?_
  have hPush : HoldsInfAll (fun k => w.f k) (guardedButton i) := by
    simpa using (w.pattern i).2 (by simp)
  exact holdsInfAll_guardedButton_persistent (ρ := fun k => w.f k) i hPush

theorem nat_guardedButton_is_button_surj {n : Nat} (i : Fin n) :
    HoldsInfSurj (fun k : Nat => k) (.diaQ (.boxQ (guardedButton i))) := by
  rcases nat_admits_surjections_guardedButton_pattern ({i} : Finset (Fin n)) with ⟨w⟩
  letI := w.hβ
  refine Exists.intro w.β ?_
  refine Exists.intro w.hβ ?_
  refine Exists.intro w.f ?_
  refine And.intro w.hsurj ?_
  have hPush : HoldsInfSurj (fun k => w.f k) (guardedButton i) := by
    simpa using (w.pattern i).2 (by simp)
  exact holdsInfSurj_guardedButton_persistent (ρ := fun k => w.f k) i hPush

end Buttons

end HeytingLean.ModalCategorySets.Framework
