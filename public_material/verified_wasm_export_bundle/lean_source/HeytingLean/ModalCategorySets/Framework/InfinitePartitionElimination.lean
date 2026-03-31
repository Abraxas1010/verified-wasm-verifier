import HeytingLean.ModalCategorySets.Framework.PureFormulaElimination
import Mathlib.Data.Set.Finite.Basic

namespace HeytingLean.ModalCategorySets.Framework

open scoped Classical
open HeytingLean.ModalCategorySets.Framework.Equality

universe u

/-- Accessibility predicates constrained to the current universe of worlds. -/
abbrev ObjectAccessibility := {α β : Type u} → (α → β) → Prop

/-- Equality-language satisfaction with an explicit restriction on admissible target worlds. -/
def HoldsObj (WorldPred : Type u → Prop) (admits : ObjectAccessibility)
    {α : Type u} (hα : WorldPred α) (ρ : Valuation α) : EqAssertion → Prop :=
  fun φ =>
    match φ with
    | .falsum => False
    | .atomEq x y => ρ x = ρ y
    | .impl φ ψ => HoldsObj WorldPred admits hα ρ φ → HoldsObj WorldPred admits hα ρ ψ
    | .conj φ ψ => HoldsObj WorldPred admits hα ρ φ ∧ HoldsObj WorldPred admits hα ρ ψ
    | .disj φ ψ => HoldsObj WorldPred admits hα ρ φ ∨ HoldsObj WorldPred admits hα ρ ψ
    | .forallQ φ => (a : α) → HoldsObj WorldPred admits hα (extend ρ a) φ
    | .existsQ φ => Exists fun a : α => HoldsObj WorldPred admits hα (extend ρ a) φ
    | .boxQ φ =>
        (β : Type u) →
          (hβ : WorldPred β) →
            (f : α → β) →
              admits f →
                HoldsObj WorldPred admits hβ (fun x => f (ρ x)) φ
    | .diaQ φ =>
        Exists fun β : Type u =>
          Exists fun hβ : WorldPred β =>
            Exists fun f : α → β =>
              admits f ∧
                HoldsObj WorldPred admits hβ (fun x => f (ρ x)) φ

def allAccessibility : ObjectAccessibility := fun {_ _} _ => True

def surjectiveAccessibility : ObjectAccessibility := fun {_ _} f => Function.Surjective f

/-- Equality semantics for infinite worlds with arbitrary functions. -/
abbrev HoldsInfAll {α : Type u} [Infinite α] (ρ : Valuation α) (φ : EqAssertion) : Prop :=
  HoldsObj Infinite allAccessibility (show Infinite α from inferInstance) ρ φ

/-- Equality semantics for infinite worlds with surjective functions. -/
abbrev HoldsInfSurj {α : Type u} [Infinite α] (ρ : Valuation α) (φ : EqAssertion) : Prop :=
  HoldsObj Infinite surjectiveAccessibility (show Infinite α from inferInstance) ρ φ

theorem holdsObj_of_pure_iff_holds
    {WorldPred : Type u → Prop} {admitsObj : ObjectAccessibility} {admits : Accessibility}
    {α : Type u} (hα : WorldPred α) (ρ : Valuation α) {φ : EqAssertion}
    (hPure : Equality.IsPure φ) :
    HoldsObj WorldPred admitsObj hα ρ φ ↔
      HeytingLean.ModalCategorySets.Framework.Equality.Holds admits ρ φ := by
  induction φ generalizing α ρ with
  | falsum =>
      rfl
  | atomEq x y =>
      rfl
  | impl φ ψ ihφ ihψ =>
      rcases hPure with ⟨hPureφ, hPureψ⟩
      constructor
      · intro hImp hφ
        exact (ihψ hα ρ hPureψ).1 (hImp ((ihφ hα ρ hPureφ).2 hφ))
      · intro hImp hφ
        exact (ihψ hα ρ hPureψ).2 (hImp ((ihφ hα ρ hPureφ).1 hφ))
  | conj φ ψ ihφ ihψ =>
      rcases hPure with ⟨hPureφ, hPureψ⟩
      constructor
      · rintro ⟨hφ, hψ⟩
        exact And.intro ((ihφ hα ρ hPureφ).1 hφ) ((ihψ hα ρ hPureψ).1 hψ)
      · rintro ⟨hφ, hψ⟩
        exact And.intro ((ihφ hα ρ hPureφ).2 hφ) ((ihψ hα ρ hPureψ).2 hψ)
  | disj φ ψ ihφ ihψ =>
      rcases hPure with ⟨hPureφ, hPureψ⟩
      constructor
      · intro h
        rcases h with hφ | hψ
        · exact Or.inl ((ihφ hα ρ hPureφ).1 hφ)
        · exact Or.inr ((ihψ hα ρ hPureψ).1 hψ)
      · intro h
        rcases h with hφ | hψ
        · exact Or.inl ((ihφ hα ρ hPureφ).2 hφ)
        · exact Or.inr ((ihψ hα ρ hPureψ).2 hψ)
  | forallQ φ _ =>
      cases hPure
  | existsQ φ _ =>
      cases hPure
  | boxQ φ _ =>
      cases hPure
  | diaQ φ _ =>
      cases hPure

theorem holdsInfAll_pure_iff_holds {α : Type u} [Infinite α]
    (ρ : Valuation α) {φ : EqAssertion} (hPure : Equality.IsPure φ) :
    HoldsInfAll ρ φ ↔
      HeytingLean.ModalCategorySets.Framework.Equality.Holds allAccessibility ρ φ := by
  simpa [HoldsInfAll] using
    (holdsObj_of_pure_iff_holds
      (WorldPred := Infinite)
      (admitsObj := allAccessibility)
      (admits := allAccessibility)
      (hα := show Infinite α from inferInstance)
      (ρ := ρ)
      hPure)

theorem holdsInfSurj_pure_iff_holds {α : Type u} [Infinite α]
    (ρ : Valuation α) {φ : EqAssertion} (hPure : Equality.IsPure φ) :
    HoldsInfSurj ρ φ ↔
      HeytingLean.ModalCategorySets.Framework.Equality.Holds surjectiveAccessibility ρ φ := by
  simpa [HoldsInfSurj] using
    (holdsObj_of_pure_iff_holds
      (WorldPred := Infinite)
      (admitsObj := surjectiveAccessibility)
      (admits := surjectiveAccessibility)
      (hα := show Infinite α from inferInstance)
      (ρ := ρ)
      hPure)

theorem realizedPartition_zero_eq {α β : Type u}
    (ρ : Valuation α) (σ : Valuation β) :
    realizedPartition ρ 0 = realizedPartition σ 0 := by
  ext i j
  exact Fin.elim0 i

theorem isPure_conjList (φs : List EqAssertion)
    (hPure : ∀ φ, φ ∈ φs → Equality.IsPure φ) :
    Equality.IsPure (Equality.conjList φs) := by
  induction φs with
  | nil =>
      trivial
  | cons φ φs ih =>
      exact And.intro
        (hPure φ List.mem_cons_self)
        (ih (fun ψ hψ => hPure ψ (List.mem_cons_of_mem _ hψ)))

theorem isPure_disjList (φs : List EqAssertion)
    (hPure : ∀ φ, φ ∈ φs → Equality.IsPure φ) :
    Equality.IsPure (Equality.disjList φs) := by
  induction φs with
  | nil =>
      trivial
  | cons φ φs ih =>
      exact And.intro
        (hPure φ List.mem_cons_self)
        (ih (fun ψ hψ => hPure ψ (List.mem_cons_of_mem _ hψ)))

theorem isPure_eqPairsFormula (pairs : List (Var × Var)) :
    Equality.IsPure (Equality.eqPairsFormula pairs) := by
  apply isPure_conjList
  intro ψ hψ
  rcases List.mem_map.mp hψ with ⟨p, _, rfl⟩
  trivial

theorem isPure_neqPairsFormula (pairs : List (Var × Var)) :
    Equality.IsPure (Equality.neqPairsFormula pairs) := by
  apply isPure_conjList
  intro ψ hψ
  rcases List.mem_map.mp hψ with ⟨p, _, rfl⟩
  exact And.intro trivial trivial

theorem isPure_partitionFormulaOf {n : Nat} (P : FinPartition n) :
    Equality.IsPure (partitionFormulaOf P) := by
  unfold partitionFormulaOf eqPairsFormulaFin neqPairsFormulaFin
  exact And.intro
    (isPure_eqPairsFormula _)
    (isPure_neqPairsFormula _)

theorem isPure_disjList_partitionFormulas {n : Nat} (Ps : List (FinPartition n)) :
    Equality.IsPure
      (HeytingLean.ModalCategorySets.Framework.Equality.disjList (Ps.map partitionFormulaOf)) := by
  apply isPure_disjList
  intro ψ hψ
  rcases List.mem_map.mp hψ with ⟨P, _, rfl⟩
  exact isPure_partitionFormulaOf P

/-- Canonical infinite witness world for a finite partition pattern. -/
abbrev InfinitePartitionWitnessWorld {n : Nat} (P : FinPartition n) :=
  PartitionWorld P ⊕ Nat

instance instInfiniteInfinitePartitionWitnessWorld {n : Nat} (P : FinPartition n) :
    Infinite (InfinitePartitionWitnessWorld P) := by
  exact (infinite_sum).2 (Or.inr inferInstance)

/-- Canonical valuation realizing a partition pattern inside an infinite witness world. -/
def infinitePartitionWitnessValuation {n : Nat} (P : FinPartition n) :
    Valuation (InfinitePartitionWitnessWorld P) :=
  bindTuple (fun _ => Sum.inr 0) (fun i => Sum.inl (partitionTuple P i))

def infinitePartitionWitnessValuationLift {n : Nat} (P : FinPartition n) :
    Valuation (ULift.{u, 0} (InfinitePartitionWitnessWorld P)) :=
  fun i => ULift.up (infinitePartitionWitnessValuation P i)

@[simp] theorem infinitePartitionWitnessValuation_fin {n : Nat} (P : FinPartition n) (i : Fin n) :
    infinitePartitionWitnessValuation P i.1 = Sum.inl (partitionTuple P i) := by
  exact bindTuple_lt
    (ρ := fun _ => Sum.inr 0)
    (xs := fun j => Sum.inl (partitionTuple P j))
    i.2

theorem realizedPartition_infinitePartitionWitnessValuation {n : Nat} (P : FinPartition n) :
    realizedPartition (infinitePartitionWitnessValuation P) n = P := by
  ext i j
  change infinitePartitionWitnessValuation P i.1 =
      infinitePartitionWitnessValuation P j.1 ↔ P.r i j
  rw [infinitePartitionWitnessValuation_fin P i]
  rw [infinitePartitionWitnessValuation_fin P j]
  change Sum.inl (partitionTuple P i) = Sum.inl (partitionTuple P j) ↔ P.r i j
  constructor
  · intro h
    apply Quotient.exact
    exact Sum.inl.inj h
  · intro h
    exact congrArg Sum.inl (Quot.sound h)

def parameterSet {α : Type u} (ρ : Valuation α) (n : Nat) : Set α :=
  Set.range fun i : Fin n => ρ i.1

theorem parameterSet_finite {α : Type u} (ρ : Valuation α) (n : Nat) :
    (parameterSet ρ n).Finite := by
  unfold parameterSet
  exact Set.finite_range fun i : Fin n => ρ i.1

theorem exists_fresh_parameter {α : Type u} [Infinite α] (ρ : Valuation α) (n : Nat) :
    Exists fun a : α => a ∉ parameterSet ρ n := by
  have hInf : (parameterSet ρ n)ᶜ.Infinite := (parameterSet_finite ρ n).infinite_compl
  rcases hInf.nonempty with ⟨a, ha⟩
  exact Exists.intro a ha

theorem refines_realizedPartition_map {α β : Type u} (ρ : Valuation α) (f : α → β) (n : Nat) :
    Refines (realizedPartition ρ n) (realizedPartition (fun i => f (ρ i)) n) := by
  intro i j hij
  change f (ρ i.1) = f (ρ j.1)
  exact congrArg f hij

/-- Forget the distinguished variable `0` from a partition on `Fin (n+1)`. -/
def dropFirstPartition {n : Nat} (P : FinPartition (n + 1)) : FinPartition n where
  r i j := P.r i.succ j.succ
  iseqv := by
    exact Equivalence.mk
      (fun i => P.refl i.succ)
      (fun {i} {j} hij => P.symm hij)
      (fun {i} {j} {k} hij hjk => P.trans hij hjk)

theorem dropFirstPartition_realizedPartition_extend {α : Type u} (ρ : Valuation α) (a : α)
    (n : Nat) :
    dropFirstPartition (realizedPartition (extend ρ a) (n + 1)) = realizedPartition ρ n := by
  ext i j
  change extend ρ a i.succ.1 = extend ρ a j.succ.1 ↔ ρ i.1 = ρ j.1
  simp [extend]

noncomputable def allFunctionsInfiniteCoarseningMap {α : Type u} {n : Nat}
    (ρ : Valuation α) {Q : FinPartition n}
    (_hQ : Refines (realizedPartition ρ n) Q) :
    α → InfinitePartitionWitnessWorld Q := by
  classical
  intro a
  by_cases h : Nonempty {i : Fin n // ρ i.1 = a}
  · exact Sum.inl (partitionTuple Q (Classical.choice h).1)
  · exact Sum.inr 0

theorem allFunctionsInfiniteCoarseningMap_on_var {α : Type u} {n : Nat}
    (ρ : Valuation α) {Q : FinPartition n}
    (hQ : Refines (realizedPartition ρ n) Q) (i : Fin n) :
    allFunctionsInfiniteCoarseningMap ρ hQ (ρ i.1) = Sum.inl (partitionTuple Q i) := by
  classical
  have hWitness : Nonempty {j : Fin n // ρ j.1 = ρ i.1} :=
    Nonempty.intro (Subtype.mk i rfl)
  unfold allFunctionsInfiniteCoarseningMap
  split_ifs
  have hChooseEq : ρ (Classical.choice hWitness).1.1 = ρ i.1 := (Classical.choice hWitness).2
  have hQrel : Q.r (Classical.choice hWitness).1 i := by
    apply hQ
    change ρ (Classical.choice hWitness).1.1 = ρ i.1
    exact hChooseEq
  exact congrArg Sum.inl (Quot.sound hQrel)

theorem realizedPartition_allFunctionsInfiniteCoarseningMap {α : Type u} {n : Nat}
    (ρ : Valuation α) {Q : FinPartition n}
    (hQ : Refines (realizedPartition ρ n) Q) :
    realizedPartition (fun i => allFunctionsInfiniteCoarseningMap ρ hQ (ρ i)) n = Q := by
  ext i j
  change allFunctionsInfiniteCoarseningMap ρ hQ (ρ i.1) =
      allFunctionsInfiniteCoarseningMap ρ hQ (ρ j.1) ↔ Q.r i j
  rw [allFunctionsInfiniteCoarseningMap_on_var ρ hQ i]
  rw [allFunctionsInfiniteCoarseningMap_on_var ρ hQ j]
  change Sum.inl (partitionTuple Q i) = Sum.inl (partitionTuple Q j) ↔ Q.r i j
  constructor
  · intro h
    apply Quotient.exact
    exact Sum.inl.inj h
  · intro h
    exact congrArg Sum.inl (Quot.sound h)

theorem realizedPartition_ulift {α : Type u} (ρ : Valuation α) (n : Nat) :
    realizedPartition (fun i => ULift.up (ρ i)) n = realizedPartition ρ n := by
  ext i j
  change ULift.up (ρ i.1) = ULift.up (ρ j.1) ↔ ρ i.1 = ρ j.1
  constructor
  · intro h
    exact ULift.up.inj h
  · intro h
    exact congrArg ULift.up h

theorem realizedPartition_infinitePartitionWitnessValuationLift {n : Nat} (P : FinPartition n) :
    realizedPartition (infinitePartitionWitnessValuationLift P) n = P := by
  rw [realizedPartition_ulift]
  exact realizedPartition_infinitePartitionWitnessValuation P

abbrev FreshPointWorld {α : Type u} (ρ : Valuation α) (n : Nat) :=
  {a : α // a ∉ parameterSet ρ n}

instance instInfiniteFreshPointWorld {α : Type u} [Infinite α] (ρ : Valuation α) (n : Nat) :
    Infinite (FreshPointWorld ρ n) := by
  exact Set.Infinite.to_subtype ((parameterSet_finite ρ n).infinite_compl)

abbrev InfiniteSurjCoarseningWorld {α : Type u} {n : Nat}
    (ρ : Valuation α) (Q : FinPartition n) :=
  PartitionWorld Q ⊕ FreshPointWorld ρ n

instance instInfiniteInfiniteSurjCoarseningWorld {α : Type u} [Infinite α] {n : Nat}
    (ρ : Valuation α) (Q : FinPartition n) :
    Infinite (InfiniteSurjCoarseningWorld ρ Q) := by
  exact (infinite_sum).2 (Or.inr inferInstance)

noncomputable def surjectionInfiniteCoarseningMap {α : Type u} [Infinite α] {n : Nat}
    (ρ : Valuation α) {Q : FinPartition n}
    (_hQ : Refines (realizedPartition ρ n) Q) :
    α → InfiniteSurjCoarseningWorld ρ Q := by
  classical
  intro a
  by_cases h : Nonempty {i : Fin n // ρ i.1 = a}
  · exact Sum.inl (partitionTuple Q (Classical.choice h).1)
  · exact Sum.inr <|
      Subtype.mk a <| by
        intro ha
        apply h
        rcases ha with ⟨i, hi⟩
        exact Nonempty.intro (Subtype.mk i hi)

theorem surjectionInfiniteCoarseningMap_on_var {α : Type u} [Infinite α] {n : Nat}
    (ρ : Valuation α) {Q : FinPartition n}
    (hQ : Refines (realizedPartition ρ n) Q) (i : Fin n) :
    surjectionInfiniteCoarseningMap ρ hQ (ρ i.1) = Sum.inl (partitionTuple Q i) := by
  classical
  have hWitness : Nonempty {j : Fin n // ρ j.1 = ρ i.1} :=
    Nonempty.intro (Subtype.mk i rfl)
  unfold surjectionInfiniteCoarseningMap
  split_ifs
  have hChooseEq : ρ (Classical.choice hWitness).1.1 = ρ i.1 := (Classical.choice hWitness).2
  have hQrel : Q.r (Classical.choice hWitness).1 i := by
    apply hQ
    change ρ (Classical.choice hWitness).1.1 = ρ i.1
    exact hChooseEq
  exact congrArg Sum.inl (Quot.sound hQrel)

theorem surjectionInfiniteCoarseningMap_surjective {α : Type u} [Infinite α] {n : Nat}
    (ρ : Valuation α) {Q : FinPartition n}
    (hQ : Refines (realizedPartition ρ n) Q) :
    Function.Surjective (surjectionInfiniteCoarseningMap ρ hQ) := by
  intro y
  cases y with
  | inl q =>
      rcases Quotient.exists_rep q with ⟨i, rfl⟩
      exact Exists.intro (ρ i) (by
        simpa using surjectionInfiniteCoarseningMap_on_var ρ hQ i)
  | inr b =>
      refine Exists.intro b.1 ?_
      unfold surjectionInfiniteCoarseningMap
      have hNoWitness : ¬ Nonempty {i : Fin n // ρ i.1 = b.1} := by
        intro h
        apply b.2
        rcases h with ⟨i, hi⟩
        exact Exists.intro i hi
      rw [dif_neg hNoWitness]

theorem realizedPartition_surjectionInfiniteCoarseningMap {α : Type u} [Infinite α] {n : Nat}
    (ρ : Valuation α) {Q : FinPartition n}
    (hQ : Refines (realizedPartition ρ n) Q) :
    realizedPartition (fun i => surjectionInfiniteCoarseningMap ρ hQ (ρ i)) n = Q := by
  ext i j
  change surjectionInfiniteCoarseningMap ρ hQ (ρ i.1) =
      surjectionInfiniteCoarseningMap ρ hQ (ρ j.1) ↔ Q.r i j
  rw [surjectionInfiniteCoarseningMap_on_var ρ hQ i]
  rw [surjectionInfiniteCoarseningMap_on_var ρ hQ j]
  change Sum.inl (partitionTuple Q i) = Sum.inl (partitionTuple Q j) ↔ Q.r i j
  constructor
  · intro h
    apply Quotient.exact
    exact Sum.inl.inj h
  · intro h
    exact congrArg Sum.inl (Quot.sound h)

theorem exists_realize_partition_extension_infinite {α : Type u} [Infinite α] {n : Nat}
    (ρ : Valuation α) {R : FinPartition (n + 1)}
    (hDrop : dropFirstPartition R = realizedPartition ρ n) :
    Exists fun a : α =>
      realizedPartition (extend ρ a) (n + 1) = R := by
  classical
  have hDropEq : (i : Fin n) → (j : Fin n) → R.r i.succ j.succ ↔ ρ i.1 = ρ j.1 := by
    intro i j
    change (dropFirstPartition R).r i j ↔ ρ i.1 = ρ j.1
    rw [hDrop]
    rfl
  by_cases hZero : Nonempty {i : Fin n // R.r 0 i.succ}
  · let i0 : Fin n := (Classical.choice hZero).1
    let a0 : α := ρ i0.1
    refine Exists.intro a0 ?_
    ext x y
    induction x using Fin.cases with
    | zero =>
        induction y using Fin.cases with
        | zero =>
            change a0 = a0 ↔ R.r 0 0
            constructor
            · intro _
              exact R.refl 0
            · intro _
              rfl
        | succ j =>
            change a0 = ρ j.1 ↔ R.r 0 j.succ
            constructor
            · intro hEq
              have hSource : (realizedPartition ρ n).r i0 j := by
                change ρ i0.1 = ρ j.1
                simpa [a0] using hEq
              have hDropRel : R.r i0.succ j.succ := by
                exact (hDropEq i0 j).2 hSource
              exact R.trans (Classical.choice hZero).2 hDropRel
            · intro hR
              have hI0R : R.r i0.succ j.succ := by
                exact R.trans (R.symm (Classical.choice hZero).2) hR
              have hSource : (realizedPartition ρ n).r i0 j := by
                exact (hDropEq i0 j).1 hI0R
              change ρ i0.1 = ρ j.1 at hSource
              simpa [a0] using hSource
    | succ i =>
        induction y using Fin.cases with
        | zero =>
            change ρ i.1 = a0 ↔ R.r i.succ 0
            constructor
            · intro hEq
              have hSource : (realizedPartition ρ n).r i i0 := by
                change ρ i.1 = ρ i0.1
                simpa [a0] using hEq
              have hDropRel : R.r i.succ i0.succ := by
                exact (hDropEq i i0).2 hSource
              exact R.trans hDropRel (R.symm (Classical.choice hZero).2)
            · intro hR
              have hR' : R.r i.succ i0.succ := by
                exact R.trans hR (Classical.choice hZero).2
              have hSource : (realizedPartition ρ n).r i i0 := by
                exact (hDropEq i i0).1 hR'
              change ρ i.1 = ρ i0.1 at hSource
              simpa [a0] using hSource
        | succ j =>
            change ρ i.1 = ρ j.1 ↔ R.r i.succ j.succ
            exact (hDropEq i j).symm
  · rcases exists_fresh_parameter ρ n with ⟨a0, ha0⟩
    refine Exists.intro a0 ?_
    ext x y
    induction x using Fin.cases with
    | zero =>
        induction y using Fin.cases with
        | zero =>
            change a0 = a0 ↔ R.r 0 0
            constructor
            · intro _
              exact R.refl 0
            · intro _
              rfl
        | succ j =>
            change a0 = ρ j.1 ↔ R.r 0 j.succ
            constructor
            · intro hEq
              exfalso
              exact ha0 (Exists.intro j hEq.symm)
            · intro hR
              exfalso
              exact hZero (Nonempty.intro (Subtype.mk j hR))
    | succ i =>
        induction y using Fin.cases with
        | zero =>
            change ρ i.1 = a0 ↔ R.r i.succ 0
            constructor
            · intro hEq
              exfalso
              exact ha0 (Exists.intro i hEq)
            · intro hR
              exfalso
              exact hZero (Nonempty.intro (Subtype.mk i (R.symm hR)))
        | succ j =>
            change ρ i.1 = ρ j.1 ↔ R.r i.succ j.succ
            exact (hDropEq i j).symm

theorem holdsInfAll_of_realizedPartition_eq {α β : Type u} [Infinite α] [Infinite β]
    {ρ : Valuation α} {σ : Valuation β} {n : Nat} {φ : EqAssertion}
    (hUses : Equality.UsesOnlyLT n φ)
    (hPart : realizedPartition ρ n = realizedPartition σ n) :
    HoldsInfAll ρ φ ↔ HoldsInfAll σ φ := by
  induction φ generalizing α β ρ σ n with
  | falsum =>
      constructor <;> intro h <;> cases h
  | atomEq x y =>
      rcases hUses with ⟨hx, hy⟩
      have hEq :
          (realizedPartition ρ n).r (Fin.mk x hx) (Fin.mk y hy) =
            (realizedPartition σ n).r (Fin.mk x hx) (Fin.mk y hy) :=
        congrArg (fun P : FinPartition n => P.r (Fin.mk x hx) (Fin.mk y hy)) hPart
      change ρ x = ρ y ↔ σ x = σ y
      exact Iff.of_eq hEq
  | impl φ ψ ihφ ihψ =>
      rcases hUses with ⟨hUsesφ, hUsesψ⟩
      constructor
      · intro hImp hσφ
        exact (ihψ hUsesψ hPart).1 (hImp ((ihφ hUsesφ hPart).2 hσφ))
      · intro hImp hρφ
        exact (ihψ hUsesψ hPart).2 (hImp ((ihφ hUsesφ hPart).1 hρφ))
  | conj φ ψ ihφ ihψ =>
      rcases hUses with ⟨hUsesφ, hUsesψ⟩
      constructor
      · rintro ⟨hφ, hψ⟩
        exact And.intro ((ihφ hUsesφ hPart).1 hφ) ((ihψ hUsesψ hPart).1 hψ)
      · rintro ⟨hφ, hψ⟩
        exact And.intro ((ihφ hUsesφ hPart).2 hφ) ((ihψ hUsesψ hPart).2 hψ)
  | disj φ ψ ihφ ihψ =>
      rcases hUses with ⟨hUsesφ, hUsesψ⟩
      constructor
      · intro h
        rcases h with hφ | hψ
        · exact Or.inl ((ihφ hUsesφ hPart).1 hφ)
        · exact Or.inr ((ihψ hUsesψ hPart).1 hψ)
      · intro h
        rcases h with hφ | hψ
        · exact Or.inl ((ihφ hUsesφ hPart).2 hφ)
        · exact Or.inr ((ihψ hUsesψ hPart).2 hψ)
  | forallQ φ ih =>
      constructor
      · intro hForall b
        let R : FinPartition (n + 1) := realizedPartition (extend σ b) (n + 1)
        have hDropR : dropFirstPartition R = realizedPartition ρ n := by
          unfold R
          rw [dropFirstPartition_realizedPartition_extend]
          exact hPart.symm
        rcases exists_realize_partition_extension_infinite ρ hDropR with ⟨a, ha⟩
        have hPart' : realizedPartition (extend ρ a) (n + 1) =
            realizedPartition (extend σ b) (n + 1) := by
          exact ha.trans rfl
        exact (ih hUses hPart').1 (hForall a)
      · intro hForall a
        let R : FinPartition (n + 1) := realizedPartition (extend ρ a) (n + 1)
        have hDropR : dropFirstPartition R = realizedPartition σ n := by
          unfold R
          rw [dropFirstPartition_realizedPartition_extend]
          exact hPart
        rcases exists_realize_partition_extension_infinite σ hDropR with ⟨b, hb⟩
        have hPart' : realizedPartition (extend ρ a) (n + 1) =
            realizedPartition (extend σ b) (n + 1) := by
          exact rfl.trans hb.symm
        exact (ih hUses hPart').2 (hForall b)
  | existsQ φ ih =>
      constructor
      · rintro ⟨a, hφ⟩
        let R : FinPartition (n + 1) := realizedPartition (extend ρ a) (n + 1)
        have hDropR : dropFirstPartition R = realizedPartition σ n := by
          unfold R
          rw [dropFirstPartition_realizedPartition_extend]
          exact hPart
        rcases exists_realize_partition_extension_infinite σ hDropR with ⟨b, hb⟩
        refine Exists.intro b ?_
        have hPart' : realizedPartition (extend ρ a) (n + 1) =
            realizedPartition (extend σ b) (n + 1) := by
          exact rfl.trans hb.symm
        exact (ih hUses hPart').1 hφ
      · rintro ⟨b, hφ⟩
        let R : FinPartition (n + 1) := realizedPartition (extend σ b) (n + 1)
        have hDropR : dropFirstPartition R = realizedPartition ρ n := by
          unfold R
          rw [dropFirstPartition_realizedPartition_extend]
          exact hPart.symm
        rcases exists_realize_partition_extension_infinite ρ hDropR with ⟨a, ha⟩
        refine Exists.intro a ?_
        have hPart' : realizedPartition (extend ρ a) (n + 1) =
            realizedPartition (extend σ b) (n + 1) := by
          exact ha.trans rfl
        exact (ih hUses hPart').2 hφ
  | boxQ φ ih =>
      constructor
      · intro hBox γ hγ f _
        let Q : FinPartition n := realizedPartition (fun i => f (σ i)) n
        have hRefσ : Refines (realizedPartition σ n) Q :=
          refines_realizedPartition_map σ f n
        have hRefρ : Refines (realizedPartition ρ n) Q := by
          intro i j hij
          have hij' : (realizedPartition σ n).r i j := by
            simpa [hPart] using hij
          exact hRefσ i j hij'
        have hRealρ :
            realizedPartition
              (fun i => ULift.up (allFunctionsInfiniteCoarseningMap ρ hRefρ (ρ i))) n = Q := by
          rw [realizedPartition_ulift]
          exact realizedPartition_allFunctionsInfiniteCoarseningMap ρ hRefρ
        have hPart' :
            realizedPartition
              (fun i => ULift.up (allFunctionsInfiniteCoarseningMap ρ hRefρ (ρ i))) n =
              realizedPartition (fun i => f (σ i)) n := by
          exact hRealρ.trans rfl
        have hφρ :
            HoldsInfAll (fun i => ULift.up (allFunctionsInfiniteCoarseningMap ρ hRefρ (ρ i))) φ := by
          exact hBox (ULift (InfinitePartitionWitnessWorld Q)) inferInstance
            (fun a => ULift.up (allFunctionsInfiniteCoarseningMap ρ hRefρ a)) trivial
        exact (ih hUses hPart').1 hφρ
      · intro hBox γ hγ f _
        let Q : FinPartition n := realizedPartition (fun i => f (ρ i)) n
        have hRefρ : Refines (realizedPartition ρ n) Q :=
          refines_realizedPartition_map ρ f n
        have hRefσ : Refines (realizedPartition σ n) Q := by
          intro i j hij
          have hij' : (realizedPartition ρ n).r i j := by
            simpa [hPart] using hij
          exact hRefρ i j hij'
        have hRealσ :
            realizedPartition
              (fun i => ULift.up (allFunctionsInfiniteCoarseningMap σ hRefσ (σ i))) n = Q := by
          rw [realizedPartition_ulift]
          exact realizedPartition_allFunctionsInfiniteCoarseningMap σ hRefσ
        have hPart' :
            realizedPartition
              (fun i => f (ρ i)) n =
              realizedPartition
                (fun i => ULift.up (allFunctionsInfiniteCoarseningMap σ hRefσ (σ i))) n := by
          exact rfl.trans hRealσ.symm
        have hφσ :
            HoldsInfAll (fun i => ULift.up (allFunctionsInfiniteCoarseningMap σ hRefσ (σ i))) φ := by
          exact hBox (ULift (InfinitePartitionWitnessWorld Q)) inferInstance
            (fun a => ULift.up (allFunctionsInfiniteCoarseningMap σ hRefσ a)) trivial
        exact (ih hUses hPart').2 hφσ
  | diaQ φ ih =>
      constructor
      · rintro ⟨γ, hγ, f, -, hφ⟩
        let Q : FinPartition n := realizedPartition (fun i => f (ρ i)) n
        have hRefρ : Refines (realizedPartition ρ n) Q :=
          refines_realizedPartition_map ρ f n
        have hRefσ : Refines (realizedPartition σ n) Q := by
          intro i j hij
          have hij' : (realizedPartition ρ n).r i j := by
            simpa [hPart] using hij
          exact hRefρ i j hij'
        refine Exists.intro (ULift (InfinitePartitionWitnessWorld Q)) ?_
        refine Exists.intro (inferInstance : Infinite (ULift (InfinitePartitionWitnessWorld Q))) ?_
        refine Exists.intro (fun a => ULift.up (allFunctionsInfiniteCoarseningMap σ hRefσ a)) ?_
        constructor
        · trivial
        · have hPart' :
              realizedPartition (fun i => f (ρ i)) n =
                realizedPartition
                  (fun i => ULift.up (allFunctionsInfiniteCoarseningMap σ hRefσ (σ i))) n := by
              rw [realizedPartition_ulift]
              exact rfl.trans (realizedPartition_allFunctionsInfiniteCoarseningMap σ hRefσ).symm
          exact (ih hUses hPart').1 hφ
      · rintro ⟨γ, hγ, f, -, hφ⟩
        let Q : FinPartition n := realizedPartition (fun i => f (σ i)) n
        have hRefσ : Refines (realizedPartition σ n) Q :=
          refines_realizedPartition_map σ f n
        have hRefρ : Refines (realizedPartition ρ n) Q := by
          intro i j hij
          have hij' : (realizedPartition σ n).r i j := by
            simpa [hPart] using hij
          exact hRefσ i j hij'
        refine Exists.intro (ULift (InfinitePartitionWitnessWorld Q)) ?_
        refine Exists.intro (inferInstance : Infinite (ULift (InfinitePartitionWitnessWorld Q))) ?_
        refine Exists.intro (fun a => ULift.up (allFunctionsInfiniteCoarseningMap ρ hRefρ a)) ?_
        constructor
        · trivial
        · have hPart' :
              realizedPartition
                (fun i => ULift.up (allFunctionsInfiniteCoarseningMap ρ hRefρ (ρ i))) n =
                realizedPartition (fun i => f (σ i)) n := by
              rw [realizedPartition_ulift]
              exact (realizedPartition_allFunctionsInfiniteCoarseningMap ρ hRefρ).trans rfl
          exact (ih hUses hPart').2 hφ

theorem holdsInfSurj_of_realizedPartition_eq {α β : Type u} [Infinite α] [Infinite β]
    {ρ : Valuation α} {σ : Valuation β} {n : Nat} {φ : EqAssertion}
    (hUses : Equality.UsesOnlyLT n φ)
    (hPart : realizedPartition ρ n = realizedPartition σ n) :
    HoldsInfSurj ρ φ ↔ HoldsInfSurj σ φ := by
  induction φ generalizing α β ρ σ n with
  | falsum =>
      constructor <;> intro h <;> cases h
  | atomEq x y =>
      rcases hUses with ⟨hx, hy⟩
      have hEq :
          (realizedPartition ρ n).r (Fin.mk x hx) (Fin.mk y hy) =
            (realizedPartition σ n).r (Fin.mk x hx) (Fin.mk y hy) :=
        congrArg (fun P : FinPartition n => P.r (Fin.mk x hx) (Fin.mk y hy)) hPart
      change ρ x = ρ y ↔ σ x = σ y
      exact Iff.of_eq hEq
  | impl φ ψ ihφ ihψ =>
      rcases hUses with ⟨hUsesφ, hUsesψ⟩
      constructor
      · intro hImp hσφ
        exact (ihψ hUsesψ hPart).1 (hImp ((ihφ hUsesφ hPart).2 hσφ))
      · intro hImp hρφ
        exact (ihψ hUsesψ hPart).2 (hImp ((ihφ hUsesφ hPart).1 hρφ))
  | conj φ ψ ihφ ihψ =>
      rcases hUses with ⟨hUsesφ, hUsesψ⟩
      constructor
      · rintro ⟨hφ, hψ⟩
        exact And.intro ((ihφ hUsesφ hPart).1 hφ) ((ihψ hUsesψ hPart).1 hψ)
      · rintro ⟨hφ, hψ⟩
        exact And.intro ((ihφ hUsesφ hPart).2 hφ) ((ihψ hUsesψ hPart).2 hψ)
  | disj φ ψ ihφ ihψ =>
      rcases hUses with ⟨hUsesφ, hUsesψ⟩
      constructor
      · intro h
        rcases h with hφ | hψ
        · exact Or.inl ((ihφ hUsesφ hPart).1 hφ)
        · exact Or.inr ((ihψ hUsesψ hPart).1 hψ)
      · intro h
        rcases h with hφ | hψ
        · exact Or.inl ((ihφ hUsesφ hPart).2 hφ)
        · exact Or.inr ((ihψ hUsesψ hPart).2 hψ)
  | forallQ φ ih =>
      constructor
      · intro hForall b
        let R : FinPartition (n + 1) := realizedPartition (extend σ b) (n + 1)
        have hDropR : dropFirstPartition R = realizedPartition ρ n := by
          unfold R
          rw [dropFirstPartition_realizedPartition_extend]
          exact hPart.symm
        rcases exists_realize_partition_extension_infinite ρ hDropR with ⟨a, ha⟩
        have hPart' : realizedPartition (extend ρ a) (n + 1) =
            realizedPartition (extend σ b) (n + 1) := by
          exact ha.trans rfl
        exact (ih hUses hPart').1 (hForall a)
      · intro hForall a
        let R : FinPartition (n + 1) := realizedPartition (extend ρ a) (n + 1)
        have hDropR : dropFirstPartition R = realizedPartition σ n := by
          unfold R
          rw [dropFirstPartition_realizedPartition_extend]
          exact hPart
        rcases exists_realize_partition_extension_infinite σ hDropR with ⟨b, hb⟩
        have hPart' : realizedPartition (extend ρ a) (n + 1) =
            realizedPartition (extend σ b) (n + 1) := by
          exact rfl.trans hb.symm
        exact (ih hUses hPart').2 (hForall b)
  | existsQ φ ih =>
      constructor
      · rintro ⟨a, hφ⟩
        let R : FinPartition (n + 1) := realizedPartition (extend ρ a) (n + 1)
        have hDropR : dropFirstPartition R = realizedPartition σ n := by
          unfold R
          rw [dropFirstPartition_realizedPartition_extend]
          exact hPart
        rcases exists_realize_partition_extension_infinite σ hDropR with ⟨b, hb⟩
        refine Exists.intro b ?_
        have hPart' : realizedPartition (extend ρ a) (n + 1) =
            realizedPartition (extend σ b) (n + 1) := by
          exact rfl.trans hb.symm
        exact (ih hUses hPart').1 hφ
      · rintro ⟨b, hφ⟩
        let R : FinPartition (n + 1) := realizedPartition (extend σ b) (n + 1)
        have hDropR : dropFirstPartition R = realizedPartition ρ n := by
          unfold R
          rw [dropFirstPartition_realizedPartition_extend]
          exact hPart.symm
        rcases exists_realize_partition_extension_infinite ρ hDropR with ⟨a, ha⟩
        refine Exists.intro a ?_
        have hPart' : realizedPartition (extend ρ a) (n + 1) =
            realizedPartition (extend σ b) (n + 1) := by
          exact ha.trans rfl
        exact (ih hUses hPart').2 hφ
  | boxQ φ ih =>
      constructor
      · intro hBox γ hγ f hf
        let Q : FinPartition n := realizedPartition (fun i => f (σ i)) n
        have hRefσ : Refines (realizedPartition σ n) Q :=
          refines_realizedPartition_map σ f n
        have hRefρ : Refines (realizedPartition ρ n) Q := by
          intro i j hij
          have hij' : (realizedPartition σ n).r i j := by
            simpa [hPart] using hij
          exact hRefσ i j hij'
        have hRealρ :
            realizedPartition
              (fun i => surjectionInfiniteCoarseningMap ρ hRefρ (ρ i)) n = Q :=
          realizedPartition_surjectionInfiniteCoarseningMap ρ hRefρ
        have hPart' :
            realizedPartition
              (fun i => surjectionInfiniteCoarseningMap ρ hRefρ (ρ i)) n =
              realizedPartition (fun i => f (σ i)) n := by
          exact hRealρ.trans rfl
        have hφρ :
            HoldsInfSurj (fun i => surjectionInfiniteCoarseningMap ρ hRefρ (ρ i)) φ := by
          exact hBox (InfiniteSurjCoarseningWorld ρ Q) inferInstance
            (surjectionInfiniteCoarseningMap ρ hRefρ)
            (surjectionInfiniteCoarseningMap_surjective ρ hRefρ)
        exact (ih hUses hPart').1 hφρ
      · intro hBox γ hγ f hf
        let Q : FinPartition n := realizedPartition (fun i => f (ρ i)) n
        have hRefρ : Refines (realizedPartition ρ n) Q :=
          refines_realizedPartition_map ρ f n
        have hRefσ : Refines (realizedPartition σ n) Q := by
          intro i j hij
          have hij' : (realizedPartition ρ n).r i j := by
            simpa [hPart] using hij
          exact hRefρ i j hij'
        have hRealσ :
            realizedPartition
              (fun i => surjectionInfiniteCoarseningMap σ hRefσ (σ i)) n = Q :=
          realizedPartition_surjectionInfiniteCoarseningMap σ hRefσ
        have hPart' :
            realizedPartition
              (fun i => f (ρ i)) n =
              realizedPartition
                (fun i => surjectionInfiniteCoarseningMap σ hRefσ (σ i)) n := by
          exact rfl.trans hRealσ.symm
        have hφσ :
            HoldsInfSurj (fun i => surjectionInfiniteCoarseningMap σ hRefσ (σ i)) φ := by
          exact hBox (InfiniteSurjCoarseningWorld σ Q) inferInstance
            (surjectionInfiniteCoarseningMap σ hRefσ)
            (surjectionInfiniteCoarseningMap_surjective σ hRefσ)
        exact (ih hUses hPart').2 hφσ
  | diaQ φ ih =>
      constructor
      · rintro ⟨γ, hγ, f, hf, hφ⟩
        let Q : FinPartition n := realizedPartition (fun i => f (ρ i)) n
        have hRefρ : Refines (realizedPartition ρ n) Q :=
          refines_realizedPartition_map ρ f n
        have hRefσ : Refines (realizedPartition σ n) Q := by
          intro i j hij
          have hij' : (realizedPartition ρ n).r i j := by
            simpa [hPart] using hij
          exact hRefρ i j hij'
        refine Exists.intro (InfiniteSurjCoarseningWorld σ Q) ?_
        refine Exists.intro (instInfiniteInfiniteSurjCoarseningWorld σ Q) ?_
        refine Exists.intro (surjectionInfiniteCoarseningMap σ hRefσ) ?_
        constructor
        · exact surjectionInfiniteCoarseningMap_surjective σ hRefσ
        · have hPart' :
              realizedPartition (fun i => f (ρ i)) n =
                realizedPartition
                  (fun i => surjectionInfiniteCoarseningMap σ hRefσ (σ i)) n := by
              exact rfl.trans (realizedPartition_surjectionInfiniteCoarseningMap σ hRefσ).symm
          exact (ih hUses hPart').1 hφ
      · rintro ⟨γ, hγ, f, hf, hφ⟩
        let Q : FinPartition n := realizedPartition (fun i => f (σ i)) n
        have hRefσ : Refines (realizedPartition σ n) Q :=
          refines_realizedPartition_map σ f n
        have hRefρ : Refines (realizedPartition ρ n) Q := by
          intro i j hij
          have hij' : (realizedPartition σ n).r i j := by
            simpa [hPart] using hij
          exact hRefσ i j hij'
        refine Exists.intro (InfiniteSurjCoarseningWorld ρ Q) ?_
        refine Exists.intro (instInfiniteInfiniteSurjCoarseningWorld ρ Q) ?_
        refine Exists.intro (surjectionInfiniteCoarseningMap ρ hRefρ) ?_
        constructor
        · exact surjectionInfiniteCoarseningMap_surjective ρ hRefρ
        · have hPart' :
              realizedPartition
                (fun i => surjectionInfiniteCoarseningMap ρ hRefρ (ρ i)) n =
                realizedPartition (fun i => f (σ i)) n := by
              exact (realizedPartition_surjectionInfiniteCoarseningMap ρ hRefρ).trans rfl
          exact (ih hUses hPart').2 hφ

noncomputable def infSatisfyingPartitionsAll (_γ : Type u) (n : Nat)
    (φ : EqAssertion) : List (FinPartition n) := by
  classical
  exact (allFinitePartitions n).filter fun P =>
    HoldsInfAll
      (α := ULift.{u, 0} (InfinitePartitionWitnessWorld P))
      (infinitePartitionWitnessValuationLift P) φ

noncomputable def infSatisfyingPartitionsSurj (_γ : Type u) (n : Nat)
    (φ : EqAssertion) : List (FinPartition n) := by
  classical
  exact (allFinitePartitions n).filter fun P =>
    HoldsInfSurj
      (α := ULift.{u, 0} (InfinitePartitionWitnessWorld P))
      (infinitePartitionWitnessValuationLift P) φ

noncomputable def infPartitionElimAll (_γ : Type u) (n : Nat) (φ : EqAssertion) : EqAssertion := by
  classical
  exact disjList ((infSatisfyingPartitionsAll _γ n φ).map partitionFormulaOf)

noncomputable def infPartitionElimSurj (_γ : Type u) (n : Nat) (φ : EqAssertion) : EqAssertion := by
  classical
  exact disjList ((infSatisfyingPartitionsSurj _γ n φ).map partitionFormulaOf)

theorem holdsInfAll_partitionFormulaOf_iff_realizedPartition {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat} (P : FinPartition n) :
    HoldsInfAll ρ (partitionFormulaOf P) ↔ realizedPartition ρ n = P := by
  exact (holdsInfAll_pure_iff_holds (ρ := ρ) (φ := partitionFormulaOf P)
    (isPure_partitionFormulaOf P)).trans <|
      holds_partitionFormulaOf_iff_realizedPartition
        (admits := allAccessibility) (ρ := ρ) (P := P)

theorem holdsInfSurj_partitionFormulaOf_iff_realizedPartition {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat} (P : FinPartition n) :
    HoldsInfSurj ρ (partitionFormulaOf P) ↔ realizedPartition ρ n = P := by
  exact (holdsInfSurj_pure_iff_holds (ρ := ρ) (φ := partitionFormulaOf P)
    (isPure_partitionFormulaOf P)).trans <|
      holds_partitionFormulaOf_iff_realizedPartition
        (admits := surjectiveAccessibility) (ρ := ρ) (P := P)

theorem holdsInfAll_infPartitionElim_iff {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat} {φ : EqAssertion}
    (hUses : Equality.UsesOnlyLT n φ) :
    HoldsInfAll ρ (infPartitionElimAll α n φ) ↔ HoldsInfAll ρ φ := by
  classical
  have hPureElim : Equality.IsPure (infPartitionElimAll α n φ) := by
    simpa [infPartitionElimAll] using
      isPure_disjList_partitionFormulas (infSatisfyingPartitionsAll α n φ)
  constructor
  · intro hElim
    have hElim' : Holds allAccessibility ρ (infPartitionElimAll α n φ) :=
      (holdsInfAll_pure_iff_holds (ρ := ρ) (φ := infPartitionElimAll α n φ) hPureElim).1 hElim
    rcases (holds_disjList_iff
      (admits := allAccessibility)
      (ρ := ρ)
      (φs := (infSatisfyingPartitionsAll α n φ).map partitionFormulaOf)).mp
        (by simpa [infPartitionElimAll] using hElim')
      with ⟨ψ, hψ, hPartψ⟩
    rcases List.mem_map.mp hψ with ⟨P, hP, rfl⟩
    have hWitness :
        HoldsInfAll
          (α := ULift.{u, 0} (InfinitePartitionWitnessWorld P))
          (infinitePartitionWitnessValuationLift P) φ := by
      simpa [infSatisfyingPartitionsAll] using (List.mem_filter.mp hP).2
    have hReal :
        realizedPartition ρ n =
          realizedPartition (infinitePartitionWitnessValuationLift P) n := by
      have hρ : realizedPartition ρ n = P :=
        (holds_partitionFormulaOf_iff_realizedPartition
          (admits := allAccessibility) (ρ := ρ) (P := P)).mp hPartψ
      exact hρ.trans (realizedPartition_infinitePartitionWitnessValuationLift P).symm
    exact (holdsInfAll_of_realizedPartition_eq
      (ρ := ρ)
      (σ := infinitePartitionWitnessValuationLift P)
      (n := n)
      (φ := φ)
      hUses
      hReal).2 hWitness
  · intro hφ
    let P : FinPartition n := realizedPartition ρ n
    have hWitness :
        HoldsInfAll
          (α := ULift.{u, 0} (InfinitePartitionWitnessWorld P))
          (infinitePartitionWitnessValuationLift P) φ := by
      have hReal :
          realizedPartition (infinitePartitionWitnessValuationLift P) n =
            realizedPartition ρ n := by
        exact (realizedPartition_infinitePartitionWitnessValuationLift P).trans rfl
      exact (holdsInfAll_of_realizedPartition_eq
        (ρ := infinitePartitionWitnessValuationLift P)
        (σ := ρ)
        (n := n)
        (φ := φ)
        hUses
        hReal).2 hφ
    have hGoal : Holds allAccessibility ρ (infPartitionElimAll α n φ) := by
      refine (holds_disjList_iff
      (admits := allAccessibility)
      (ρ := ρ)
        (φs := (infSatisfyingPartitionsAll α n φ).map partitionFormulaOf)).mpr ?_
      refine Exists.intro (partitionFormulaOf P) ?_
      refine And.intro ?_ ?_
      · exact List.mem_map.mpr (Exists.intro P (And.intro
          (by
            refine List.mem_filter.mpr ?_
            exact And.intro (mem_allFinitePartitions P) (by simpa [P] using hWitness))
          rfl))
      · simpa [P] using
          (holds_partitionFormulaOf_realizedPartition (admits := allAccessibility) (ρ := ρ) n)
    exact (holdsInfAll_pure_iff_holds (ρ := ρ) (φ := infPartitionElimAll α n φ) hPureElim).2 hGoal

theorem holdsInfSurj_infPartitionElim_iff {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat} {φ : EqAssertion}
    (hUses : Equality.UsesOnlyLT n φ) :
    HoldsInfSurj ρ (infPartitionElimSurj α n φ) ↔ HoldsInfSurj ρ φ := by
  classical
  have hPureElim : Equality.IsPure (infPartitionElimSurj α n φ) := by
    simpa [infPartitionElimSurj] using
      isPure_disjList_partitionFormulas (infSatisfyingPartitionsSurj α n φ)
  constructor
  · intro hElim
    have hElim' : Holds surjectiveAccessibility ρ (infPartitionElimSurj α n φ) :=
      (holdsInfSurj_pure_iff_holds (ρ := ρ) (φ := infPartitionElimSurj α n φ) hPureElim).1 hElim
    rcases (holds_disjList_iff
      (admits := surjectiveAccessibility)
      (ρ := ρ)
      (φs := (infSatisfyingPartitionsSurj α n φ).map partitionFormulaOf)).mp
        (by simpa [infPartitionElimSurj] using hElim')
      with ⟨ψ, hψ, hPartψ⟩
    rcases List.mem_map.mp hψ with ⟨P, hP, rfl⟩
    have hWitness :
        HoldsInfSurj
          (α := ULift.{u, 0} (InfinitePartitionWitnessWorld P))
          (infinitePartitionWitnessValuationLift P) φ := by
      simpa [infSatisfyingPartitionsSurj] using (List.mem_filter.mp hP).2
    have hReal :
        realizedPartition ρ n =
          realizedPartition (infinitePartitionWitnessValuationLift P) n := by
      have hρ : realizedPartition ρ n = P :=
        (holds_partitionFormulaOf_iff_realizedPartition
          (admits := surjectiveAccessibility) (ρ := ρ) (P := P)).mp hPartψ
      exact hρ.trans (realizedPartition_infinitePartitionWitnessValuationLift P).symm
    exact (holdsInfSurj_of_realizedPartition_eq
      (ρ := ρ)
      (σ := infinitePartitionWitnessValuationLift P)
      (n := n)
      (φ := φ)
      hUses
      hReal).2 hWitness
  · intro hφ
    let P : FinPartition n := realizedPartition ρ n
    have hWitness :
        HoldsInfSurj
          (α := ULift.{u, 0} (InfinitePartitionWitnessWorld P))
          (infinitePartitionWitnessValuationLift P) φ := by
      have hReal :
          realizedPartition (infinitePartitionWitnessValuationLift P) n =
            realizedPartition ρ n := by
        exact (realizedPartition_infinitePartitionWitnessValuationLift P).trans rfl
      exact (holdsInfSurj_of_realizedPartition_eq
        (ρ := infinitePartitionWitnessValuationLift P)
        (σ := ρ)
        (n := n)
        (φ := φ)
        hUses
        hReal).2 hφ
    have hGoal : Holds surjectiveAccessibility ρ (infPartitionElimSurj α n φ) := by
      refine (holds_disjList_iff
      (admits := surjectiveAccessibility)
      (ρ := ρ)
        (φs := (infSatisfyingPartitionsSurj α n φ).map partitionFormulaOf)).mpr ?_
      refine Exists.intro (partitionFormulaOf P) ?_
      refine And.intro ?_ ?_
      · exact List.mem_map.mpr (Exists.intro P (And.intro
          (by
            refine List.mem_filter.mpr ?_
            exact And.intro (mem_allFinitePartitions P) (by simpa [P] using hWitness))
          rfl))
      · simpa [P] using
          (holds_partitionFormulaOf_realizedPartition (admits := surjectiveAccessibility) (ρ := ρ) n)
    exact (holdsInfSurj_pure_iff_holds (ρ := ρ) (φ := infPartitionElimSurj α n φ) hPureElim).2 hGoal

theorem holdsInfAll_sentence_irrel {α β : Type u} [Infinite α] [Infinite β]
    (ρ : Valuation α) (σ : Valuation β) {φ : EqAssertion}
    (hUses : Equality.UsesOnlyLT 0 φ) :
    HoldsInfAll ρ φ ↔ HoldsInfAll σ φ :=
  holdsInfAll_of_realizedPartition_eq
    (ρ := ρ) (σ := σ) (n := 0) (φ := φ) hUses (realizedPartition_zero_eq ρ σ)

theorem holdsInfSurj_sentence_irrel {α β : Type u} [Infinite α] [Infinite β]
    (ρ : Valuation α) (σ : Valuation β) {φ : EqAssertion}
    (hUses : Equality.UsesOnlyLT 0 φ) :
    HoldsInfSurj ρ φ ↔ HoldsInfSurj σ φ :=
  holdsInfSurj_of_realizedPartition_eq
    (ρ := ρ) (σ := σ) (n := 0) (φ := φ) hUses (realizedPartition_zero_eq ρ σ)

end HeytingLean.ModalCategorySets.Framework
