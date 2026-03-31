import HeytingLean.ModalCategorySets.Framework.PartitionFormulas
import HeytingLean.ModalCategorySets.Framework.FiniteCorrespondence
import HeytingLean.ModalCategorySets.Framework.EqualityMorphismBridge

namespace HeytingLean.ModalCategorySets.Framework

open HeytingLean.ModalCategorySets.Framework.Equality

universe u

/-- An always-inhabited carrier realizing a partition pattern on the first `n` variables. -/
abbrev PartitionWitnessWorld {n : Nat} (P : FinPartition n) := Option (PartitionWorld P)

/-- Canonical valuation whose first `n` variables realize `P`, with `none` as the default tail. -/
def partitionWitnessValuation {n : Nat} (P : FinPartition n) :
    Valuation (PartitionWitnessWorld P) :=
  bindTuple (fun _ => none) (fun i => some (partitionTuple P i))

@[simp] theorem partitionWitnessValuation_fin {n : Nat} (P : FinPartition n) (i : Fin n) :
    partitionWitnessValuation P i.1 = some (partitionTuple P i) := by
  exact bindTuple_lt (ρ := fun _ => none) (xs := fun j => some (partitionTuple P j)) i.2

theorem realizedPartition_partitionWitnessValuation {n : Nat} (P : FinPartition n) :
    realizedPartition (partitionWitnessValuation P) n = P := by
  ext i j
  change partitionWitnessValuation P i.1 = partitionWitnessValuation P j.1 ↔ P.r i j
  rw [partitionWitnessValuation_fin P i]
  rw [partitionWitnessValuation_fin P j]
  change some (partitionTuple P i) = some (partitionTuple P j) ↔ P.r i j
  constructor
  · intro h
    apply Quotient.exact
    exact Option.some.inj h
  · intro h
    exact congrArg some (Quot.sound h)

theorem holds_partitionFormulaOf_partitionWitnessValuation {admits : Accessibility} {n : Nat}
    (P : FinPartition n) :
    Holds admits (partitionWitnessValuation P) (partitionFormulaOf P) := by
  exact (holds_partitionFormulaOf_iff_realizedPartition
    (admits := admits) (ρ := partitionWitnessValuation P) (P := P)).mpr
      (realizedPartition_partitionWitnessValuation P)

def optionQuotientMap {n : Nat} {P Q : FinPartition n} (hPQ : Refines P Q) :
    PartitionWitnessWorld P → PartitionWitnessWorld Q
  | none => none
  | some q => some (quotientMapOfRefines hPQ q)

@[simp] theorem optionQuotientMap_partitionWitnessValuation {n : Nat}
    {P Q : FinPartition n} (hPQ : Refines P Q) (i : Fin n) :
    optionQuotientMap hPQ (partitionWitnessValuation P i.1) =
      partitionWitnessValuation Q i.1 := by
  rw [partitionWitnessValuation_fin P i]
  rw [partitionWitnessValuation_fin Q i]
  simp [optionQuotientMap]

theorem optionQuotientMap_surjective {n : Nat} {P Q : FinPartition n}
    (hPQ : Refines P Q) :
    Function.Surjective (optionQuotientMap hPQ) := by
  intro y
  cases y with
  | none =>
      exact Exists.intro none rfl
  | some q =>
      rcases quotientMapOfRefines_surjective hPQ q with ⟨p, hp⟩
      exact Exists.intro (some p) (by simp [optionQuotientMap]; rw [hp])

theorem realizedPartition_optionQuotientMap {n : Nat} {P Q : FinPartition n}
    (hPQ : Refines P Q) :
    realizedPartition (fun v => optionQuotientMap hPQ (partitionWitnessValuation P v)) n = Q := by
  ext i j
  change optionQuotientMap hPQ (partitionWitnessValuation P i.1) =
      optionQuotientMap hPQ (partitionWitnessValuation P j.1) ↔ Q.r i j
  rw [optionQuotientMap_partitionWitnessValuation hPQ i]
  rw [optionQuotientMap_partitionWitnessValuation hPQ j]
  rw [partitionWitnessValuation_fin Q i]
  rw [partitionWitnessValuation_fin Q j]
  change some (partitionTuple Q i) = some (partitionTuple Q j) ↔ Q.r i j
  constructor
  · intro h
    apply Quotient.exact
    exact Option.some.inj h
  · intro h
    exact congrArg some (Quot.sound h)

theorem refines_of_partitionFormula_hom
    {M : MorphismClass} {n : Nat} {P Q : FinPartition n}
    {β : Type u} {f : PartitionWitnessWorld P → β}
    (hf : Holds M.admits (fun i => f (partitionWitnessValuation P i)) (partitionFormulaOf Q)) :
    Refines P Q := by
  have hReal :
      realizedPartition (fun i => f (partitionWitnessValuation P i)) n = Q :=
    (holds_partitionFormulaOf_iff_realizedPartition
      (admits := M.admits) (ρ := fun i => f (partitionWitnessValuation P i)) (P := Q)).mp hf
  intro i j hij
  have hEq :
      f (partitionWitnessValuation P i.1) = f (partitionWitnessValuation P j.1) := by
    rw [partitionWitnessValuation_fin P i]
    rw [partitionWitnessValuation_fin P j]
    exact congrArg (fun x => f (some x)) (Quot.sound hij)
  have hRealRel : (realizedPartition (fun k => f (partitionWitnessValuation P k)) n).r i j := by
    change f (partitionWitnessValuation P i.1) = f (partitionWitnessValuation P j.1)
    exact hEq
  simpa [hReal] using hRealRel

theorem refines_of_holdsIn_dia_partitionFormulaOf
    {M : MorphismClass} {n : Nat} {P Q : FinPartition n}
    (h :
      HoldsIn M (partitionWitnessValuation P) (EqAssertion.diaQ (partitionFormulaOf Q))) :
    Refines P Q := by
  rcases h with ⟨β, f, hfAdm, hφ⟩
  exact refines_of_partitionFormula_hom (M := M) (P := P) (Q := Q) (f := f) hφ

theorem allFunctions_dia_partitionFormulaOf_iff_refines {n : Nat} {P Q : FinPartition n} :
    HoldsIn allFunctions (partitionWitnessValuation P) (EqAssertion.diaQ (partitionFormulaOf Q)) ↔
      Refines P Q := by
  constructor
  · exact refines_of_holdsIn_dia_partitionFormulaOf (M := allFunctions) (P := P) (Q := Q)
  · intro hPQ
    refine Exists.intro (PartitionWitnessWorld Q) ?_
    refine Exists.intro (optionQuotientMap hPQ) ?_
    constructor
    · trivial
    · exact (holds_partitionFormulaOf_iff_realizedPartition
        (admits := allFunctions.admits)
        (ρ := fun i => optionQuotientMap hPQ (partitionWitnessValuation P i))
        (P := Q)).mpr (realizedPartition_optionQuotientMap hPQ)

theorem surjections_dia_partitionFormulaOf_iff_refines {n : Nat} {P Q : FinPartition n} :
    HoldsIn surjections (partitionWitnessValuation P) (EqAssertion.diaQ (partitionFormulaOf Q)) ↔
      Refines P Q := by
  constructor
  · exact refines_of_holdsIn_dia_partitionFormulaOf (M := surjections) (P := P) (Q := Q)
  · intro hPQ
    refine Exists.intro (PartitionWitnessWorld Q) ?_
    refine Exists.intro (optionQuotientMap hPQ) ?_
    constructor
    · exact optionQuotientMap_surjective hPQ
    · exact (holds_partitionFormulaOf_iff_realizedPartition
        (admits := surjections.admits)
        (ρ := fun i => optionQuotientMap hPQ (partitionWitnessValuation P i))
        (P := Q)).mpr (realizedPartition_optionQuotientMap hPQ)

noncomputable def allFunctionsRefinementMap {α : Type u} {n : Nat}
    {P Q : FinPartition n} (ρ : Valuation α)
    (_hP : HoldsIn allFunctions ρ (partitionFormulaOf P))
    (_hPQ : Refines P Q) :
    α → ULift (PartitionWitnessWorld Q) := by
  classical
  intro a
  by_cases h : Nonempty {i : Fin n // ρ i.1 = a}
  · exact ULift.up (some (partitionTuple Q (Classical.choice h).1))
  · exact ULift.up none

theorem allFunctionsRefinementMap_on_var {α : Type u} {n : Nat}
    {P Q : FinPartition n} (ρ : Valuation α)
    (hP : HoldsIn allFunctions ρ (partitionFormulaOf P))
    (hPQ : Refines P Q) (i : Fin n) :
    allFunctionsRefinementMap ρ hP hPQ (ρ i.1) = ULift.up (some (partitionTuple Q i)) := by
  classical
  have hWitness : Nonempty {j : Fin n // ρ j.1 = ρ i.1} :=
    Nonempty.intro (Subtype.mk i rfl)
  have hRealP : realizedPartition ρ n = P :=
    (holds_partitionFormulaOf_iff_realizedPartition
      (admits := allFunctions.admits) (ρ := ρ) (P := P)).mp hP
  unfold allFunctionsRefinementMap
  rw [dif_pos hWitness]
  have hChooseEq : ρ (Classical.choice hWitness).1.1 = ρ i.1 :=
    (Classical.choice hWitness).2
  have hPrel : P.r (Classical.choice hWitness).1 i := by
    have hRealRel : (realizedPartition ρ n).r (Classical.choice hWitness).1 i := by
      change ρ (Classical.choice hWitness).1.1 = ρ i.1
      exact hChooseEq
    simpa [hRealP] using hRealRel
  have hQrel : Q.r (Classical.choice hWitness).1 i := hPQ _ _ hPrel
  exact congrArg ULift.up (congrArg some (Quot.sound hQrel))

theorem allFunctions_dia_partitionFormulaOf_iff_refines_of_holds
    {α : Type u} {n : Nat} {P Q : FinPartition n} (ρ : Valuation α)
    (hP : HoldsIn allFunctions ρ (partitionFormulaOf P)) :
    HoldsIn allFunctions ρ (EqAssertion.diaQ (partitionFormulaOf Q)) ↔
      Refines P Q := by
  constructor
  · intro hDia
    have hRealP : realizedPartition ρ n = P :=
      (holds_partitionFormulaOf_iff_realizedPartition
        (admits := allFunctions.admits) (ρ := ρ) (P := P)).mp hP
    rcases hDia with ⟨β, f, -, hQ⟩
    have hRealQ :
        realizedPartition (fun i => f (ρ i)) n = Q :=
      (holds_partitionFormulaOf_iff_realizedPartition
        (admits := allFunctions.admits) (ρ := fun i => f (ρ i)) (P := Q)).mp hQ
    intro i j hij
    have hPEq : ρ i.1 = ρ j.1 := by
      have hPrel : P.r i j := hij
      have hRealRel : (realizedPartition ρ n).r i j := by
        simpa [hRealP] using hPrel
      change ρ i.1 = ρ j.1 at hRealRel
      exact hRealRel
    have hQEq : f (ρ i.1) = f (ρ j.1) := congrArg f hPEq
    have hQRel : (realizedPartition (fun k => f (ρ k)) n).r i j := by
      change f (ρ i.1) = f (ρ j.1)
      exact hQEq
    simpa [hRealQ] using hQRel
  · intro hPQ
    refine Exists.intro (ULift (PartitionWitnessWorld Q)) ?_
    refine Exists.intro (allFunctionsRefinementMap ρ hP hPQ) ?_
    constructor
    · trivial
    · exact (holds_partitionFormulaOf_iff_realizedPartition
        (admits := allFunctions.admits)
        (ρ := fun i => allFunctionsRefinementMap ρ hP hPQ (ρ i))
        (P := Q)).mpr <| by
          ext i j
          change allFunctionsRefinementMap ρ hP hPQ (ρ i.1) =
              allFunctionsRefinementMap ρ hP hPQ (ρ j.1) ↔ Q.r i j
          rw [allFunctionsRefinementMap_on_var ρ hP hPQ i]
          rw [allFunctionsRefinementMap_on_var ρ hP hPQ j]
          change ULift.up (some (partitionTuple Q i)) =
              ULift.up (some (partitionTuple Q j)) ↔ Q.r i j
          constructor
          · intro h
            apply Quotient.exact
            exact Option.some.inj (ULift.up.inj h)
          · intro h
            exact congrArg ULift.up (congrArg some (Quot.sound h))

noncomputable def surjectionRefinementMap {α : Type u} {n : Nat}
    (hn : 0 < n) {P Q : FinPartition n} (ρ : Valuation α)
    (_hP : HoldsIn surjections ρ (partitionFormulaOf P))
    (_hPQ : Refines P Q) :
    α → ULift (PartitionWorld Q) := by
  classical
  intro a
  by_cases h : Nonempty {i : Fin n // ρ i.1 = a}
  · exact ULift.up (partitionTuple Q (Classical.choice h).1)
  · exact ULift.up (partitionTuple Q (Fin.mk 0 hn))

theorem surjectionRefinementMap_on_var {α : Type u} {n : Nat}
    (hn : 0 < n) {P Q : FinPartition n} (ρ : Valuation α)
    (hP : HoldsIn surjections ρ (partitionFormulaOf P))
    (hPQ : Refines P Q) (i : Fin n) :
    surjectionRefinementMap hn ρ hP hPQ (ρ i.1) = ULift.up (partitionTuple Q i) := by
  classical
  have hWitness : Nonempty {j : Fin n // ρ j.1 = ρ i.1} :=
    Nonempty.intro (Subtype.mk i rfl)
  have hRealP : realizedPartition ρ n = P :=
    (holds_partitionFormulaOf_iff_realizedPartition
      (admits := surjections.admits) (ρ := ρ) (P := P)).mp hP
  unfold surjectionRefinementMap
  rw [dif_pos hWitness]
  have hChooseEq : ρ (Classical.choice hWitness).1.1 = ρ i.1 :=
    (Classical.choice hWitness).2
  have hPrel : P.r (Classical.choice hWitness).1 i := by
    have hRealRel : (realizedPartition ρ n).r (Classical.choice hWitness).1 i := by
      change ρ (Classical.choice hWitness).1.1 = ρ i.1
      exact hChooseEq
    simpa [hRealP] using hRealRel
  have hQrel : Q.r (Classical.choice hWitness).1 i := hPQ _ _ hPrel
  exact congrArg ULift.up (Quot.sound hQrel)

theorem surjectionRefinementMap_surjective {α : Type u} {n : Nat}
    (hn : 0 < n) {P Q : FinPartition n} (ρ : Valuation α)
    (hP : HoldsIn surjections ρ (partitionFormulaOf P))
    (hPQ : Refines P Q) :
    Function.Surjective (surjectionRefinementMap hn ρ hP hPQ) := by
  intro q
  cases q with
  | up qdown =>
      refine Quotient.inductionOn qdown ?_
      intro i
      exact Exists.intro (ρ i.1) (surjectionRefinementMap_on_var hn ρ hP hPQ i)

theorem surjections_dia_partitionFormulaOf_iff_refines_of_holds
    {α : Type u} {n : Nat} (hn : 0 < n) {P Q : FinPartition n} (ρ : Valuation α)
    (hP : HoldsIn surjections ρ (partitionFormulaOf P)) :
    HoldsIn surjections ρ (EqAssertion.diaQ (partitionFormulaOf Q)) ↔
      Refines P Q := by
  constructor
  · intro hDia
    have hRealP : realizedPartition ρ n = P :=
      (holds_partitionFormulaOf_iff_realizedPartition
        (admits := surjections.admits) (ρ := ρ) (P := P)).mp hP
    rcases hDia with ⟨β, f, -, hQ⟩
    have hRealQ :
        realizedPartition (fun i => f (ρ i)) n = Q :=
      (holds_partitionFormulaOf_iff_realizedPartition
        (admits := surjections.admits) (ρ := fun i => f (ρ i)) (P := Q)).mp hQ
    intro i j hij
    have hPEq : ρ i.1 = ρ j.1 := by
      have hPrel : P.r i j := hij
      have hRealRel : (realizedPartition ρ n).r i j := by
        simpa [hRealP] using hPrel
      change ρ i.1 = ρ j.1 at hRealRel
      exact hRealRel
    have hQEq : f (ρ i.1) = f (ρ j.1) := congrArg f hPEq
    have hQRel : (realizedPartition (fun k => f (ρ k)) n).r i j := by
      change f (ρ i.1) = f (ρ j.1)
      exact hQEq
    simpa [hRealQ] using hQRel
  · intro hPQ
    refine Exists.intro (ULift (PartitionWorld Q)) ?_
    refine Exists.intro (surjectionRefinementMap hn ρ hP hPQ) ?_
    constructor
    · exact surjectionRefinementMap_surjective hn ρ hP hPQ
    · exact (holds_partitionFormulaOf_iff_realizedPartition
        (admits := surjections.admits)
        (ρ := fun i => surjectionRefinementMap hn ρ hP hPQ (ρ i))
        (P := Q)).mpr <| by
          ext i j
          change surjectionRefinementMap hn ρ hP hPQ (ρ i.1) =
              surjectionRefinementMap hn ρ hP hPQ (ρ j.1) ↔ Q.r i j
          rw [surjectionRefinementMap_on_var hn ρ hP hPQ i]
          rw [surjectionRefinementMap_on_var hn ρ hP hPQ j]
          constructor
          · intro h
            exact Quotient.exact (ULift.up.inj h)
          · intro h
            exact congrArg ULift.up (Quot.sound h)

end HeytingLean.ModalCategorySets.Framework
