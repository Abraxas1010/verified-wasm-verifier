import HeytingLean.ModalCategorySets.Framework.FiniteStateFrames
import HeytingLean.ModalCategorySets.Framework.SubstitutionValidity

namespace HeytingLean.ModalCategorySets.Framework

open HeytingLean.ModalCategorySets.Framework.Equality
open HeytingLean.ModalCategorySets.Propositional

universe u v

namespace PropSubst

theorem satisfies_partitionModelInfAll_iff_holdsInfAll_translate
    {ι : Type v} {n : Nat} {tau : ι → EqAssertion}
    (hTau : UsesOnlyLT n tau)
    {α : Type u} [Infinite α] (ρ : Valuation α) (phi : Formula ι) :
    let val : FinPartition n → ι → Prop := fun P p =>
      @HoldsInfAll (ULift.{u, 0} (InfinitePartitionWitnessWorld P))
        (by infer_instance)
        (infinitePartitionWitnessValuationLift.{u} P)
        (tau p)
    let M : Model (FinPartition n) ι := mkModel (partitionFrame n) val
    satisfies M (realizedPartition ρ n) phi ↔ HoldsInfAll ρ (translate tau phi) := by
  intro val M
  induction phi generalizing α ρ with
  | var p =>
      have hVal :
          val (realizedPartition ρ n) p ↔ HoldsInfAll ρ (tau p) := by
        simpa [val] using
          (holdsInfAll_of_realizedPartition_eq
            (ρ := infinitePartitionWitnessValuationLift.{u} (realizedPartition ρ n))
            (σ := ρ)
            (n := n)
            (φ := tau p)
            (hUses := hTau p)
            (by
              simpa using
                (realizedPartition_infinitePartitionWitnessValuationLift
                  (realizedPartition ρ n))))
      simpa [M] using hVal
  | bot =>
      rfl
  | imp phi psi ihPhi ihPsi =>
      constructor
      · intro hImp hPhi
        exact (ihPsi (ρ := ρ)).1 (hImp ((ihPhi (ρ := ρ)).2 hPhi))
      · intro hImp hPhi
        exact (ihPsi (ρ := ρ)).2 (hImp ((ihPhi (ρ := ρ)).1 hPhi))
  | conj phi psi ihPhi ihPsi =>
      constructor
      · rintro ⟨hPhi, hPsi⟩
        exact And.intro ((ihPhi (ρ := ρ)).1 hPhi) ((ihPsi (ρ := ρ)).1 hPsi)
      · rintro ⟨hPhi, hPsi⟩
        exact And.intro ((ihPhi (ρ := ρ)).2 hPhi) ((ihPsi (ρ := ρ)).2 hPsi)
  | disj phi psi ihPhi ihPsi =>
      constructor
      · intro h
        rcases h with hPhi | hPsi
        · exact Or.inl ((ihPhi (ρ := ρ)).1 hPhi)
        · exact Or.inr ((ihPsi (ρ := ρ)).1 hPsi)
      · intro h
        rcases h with hPhi | hPsi
        · exact Or.inl ((ihPhi (ρ := ρ)).2 hPhi)
        · exact Or.inr ((ihPsi (ρ := ρ)).2 hPsi)
  | box phi ih =>
      constructor
      · intro hBox β hβ f _
        have hRef :
            Refines (realizedPartition ρ n) (realizedPartition (fun i => f (ρ i)) n) :=
          refines_realizedPartition_map ρ f n
        exact (ih (ρ := fun i => f (ρ i))).1 (hBox _ hRef)
      · intro hBox Q hRef
        let f : α → ULift (InfinitePartitionWitnessWorld Q) :=
          fun a => ULift.up (allFunctionsInfiniteCoarseningMap ρ hRef a)
        have hLift :
            HoldsInfAll (fun i => f (ρ i)) (translate tau phi) := by
          exact hBox _ inferInstance f trivial
        have hModel :
            satisfies M (realizedPartition (fun i => f (ρ i)) n) phi :=
          (ih (α := ULift (InfinitePartitionWitnessWorld Q)) (ρ := fun i => f (ρ i))).2 hLift
        have hReal :
            realizedPartition (fun i => f (ρ i)) n = Q := by
          change realizedPartition
            (fun i => ULift.up (allFunctionsInfiniteCoarseningMap ρ hRef (ρ i))) n = Q
          rw [realizedPartition_ulift]
          exact realizedPartition_allFunctionsInfiniteCoarseningMap ρ hRef
        simpa [hReal] using hModel
  | dia phi ih =>
      constructor
      · rintro ⟨Q, hRef, hQ⟩
        let f : α → ULift (InfinitePartitionWitnessWorld Q) :=
          fun a => ULift.up (allFunctionsInfiniteCoarseningMap ρ hRef a)
        refine Exists.intro (ULift (InfinitePartitionWitnessWorld Q)) ?_
        refine Exists.intro (by infer_instance) ?_
        refine Exists.intro f ?_
        constructor
        · trivial
        · have hReal :
              realizedPartition (fun i => f (ρ i)) n = Q := by
            change realizedPartition
              (fun i => ULift.up (allFunctionsInfiniteCoarseningMap ρ hRef (ρ i))) n = Q
            rw [realizedPartition_ulift]
            exact realizedPartition_allFunctionsInfiniteCoarseningMap ρ hRef
          have hModel :
              satisfies M (realizedPartition (fun i => f (ρ i)) n) phi := by
            simpa [hReal] using hQ
          exact (ih (α := ULift (InfinitePartitionWitnessWorld Q)) (ρ := fun i => f (ρ i))).1 hModel
      · rintro ⟨β, hβ, f, -, hPhi⟩
        let Q : FinPartition n := realizedPartition (fun i => f (ρ i)) n
        have hRef :
            Refines (realizedPartition ρ n) Q :=
          refines_realizedPartition_map ρ f n
        refine Exists.intro Q ?_
        refine And.intro hRef ?_
        exact (ih (α := β) (ρ := fun i => f (ρ i))).2 hPhi

theorem satisfies_partitionModelInfSurj_iff_holdsInfSurj_translate
    {ι : Type v} {n : Nat} {tau : ι → EqAssertion}
    (hTau : UsesOnlyLT n tau)
    {α : Type u} [Infinite α] (ρ : Valuation α) (phi : Formula ι) :
    let val : FinPartition n → ι → Prop := fun P p =>
      @HoldsInfSurj (ULift.{u, 0} (InfinitePartitionWitnessWorld P))
        (by infer_instance)
        (infinitePartitionWitnessValuationLift.{u} P)
        (tau p)
    let M : Model (FinPartition n) ι := mkModel (partitionFrame n) val
    satisfies M (realizedPartition ρ n) phi ↔ HoldsInfSurj ρ (translate tau phi) := by
  intro val M
  induction phi generalizing α ρ with
  | var p =>
      have hVal :
          val (realizedPartition ρ n) p ↔ HoldsInfSurj ρ (tau p) := by
        simpa [val] using
          (holdsInfSurj_of_realizedPartition_eq
            (ρ := infinitePartitionWitnessValuationLift.{u} (realizedPartition ρ n))
            (σ := ρ)
            (n := n)
            (φ := tau p)
            (hUses := hTau p)
            (by
              simpa using
                (realizedPartition_infinitePartitionWitnessValuationLift
                  (realizedPartition ρ n))))
      simpa [M] using hVal
  | bot =>
      rfl
  | imp phi psi ihPhi ihPsi =>
      constructor
      · intro hImp hPhi
        exact (ihPsi (ρ := ρ)).1 (hImp ((ihPhi (ρ := ρ)).2 hPhi))
      · intro hImp hPhi
        exact (ihPsi (ρ := ρ)).2 (hImp ((ihPhi (ρ := ρ)).1 hPhi))
  | conj phi psi ihPhi ihPsi =>
      constructor
      · rintro ⟨hPhi, hPsi⟩
        exact And.intro ((ihPhi (ρ := ρ)).1 hPhi) ((ihPsi (ρ := ρ)).1 hPsi)
      · rintro ⟨hPhi, hPsi⟩
        exact And.intro ((ihPhi (ρ := ρ)).2 hPhi) ((ihPsi (ρ := ρ)).2 hPsi)
  | disj phi psi ihPhi ihPsi =>
      constructor
      · intro h
        rcases h with hPhi | hPsi
        · exact Or.inl ((ihPhi (ρ := ρ)).1 hPhi)
        · exact Or.inr ((ihPsi (ρ := ρ)).1 hPsi)
      · intro h
        rcases h with hPhi | hPsi
        · exact Or.inl ((ihPhi (ρ := ρ)).2 hPhi)
        · exact Or.inr ((ihPsi (ρ := ρ)).2 hPsi)
  | box phi ih =>
      constructor
      · intro hBox β hβ f hf
        have hRef :
            Refines (realizedPartition ρ n) (realizedPartition (fun i => f (ρ i)) n) :=
          refines_realizedPartition_map ρ f n
        exact (ih (ρ := fun i => f (ρ i))).1 (hBox _ hRef)
      · intro hBox Q hRef
        let f : α → InfiniteSurjCoarseningWorld ρ Q :=
          surjectionInfiniteCoarseningMap ρ hRef
        have hTarget :
            HoldsInfSurj (fun i => f (ρ i)) (translate tau phi) := by
          exact hBox _ inferInstance f (surjectionInfiniteCoarseningMap_surjective ρ hRef)
        have hModel :
            satisfies M (realizedPartition (fun i => f (ρ i)) n) phi :=
          (ih (α := InfiniteSurjCoarseningWorld ρ Q) (ρ := fun i => f (ρ i))).2 hTarget
        have hReal :
            realizedPartition (fun i => f (ρ i)) n = Q :=
          realizedPartition_surjectionInfiniteCoarseningMap ρ hRef
        simpa [hReal] using hModel
  | dia phi ih =>
      constructor
      · rintro ⟨Q, hRef, hQ⟩
        let f : α → InfiniteSurjCoarseningWorld ρ Q :=
          surjectionInfiniteCoarseningMap ρ hRef
        refine Exists.intro (InfiniteSurjCoarseningWorld ρ Q) ?_
        refine Exists.intro inferInstance ?_
        refine Exists.intro f ?_
        constructor
        · exact surjectionInfiniteCoarseningMap_surjective ρ hRef
        · have hReal :
              realizedPartition (fun i => f (ρ i)) n = Q :=
            realizedPartition_surjectionInfiniteCoarseningMap ρ hRef
          have hModel :
              satisfies M (realizedPartition (fun i => f (ρ i)) n) phi := by
            simpa [hReal] using hQ
          exact (ih (α := InfiniteSurjCoarseningWorld ρ Q) (ρ := fun i => f (ρ i))).1 hModel
      · rintro ⟨β, hβ, f, hf, hPhi⟩
        let Q : FinPartition n := realizedPartition (fun i => f (ρ i)) n
        have hRef :
            Refines (realizedPartition ρ n) Q :=
          refines_realizedPartition_map ρ f n
        refine Exists.intro Q ?_
        refine And.intro hRef ?_
        exact (ih (α := β) (ρ := fun i => f (ρ i))).2 hPhi

theorem holdsInfAll_translate_of_partitionFrame_valid {ι : Type v} {n : Nat}
    {tau : ι → EqAssertion} (hTau : UsesOnlyLT n tau)
    {phi : Formula ι} (hValid : (partitionFrame n).Valid phi)
    {α : Type u} [Infinite α] (ρ : Valuation α) :
    HoldsInfAll ρ (translate tau phi) := by
  let val : FinPartition n → ι → Prop := fun P p =>
    @HoldsInfAll (ULift.{u, 0} (InfinitePartitionWitnessWorld P))
      (by infer_instance)
      (infinitePartitionWitnessValuationLift.{u} P)
      (tau p)
  let M : Model (FinPartition n) ι := mkModel (partitionFrame n) val
  have hModel : satisfies M (realizedPartition ρ n) phi :=
    hValid val (realizedPartition ρ n)
  have hCorr :=
    satisfies_partitionModelInfAll_iff_holdsInfAll_translate
      (hTau := hTau) (ρ := ρ) phi
  dsimp [M] at hCorr
  exact hCorr.1 hModel

theorem holdsInfSurj_translate_of_partitionFrame_valid {ι : Type v} {n : Nat}
    {tau : ι → EqAssertion} (hTau : UsesOnlyLT n tau)
    {phi : Formula ι} (hValid : (partitionFrame n).Valid phi)
    {α : Type u} [Infinite α] (ρ : Valuation α) :
    HoldsInfSurj ρ (translate tau phi) := by
  let val : FinPartition n → ι → Prop := fun P p =>
    @HoldsInfSurj (ULift.{u, 0} (InfinitePartitionWitnessWorld P))
      (by infer_instance)
      (infinitePartitionWitnessValuationLift.{u} P)
      (tau p)
  let M : Model (FinPartition n) ι := mkModel (partitionFrame n) val
  have hModel : satisfies M (realizedPartition ρ n) phi :=
    hValid val (realizedPartition ρ n)
  have hCorr :=
    satisfies_partitionModelInfSurj_iff_holdsInfSurj_translate
      (hTau := hTau) (ρ := ρ) phi
  dsimp [M] at hCorr
  exact hCorr.1 hModel

end PropSubst

end HeytingLean.ModalCategorySets.Framework
