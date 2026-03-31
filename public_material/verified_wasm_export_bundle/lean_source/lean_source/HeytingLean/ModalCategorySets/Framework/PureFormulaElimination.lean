import HeytingLean.ModalCategorySets.Framework.PartitionModalCorrespondence
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Function.Basic

namespace HeytingLean.ModalCategorySets.Framework

open scoped Classical
open HeytingLean.ModalCategorySets.Framework.Equality

namespace Equality

/-- Quantifier-free and modality-free equality formulas. -/
def IsPure : EqAssertion → Prop
  | .falsum => True
  | .atomEq _ _ => True
  | .impl φ ψ => IsPure φ ∧ IsPure ψ
  | .conj φ ψ => IsPure φ ∧ IsPure ψ
  | .disj φ ψ => IsPure φ ∧ IsPure ψ
  | .forallQ _ => False
  | .existsQ _ => False
  | .boxQ _ => False
  | .diaQ _ => False

/-- Every variable mentioned by the formula lies below `n`. -/
def UsesOnlyLT (n : Nat) : EqAssertion → Prop
  | .falsum => True
  | .atomEq x y => x < n ∧ y < n
  | .impl φ ψ => UsesOnlyLT n φ ∧ UsesOnlyLT n ψ
  | .conj φ ψ => UsesOnlyLT n φ ∧ UsesOnlyLT n ψ
  | .disj φ ψ => UsesOnlyLT n φ ∧ UsesOnlyLT n ψ
  | .forallQ φ => UsesOnlyLT (n + 1) φ
  | .existsQ φ => UsesOnlyLT (n + 1) φ
  | .boxQ φ => UsesOnlyLT n φ
  | .diaQ φ => UsesOnlyLT n φ

/-- Pure formulas ignore the admissibility predicate and only depend on the induced
finite equality pattern of the variables they mention. -/
theorem holds_pure_of_realizedPartition_eq
    {admits₁ admits₂ : Accessibility} {α β : Type}
    {ρ : Valuation α} {σ : Valuation β} {n : Nat} {φ : EqAssertion}
    (hPure : IsPure φ) (hUses : UsesOnlyLT n φ)
    (hPart : realizedPartition ρ n = realizedPartition σ n) :
    Holds admits₁ ρ φ ↔ Holds admits₂ σ φ := by
  induction φ generalizing α β ρ σ n with
  | falsum =>
      constructor <;> intro h <;> cases h
  | atomEq x y =>
      rcases hUses with ⟨hx, hy⟩
      have hEq :
          (realizedPartition ρ n).r (Fin.mk x hx) (Fin.mk y hy) =
            (realizedPartition σ n).r (Fin.mk x hx) (Fin.mk y hy) :=
        congrArg (fun P : FinPartition n => P.r (Fin.mk x hx) (Fin.mk y hy)) hPart
      have hRel : ρ x = ρ y ↔ σ x = σ y := by
        change (realizedPartition ρ n).r (Fin.mk x hx) (Fin.mk y hy) ↔
            (realizedPartition σ n).r (Fin.mk x hx) (Fin.mk y hy)
        exact Iff.of_eq hEq
      simpa [Holds] using hRel
  | impl φ ψ ihφ ihψ =>
      rcases hPure with ⟨hPureφ, hPureψ⟩
      rcases hUses with ⟨hUsesφ, hUsesψ⟩
      constructor
      · intro hImp hσφ
        exact (ihψ hPureψ hUsesψ hPart).1 (hImp ((ihφ hPureφ hUsesφ hPart).2 hσφ))
      · intro hImp hρφ
        exact (ihψ hPureψ hUsesψ hPart).2 (hImp ((ihφ hPureφ hUsesφ hPart).1 hρφ))
  | conj φ ψ ihφ ihψ =>
      rcases hPure with ⟨hPureφ, hPureψ⟩
      rcases hUses with ⟨hUsesφ, hUsesψ⟩
      constructor
      · rintro ⟨hφ, hψ⟩
        exact And.intro
          ((ihφ hPureφ hUsesφ hPart).1 hφ)
          ((ihψ hPureψ hUsesψ hPart).1 hψ)
      · rintro ⟨hφ, hψ⟩
        exact And.intro
          ((ihφ hPureφ hUsesφ hPart).2 hφ)
          ((ihψ hPureψ hUsesψ hPart).2 hψ)
  | disj φ ψ ihφ ihψ =>
      rcases hPure with ⟨hPureφ, hPureψ⟩
      rcases hUses with ⟨hUsesφ, hUsesψ⟩
      constructor
      · intro h
        rcases h with hφ | hψ
        · exact Or.inl ((ihφ hPureφ hUsesφ hPart).1 hφ)
        · exact Or.inr ((ihψ hPureψ hUsesψ hPart).1 hψ)
      · intro h
        rcases h with hφ | hψ
        · exact Or.inl ((ihφ hPureφ hUsesφ hPart).2 hφ)
        · exact Or.inr ((ihψ hPureψ hUsesψ hPart).2 hψ)
  | forallQ φ _ =>
      cases hPure
  | existsQ φ _ =>
      cases hPure
  | boxQ φ _ =>
      cases hPure
  | diaQ φ _ =>
      cases hPure

theorem holds_pure_irrel
    {admits₁ admits₂ : Accessibility} {α : Type}
    {ρ : Valuation α} {n : Nat} {φ : EqAssertion}
    (hPure : IsPure φ) (hUses : UsesOnlyLT n φ) :
    Holds admits₁ ρ φ ↔ Holds admits₂ ρ φ :=
  holds_pure_of_realizedPartition_eq
    (admits₁ := admits₁) (admits₂ := admits₂)
    (ρ := ρ) (σ := ρ) hPure hUses rfl

theorem holds_dia_congr {admits : Accessibility} {α : Type}
    (ρ : Valuation α) {φ ψ : EqAssertion}
    (hCongr : ∀ {β : Type} (σ : Valuation β), Holds admits σ φ ↔ Holds admits σ ψ) :
    Holds admits ρ (.diaQ φ) ↔ Holds admits ρ (.diaQ ψ) := by
  constructor
  · rintro ⟨β, f, hfAdm, hφ⟩
    refine Exists.intro β ?_
    refine Exists.intro f ?_
    exact And.intro hfAdm ((hCongr (σ := fun x => f (ρ x))).1 hφ)
  · rintro ⟨β, f, hfAdm, hψ⟩
    refine Exists.intro β ?_
    refine Exists.intro f ?_
    exact And.intro hfAdm ((hCongr (σ := fun x => f (ρ x))).2 hψ)

theorem holds_box_congr {admits : Accessibility} {α : Type}
    (ρ : Valuation α) {φ ψ : EqAssertion}
    (hCongr : ∀ {β : Type} (σ : Valuation β), Holds admits σ φ ↔ Holds admits σ ψ) :
    Holds admits ρ (.boxQ φ) ↔ Holds admits ρ (.boxQ ψ) := by
  constructor
  · intro h β f hfAdm
    exact (hCongr (σ := fun x => f (ρ x))).1 (h β f hfAdm)
  · intro h β f hfAdm
    exact (hCongr (σ := fun x => f (ρ x))).2 (h β f hfAdm)

end Equality

open Equality

/-- Finite partitions can be encoded by their Boolean equality matrix on `Fin n`. -/
noncomputable instance instFiniteFinPartition (n : Nat) : Finite (FinPartition n) := by
  classical
  let encode : FinPartition n → Fin n → Fin n → Bool := fun P i j => decide (P.r i j)
  letI : Finite (Fin n → Fin n → Bool) := by infer_instance
  have hEncode : Function.Injective encode := by
    intro P Q hPQ
    cases P with
    | mk rP iseqvP =>
        cases Q with
        | mk rQ iseqvQ =>
            change (fun i j => decide (rP i j)) = (fun i j => decide (rQ i j)) at hPQ
            have hRel : rP = rQ := by
              funext i j
              apply propext
              have hBool : decide (rP i j) = decide (rQ i j) := by
                exact congrFun (congrFun hPQ i) j
              constructor
              · intro hp
                have hqTrue : decide (rQ i j) = true := by
                  simpa [hp] using hBool.symm
                simpa using hqTrue
              · intro hq
                have hpTrue : decide (rP i j) = true := by
                  simpa [hq] using hBool
                simpa using hpTrue
            cases hRel
            have hEqv : iseqvP = iseqvQ := Subsingleton.elim _ _
            cases hEqv
            rfl
  exact Finite.of_injective encode hEncode

/-- Enumerate all finite partitions on the first `n` variables. -/
noncomputable def allFinitePartitions (n : Nat) : List (FinPartition n) := by
  classical
  letI : Fintype (FinPartition n) := Fintype.ofFinite (FinPartition n)
  exact (Finset.univ : Finset (FinPartition n)).toList

@[simp] theorem mem_allFinitePartitions {n : Nat} (P : FinPartition n) :
    P ∈ allFinitePartitions n := by
  classical
  unfold allFinitePartitions
  simp

/-- The partition states whose canonical witness valuation satisfies a pure formula. -/
noncomputable def satisfyingPartitions (n : Nat) (φ : EqAssertion) : List (FinPartition n) := by
  classical
  exact (allFinitePartitions n).filter fun P =>
    Holds allFunctions.admits (partitionWitnessValuation P) φ

@[simp] theorem mem_satisfyingPartitions {n : Nat} {φ : EqAssertion} {P : FinPartition n} :
    P ∈ satisfyingPartitions n φ ↔
      Holds allFunctions.admits (partitionWitnessValuation P) φ := by
  classical
  constructor
  · intro h
    simpa using (List.mem_filter.mp h).2
  · intro h
    refine List.mem_filter.mpr ?_
    exact And.intro (mem_allFinitePartitions P) (by simpa using h)

/-- Disjunctive partition normal form for a pure finite-window equality formula. -/
noncomputable def purePartitionElim (n : Nat) (φ : EqAssertion) : EqAssertion := by
  classical
  exact disjList ((satisfyingPartitions n φ).map partitionFormulaOf)

theorem holds_purePartitionElim_iff {admits : Accessibility} {α : Type}
    (ρ : Valuation α) {n : Nat} {φ : EqAssertion}
    (hPure : Equality.IsPure φ) (hUses : Equality.UsesOnlyLT n φ) :
    Holds admits ρ (purePartitionElim n φ) ↔ Holds admits ρ φ := by
  classical
  constructor
  · intro hElim
    rcases (holds_disjList_iff (admits := admits) (ρ := ρ)
      (φs := (satisfyingPartitions n φ).map partitionFormulaOf)).mp
        (by simpa [purePartitionElim] using hElim) with ⟨ψ, hψ, hPartψ⟩
    rcases List.mem_map.mp hψ with ⟨P, hP, rfl⟩
    have hWitnessAll : Holds allFunctions.admits (partitionWitnessValuation P) φ :=
      (mem_satisfyingPartitions (φ := φ) (P := P)).mp hP
    have hWitness : Holds admits (partitionWitnessValuation P) φ :=
      (Equality.holds_pure_irrel
        (admits₁ := allFunctions.admits)
        (admits₂ := admits)
        (α := PartitionWitnessWorld P)
        (ρ := partitionWitnessValuation P)
        (n := n) (φ := φ) hPure hUses).1 hWitnessAll
    have hReal :
        realizedPartition ρ n = realizedPartition (partitionWitnessValuation P) n := by
      exact
        ((holds_partitionFormulaOf_iff_realizedPartition
          (admits := admits) (ρ := ρ) (P := P)).mp hPartψ).trans
          (realizedPartition_partitionWitnessValuation P).symm
    exact (Equality.holds_pure_of_realizedPartition_eq
      (admits₁ := admits) (admits₂ := admits)
      (α := α) (β := PartitionWitnessWorld P)
      (ρ := ρ) (σ := partitionWitnessValuation P)
      (n := n) (φ := φ) hPure hUses hReal).2 hWitness
  · intro hφ
    let P : FinPartition n := realizedPartition ρ n
    have hAll : Holds allFunctions.admits ρ φ :=
      (Equality.holds_pure_irrel
        (admits₁ := admits)
        (admits₂ := allFunctions.admits)
        (ρ := ρ)
        (n := n) (φ := φ) hPure hUses).1 hφ
    have hWitnessAll : Holds allFunctions.admits (partitionWitnessValuation P) φ := by
      have hReal :
          realizedPartition ρ n = realizedPartition (partitionWitnessValuation P) n := by
        simpa [P] using (realizedPartition_partitionWitnessValuation P).symm
      exact (Equality.holds_pure_of_realizedPartition_eq
        (admits₁ := allFunctions.admits) (admits₂ := allFunctions.admits)
        (α := α) (β := PartitionWitnessWorld P)
        (ρ := ρ) (σ := partitionWitnessValuation P)
        (n := n) (φ := φ) hPure hUses hReal).1 hAll
    refine (holds_disjList_iff (admits := admits) (ρ := ρ)
      (φs := (satisfyingPartitions n φ).map partitionFormulaOf)).mpr ?_
    refine Exists.intro (partitionFormulaOf P) ?_
    refine And.intro ?_ ?_
    · exact List.mem_map.mpr (Exists.intro P (And.intro
        ((mem_satisfyingPartitions (φ := φ) (P := P)).2 hWitnessAll) rfl))
    · simpa [P] using
        (holds_partitionFormulaOf_realizedPartition (admits := admits) (ρ := ρ) n)

theorem holds_dia_purePartitionElim_iff {M : MorphismClass} {α : Type}
    (ρ : Valuation α) {n : Nat} {φ : EqAssertion}
    (hPure : Equality.IsPure φ) (hUses : Equality.UsesOnlyLT n φ) :
    HoldsIn M ρ (.diaQ φ) ↔ HoldsIn M ρ (.diaQ (purePartitionElim n φ)) := by
  exact Equality.holds_dia_congr (admits := M.admits) ρ <|
    fun σ => (holds_purePartitionElim_iff (admits := M.admits) (ρ := σ) hPure hUses).symm

theorem holds_box_purePartitionElim_iff {M : MorphismClass} {α : Type}
    (ρ : Valuation α) {n : Nat} {φ : EqAssertion}
    (hPure : Equality.IsPure φ) (hUses : Equality.UsesOnlyLT n φ) :
    HoldsIn M ρ (.boxQ φ) ↔ HoldsIn M ρ (.boxQ (purePartitionElim n φ)) := by
  exact Equality.holds_box_congr (admits := M.admits) ρ <|
    fun σ => (holds_purePartitionElim_iff (admits := M.admits) (ρ := σ) hPure hUses).symm

end HeytingLean.ModalCategorySets.Framework
