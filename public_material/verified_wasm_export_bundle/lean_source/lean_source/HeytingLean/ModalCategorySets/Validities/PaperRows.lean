import HeytingLean.ModalCategorySets.Framework.FiniteCorrespondence
import HeytingLean.ModalCategorySets.Framework.FiniteSententialCorrespondence
import HeytingLean.ModalCategorySets.Framework.InfinitePartitionElimination
import HeytingLean.ModalCategorySets.Propositional.Theories
import HeytingLean.ModalCategorySets.Framework.GuardedBooleanTransfer
import HeytingLean.ModalCategorySets.Framework.SubstitutionPartitionCorrespondence
import HeytingLean.ModalCategorySets.Framework.SubstitutionValidity
import HeytingLean.ModalCategorySets.Validities.FiniteControlFrames
import HeytingLean.ModalCategorySets.Validities.FiniteLatticeCharacterization
import HeytingLean.ModalCategorySets.Validities.GrzFinite

namespace HeytingLean.ModalCategorySets.Validities

open scoped Classical
open HeytingLean.ModalCategorySets.Framework
open HeytingLean.ModalCategorySets.Framework.Equality
open HeytingLean.ModalCategorySets.Propositional

universe u

/-- The finite sentential surjection row `Grz.3J_n` is witnessed by the canonical
surjection-line worlds: accessibility is exactly the finite linear-order relation. -/
theorem grz3j_n_row_rel_iff {n : Nat} (i j : Fin n) :
    surjections.toKripkeCategory.toFrame.rel (surjectionLineWorld n i) (surjectionLineWorld n j) ↔
      (surjectionLineFrame n).rel i j :=
  surjectionLineWorld_rel_iff i j

/-- Each canonical `Grz.3J_n` witness world carries the exact cardinality label
required by the paper's finite sentential surjection row. -/
theorem grz3j_n_row_realizes_label {n : Nat} (i : Fin n) :
    RealizesCardinalityLabel (surjectionLineWorld n i) (surjectionLineLabel n i) :=
  surjectionLineWorld_realizes_label i

/-- On a finite witness world, the row label is exactly the equality sentence
`exactCardinality (n - i)`. -/
theorem grz3j_n_row_exactCardinality_iff {α : Type u} [Fintype α]
    (ρ : Valuation α) {n : Nat} (i : Fin n) :
    HoldsIn surjections ρ (exactCardinality (n - i.1)) ↔
      Fintype.card α = n - i.1 :=
  holds_surjectionLine_exactCardinality_iff ρ i

/-- The empty-world functions row `Lollipop` is witnessed by the canonical
`lollipopWitnessWorld` construction: accessibility is exactly the lollipop frame. -/
theorem lollipop_row_rel_iff (m : Nat) (s t : LollipopState m) :
    allFunctions.toKripkeCategory.toFrame.rel (lollipopWitnessWorld m s) (lollipopWitnessWorld m t) ↔
      (lollipopFrame m).rel s t :=
  lollipopWitnessWorld_rel_iff m s t

/-- Exact labels are realized by the obvious finite witness type. -/
theorem realizes_exact_label_fin (n : Nat) :
    RealizesCardinalityLabel (Fin n) (.exact n) := by
  change Nonempty { hα : Fintype (Fin n) // @Fintype.card (Fin n) hα = n }
  let hα : Fintype (Fin n) := inferInstance
  exact Nonempty.intro (Subtype.mk hα (by simp [hα]))

/-- Lower-bound labels are realized by the identity embedding on `Fin n`. -/
theorem realizes_atLeast_label_fin (n : Nat) :
    RealizesCardinalityLabel (Fin n) (.atLeast n) := by
  change Nonempty { xs : Fin n → Fin n // Function.Injective xs }
  exact Nonempty.intro (Subtype.mk id (by intro _ _ hEq; exact hEq))

/-- Each lollipop witness world realizes the cardinality label attached to the
corresponding finite row state. -/
theorem lollipop_row_realizes_label (m : Nat) (s : LollipopState m) :
    RealizesCardinalityLabel (lollipopWitnessWorld m s) (lollipopLabel m s) := by
  cases s with
  | root =>
      change RealizesCardinalityLabel PEmpty (.exact 0)
      change Nonempty { hα : Fintype PEmpty // @Fintype.card PEmpty hα = 0 }
      let hα : Fintype PEmpty := inferInstance
      exact Nonempty.intro (Subtype.mk hα (by simp [hα]))
  | cluster i =>
      by_cases h : i.1 < m
      · unfold lollipopWitnessWorld lollipopLabel
        simp [h]
        exact realizes_exact_label_fin (i.1 + 1)
      · unfold lollipopWitnessWorld lollipopLabel
        simp [h]
        exact realizes_atLeast_label_fin (m + 1)

/-- The finite formulaic surjection row `Partition_n` is packaged by the exact
correspondence between refinement and surjective tuple-preserving maps. -/
theorem partition_n_row_iff_refines {n : Nat} {P Q : FinPartition n} :
    Nonempty {f : PartitionWorld P → PartitionWorld Q //
      Function.Surjective f ∧ PartitionTupleMap f} ↔
      Refines P Q :=
  exists_surjective_partition_map_iff_refines

/-- The finite formulaic functions row `Prepartition_n` is packaged by the exact
correspondence between refinement and tuple-preserving maps with extra target points. -/
theorem prepartition_n_row_iff_refines {n k l : Nat} (hn : 0 < n)
    {P Q : FinPartition n} :
    Nonempty {f : PrepartitionWorld P k → PrepartitionWorld Q l // PrepartitionTupleMap f} ↔
      Refines P Q :=
  exists_prepartition_map_iff_refines hn

/-- The finite formulaic surjection row carries the control-core lower bound
`T + 4 + .2 + Grz` on its canonical partition frame. -/
theorem partition_n_row_validates_grzDot2Core (n : Nat) :
    ValidatesGrzDot2Core (partitionFrame n) :=
  partitionFrame_validatesGrzDot2Core n

/-- The finite formulaic functions row carries the control lower bound `S4.2`
on its canonical bounded prepartition frame. -/
theorem prepartition_n_row_validates_s4Dot2 (n m : Nat) :
    ValidatesS4Dot2 (prepartitionFrame n m) :=
  prepartitionFrame_validatesS4Dot2 n m

/-- Corollary `InfSets-formulas-partitions`: every finite-window equality-modal formula
on an infinite world in `Sets` is equivalent to a finite disjunction of partition formulas. -/
theorem infsets_formulas_partition_normal_form {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat} {φ : EqAssertion}
    (hUses : Equality.UsesOnlyLT n φ) :
    HoldsInfAll ρ φ ↔
      HoldsInfAll ρ (Equality.disjList ((infSatisfyingPartitionsAll α n φ).map partitionFormulaOf)) := by
  simpa [infPartitionElimAll] using
    (holdsInfAll_infPartitionElim_iff (ρ := ρ) (n := n) (φ := φ) hUses).symm

/-- Corollary `InfSets[onto]-formulas-partitions`: every finite-window equality-modal formula
on an infinite world in `Sets[onto]` is equivalent to a finite disjunction of partition formulas. -/
theorem infsurj_formulas_partition_normal_form {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat} {φ : EqAssertion}
    (hUses : Equality.UsesOnlyLT n φ) :
    HoldsInfSurj ρ φ ↔
      HoldsInfSurj ρ (Equality.disjList ((infSatisfyingPartitionsSurj α n φ).map partitionFormulaOf)) := by
  simpa [infPartitionElimSurj] using
    (holdsInfSurj_infPartitionElim_iff (ρ := ρ) (n := n) (φ := φ) hUses).symm

/-- Corollary `InfSets-sentences-Triv`: closed equality-modal sentences have the same truth
value at every infinite world of `Sets`. -/
theorem infsets_sentences_truth_invariant {α β : Type u} [Infinite α] [Infinite β]
    (ρ : Valuation α) (σ : Valuation β) {φ : EqAssertion}
    (hUses : Equality.UsesOnlyLT 0 φ) :
    HoldsInfAll ρ φ ↔ HoldsInfAll σ φ :=
  holdsInfAll_sentence_irrel ρ σ hUses

/-- Corollary `InfSets[onto]-sentences-Triv`: closed equality-modal sentences have the same truth
value at every infinite world of `Sets[onto]`. -/
theorem infsurj_sentences_truth_invariant {α β : Type u} [Infinite α] [Infinite β]
    (ρ : Valuation α) (σ : Valuation β) {φ : EqAssertion}
    (hUses : Equality.UsesOnlyLT 0 φ) :
    HoldsInfSurj ρ φ ↔ HoldsInfSurj σ φ :=
  holdsInfSurj_sentence_irrel ρ σ hUses

/-- In the infinite-only functions subcategory, sentential propositional substitution
instances are truth-invariant across all infinite worlds. -/
theorem infsets_sentential_substitution_truth_invariant
    {ι : Type u} {α β : Type u} [Infinite α] [Infinite β]
    (ρ : Valuation α) (σ : Valuation β) {τ : ι → EqAssertion} {φ : Formula ι}
    (hSent : PropSubst.IsSentential τ) :
    HoldsInfAll ρ (PropSubst.translate τ φ) ↔
      HoldsInfAll σ (PropSubst.translate τ φ) :=
  PropSubst.holdsInfAll_translate_sentential_irrel ρ σ hSent

/-- In the infinite-only surjection subcategory, sentential propositional substitution
instances are truth-invariant across all infinite worlds. -/
theorem infsurj_sentential_substitution_truth_invariant
    {ι : Type u} {α β : Type u} [Infinite α] [Infinite β]
    (ρ : Valuation α) (σ : Valuation β) {τ : ι → EqAssertion} {φ : Formula ι}
    (hSent : PropSubst.IsSentential τ) :
    HoldsInfSurj ρ (PropSubst.translate τ φ) ↔
      HoldsInfSurj σ (PropSubst.translate τ φ) :=
  PropSubst.holdsInfSurj_translate_sentential_irrel ρ σ hSent

/-- The infinite-only functions row validates every sentential substitution instance
of `Triv`. This packages the paper's sentential `Triv` row for `InfSets`. -/
theorem infsets_sentential_triv_instance
    {ι : Type u} {α : Type u} [Infinite α]
    (ρ : Valuation α) {τ : ι → EqAssertion}
    (hSent : PropSubst.IsSentential τ) (p : ι) :
    HoldsInfAll ρ (PropSubst.translate τ (axiomTriv p)) :=
  PropSubst.holdsInfAll_translate_axiomTriv_of_sentential ρ hSent p

/-- The infinite-only surjection row validates every sentential substitution instance
of `Triv`. This packages the paper's sentential `Triv` row for `InfSets[onto]`. -/
theorem infsurj_sentential_triv_instance
    {ι : Type u} {α : Type u} [Infinite α]
    (ρ : Valuation α) {τ : ι → EqAssertion}
    (hSent : PropSubst.IsSentential τ) (p : ι) :
    HoldsInfSurj ρ (PropSubst.translate τ (axiomTriv p)) :=
  PropSubst.holdsInfSurj_translate_axiomTriv_of_sentential ρ hSent p

/-- Finite-window formulaic substitution instances of `T` hold in `InfSets`
because the partition frame is reflexive. -/
theorem infsets_formulaic_t_instance
    {ι : Type u} {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat} {τ : ι → EqAssertion}
    (hUses : PropSubst.UsesOnlyLT n τ) (p : ι) :
    HoldsInfAll ρ (PropSubst.translate τ (axiomT p)) := by
  exact PropSubst.holdsInfAll_translate_of_partitionFrame_valid
    (ρ := ρ)
    (hTau := hUses)
    (phi := axiomT p)
    (axiomT_valid_of_reflexive (partitionFrame_reflexive n) p)

/-- Finite-window formulaic substitution instances of `T` hold in `InfSets[onto]`
because the partition frame is reflexive. -/
theorem infsurj_formulaic_t_instance
    {ι : Type u} {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat} {τ : ι → EqAssertion}
    (hUses : PropSubst.UsesOnlyLT n τ) (p : ι) :
    HoldsInfSurj ρ (PropSubst.translate τ (axiomT p)) := by
  exact PropSubst.holdsInfSurj_translate_of_partitionFrame_valid
    (ρ := ρ)
    (hTau := hUses)
    (phi := axiomT p)
    (axiomT_valid_of_reflexive (partitionFrame_reflexive n) p)

/-- Finite-window formulaic substitution instances of `4` hold in `InfSets`
because the partition frame is transitive. -/
theorem infsets_formulaic_4_instance
    {ι : Type u} {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat} {τ : ι → EqAssertion}
    (hUses : PropSubst.UsesOnlyLT n τ) (p : ι) :
    HoldsInfAll ρ (PropSubst.translate τ (axiom4 p)) := by
  exact PropSubst.holdsInfAll_translate_of_partitionFrame_valid
    (ρ := ρ)
    (hTau := hUses)
    (phi := axiom4 p)
    (axiom4_valid_of_transitive (partitionFrame_transitive n) p)

/-- Finite-window formulaic substitution instances of `4` hold in `InfSets[onto]`
because the partition frame is transitive. -/
theorem infsurj_formulaic_4_instance
    {ι : Type u} {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat} {τ : ι → EqAssertion}
    (hUses : PropSubst.UsesOnlyLT n τ) (p : ι) :
    HoldsInfSurj ρ (PropSubst.translate τ (axiom4 p)) := by
  exact PropSubst.holdsInfSurj_translate_of_partitionFrame_valid
    (ρ := ρ)
    (hTau := hUses)
    (phi := axiom4 p)
    (axiom4_valid_of_transitive (partitionFrame_transitive n) p)

/-- The infinite-only functions row validates finite-window formulaic substitution
instances of `.2`. This is a lower-bound piece of the paper's `Grz.2` result for `InfSets`. -/
theorem infsets_formulaic_dot2_instance
    {ι : Type u} {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat} {τ : ι → EqAssertion}
    (hUses : PropSubst.UsesOnlyLT n τ) (p : ι) :
    HoldsInfAll ρ (PropSubst.translate τ (axiomDot2 p)) :=
  PropSubst.holdsInfAll_translate_axiomDot2_of_usesOnlyLT ρ hUses p

/-- The infinite-only surjections row validates finite-window formulaic substitution
instances of `.2`. This is a lower-bound piece of the paper's `Grz.2` result for
`InfSets[onto]`. -/
theorem infsurj_formulaic_dot2_instance
    {ι : Type u} {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat} {τ : ι → EqAssertion}
    (hUses : PropSubst.UsesOnlyLT n τ) (p : ι) :
    HoldsInfSurj ρ (PropSubst.translate τ (axiomDot2 p)) :=
  PropSubst.holdsInfSurj_translate_axiomDot2_of_usesOnlyLT ρ hUses p

/-- Finite-window formulaic substitution instances of `Grz` hold in `InfSets`
because every such substitution factors through the finite partition frame, which
is a finite partial order. -/
theorem infsets_formulaic_grz_instance
    {ι : Type u} {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat} {τ : ι → EqAssertion}
    (hUses : PropSubst.UsesOnlyLT n τ) (p : ι) :
    HoldsInfAll ρ (PropSubst.translate τ (axiomGrz p)) := by
  exact PropSubst.holdsInfAll_translate_of_partitionFrame_valid
    (ρ := ρ)
    (hTau := hUses)
    (phi := axiomGrz p) <|
      by
        intro val q
        exact
          (OrderedFrames.axiomGrz_valid_on_finite_partialOrder
            (W := FinPartition n) (α := ι) p) val q

/-- Finite-window formulaic substitution instances of `Grz` hold in `InfSets[onto]`
for the same partition-frame reason. -/
theorem infsurj_formulaic_grz_instance
    {ι : Type u} {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat} {τ : ι → EqAssertion}
    (hUses : PropSubst.UsesOnlyLT n τ) (p : ι) :
    HoldsInfSurj ρ (PropSubst.translate τ (axiomGrz p)) := by
  exact PropSubst.holdsInfSurj_translate_of_partitionFrame_valid
    (ρ := ρ)
    (hTau := hUses)
    (phi := axiomGrz p) <|
      by
        intro val q
        exact
          (OrderedFrames.axiomGrz_valid_on_finite_partialOrder
            (W := FinPartition n) (α := ι) p) val q

/-- Packaged finite-window `S4.2` lower bound for `InfSets`. -/
theorem infsets_formulaic_s4Dot2_package
    {ι : Type u} {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat} {τ : ι → EqAssertion} (p : ι)
    (hUses : PropSubst.UsesOnlyLT n τ) :
    HoldsInfAll ρ (PropSubst.translate τ (axiomT p)) ∧
      HoldsInfAll ρ (PropSubst.translate τ (axiom4 p)) ∧
        HoldsInfAll ρ (PropSubst.translate τ (axiomDot2 p)) := by
  exact And.intro
    (infsets_formulaic_t_instance (ρ := ρ) (n := n) (τ := τ) hUses p)
    (And.intro
      (infsets_formulaic_4_instance (ρ := ρ) (n := n) (τ := τ) hUses p)
      (infsets_formulaic_dot2_instance (ρ := ρ) (n := n) (τ := τ) hUses p))

/-- Packaged finite-window `S4.2` lower bound for `InfSets[onto]`. -/
theorem infsurj_formulaic_s4Dot2_package
    {ι : Type u} {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat} {τ : ι → EqAssertion} (p : ι)
    (hUses : PropSubst.UsesOnlyLT n τ) :
    HoldsInfSurj ρ (PropSubst.translate τ (axiomT p)) ∧
      HoldsInfSurj ρ (PropSubst.translate τ (axiom4 p)) ∧
        HoldsInfSurj ρ (PropSubst.translate τ (axiomDot2 p)) := by
  exact And.intro
    (infsurj_formulaic_t_instance (ρ := ρ) (n := n) (τ := τ) hUses p)
    (And.intro
      (infsurj_formulaic_4_instance (ρ := ρ) (n := n) (τ := τ) hUses p)
      (infsurj_formulaic_dot2_instance (ρ := ρ) (n := n) (τ := τ) hUses p))

/-- Packaged finite-window `T + 4 + .2 + Grz` lower bound for `InfSets`. -/
theorem infsets_formulaic_grzDot2Core_package
    {ι : Type u} {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat} {τ : ι → EqAssertion} (p : ι)
    (hUses : PropSubst.UsesOnlyLT n τ) :
    HoldsInfAll ρ (PropSubst.translate τ (axiomT p)) ∧
      HoldsInfAll ρ (PropSubst.translate τ (axiom4 p)) ∧
        HoldsInfAll ρ (PropSubst.translate τ (axiomDot2 p)) ∧
          HoldsInfAll ρ (PropSubst.translate τ (axiomGrz p)) := by
  exact And.intro
    (infsets_formulaic_t_instance (ρ := ρ) (n := n) (τ := τ) hUses p)
    (And.intro
      (infsets_formulaic_4_instance (ρ := ρ) (n := n) (τ := τ) hUses p)
      (And.intro
        (infsets_formulaic_dot2_instance (ρ := ρ) (n := n) (τ := τ) hUses p)
        (infsets_formulaic_grz_instance (ρ := ρ) (n := n) (τ := τ) hUses p)))

/-- Packaged finite-window `T + 4 + .2 + Grz` lower bound for `InfSets[onto]`. -/
theorem infsurj_formulaic_grzDot2Core_package
    {ι : Type u} {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat} {τ : ι → EqAssertion} (p : ι)
    (hUses : PropSubst.UsesOnlyLT n τ) :
    HoldsInfSurj ρ (PropSubst.translate τ (axiomT p)) ∧
      HoldsInfSurj ρ (PropSubst.translate τ (axiom4 p)) ∧
        HoldsInfSurj ρ (PropSubst.translate τ (axiomDot2 p)) ∧
          HoldsInfSurj ρ (PropSubst.translate τ (axiomGrz p)) := by
  exact And.intro
    (infsurj_formulaic_t_instance (ρ := ρ) (n := n) (τ := τ) hUses p)
    (And.intro
      (infsurj_formulaic_4_instance (ρ := ρ) (n := n) (τ := τ) hUses p)
      (And.intro
        (infsurj_formulaic_dot2_instance (ρ := ρ) (n := n) (τ := τ) hUses p)
        (infsurj_formulaic_grz_instance (ρ := ρ) (n := n) (τ := τ) hUses p)))

/-- Exact semantic upper bound exported from the guarded-button Boolean transfer:
a propositional formula holds under every guarded-label translation in `InfSets`
iff it is valid on all finite Boolean frames. This is the completed local control
transfer; identifying that benchmark with the paper's syntactic `Grz.2` theory is
a separate external theorem. -/
theorem infsets_formulaic_boolean_upper_bound
    {ι : Type u} {phi : Formula ι} :
    BooleanFrames.ValidOnAllFiniteBooleanFrames phi ↔
      ∀ n, Buttons.AllGuardedLabelSubstValid n phi :=
  Buttons.validOnAllFiniteBooleanFrames_iff_holdsInfAll_guardedLabelSubst

/-- Surjective analogue of `infsets_formulaic_boolean_upper_bound`. -/
theorem infsurj_formulaic_boolean_upper_bound
    {ι : Type u} {phi : Formula ι} :
    BooleanFrames.ValidOnAllFiniteBooleanFrames phi ↔
      ∀ n, Buttons.SurjGuardedLabelSubstValid n phi :=
  Buttons.validOnAllFiniteBooleanFrames_iff_holdsInfSurj_guardedLabelSubst

/-- Pointed refinement of `infsets_formulaic_boolean_upper_bound`: because every world
of a finite Boolean frame can be shifted back to `∅`, the finite-Boolean benchmark is
equivalent to validity of every guarded-label translation at the canonical `Nat` root
of `InfSets`. This is the exact local pointed benchmark used by the paper's upper-bound
route; only the external identification of that benchmark with syntactic `Grz.2`
remains outside the repo. -/
theorem infsets_formulaic_boolean_upper_bound_at_nat_root
    {ι : Type u} {phi : Formula ι} :
    BooleanFrames.ValidOnAllFiniteBooleanFrames phi ↔
      ∀ n val, HoldsInfAll (fun k : Nat => k)
        (PropSubst.translate (Buttons.guardedLabelSubst n val) phi) :=
  Buttons.validOnAllFiniteBooleanFrames_iff_holdsInfAll_guardedLabelSubst_at_nat_root

/-- Surjective analogue of `infsets_formulaic_boolean_upper_bound_at_nat_root`. -/
theorem infsurj_formulaic_boolean_upper_bound_at_nat_root
    {ι : Type u} {phi : Formula ι} :
    BooleanFrames.ValidOnAllFiniteBooleanFrames phi ↔
      ∀ n val, HoldsInfSurj (fun k : Nat => k)
        (PropSubst.translate (Buttons.guardedLabelSubst n val) phi) :=
  Buttons.validOnAllFiniteBooleanFrames_iff_holdsInfSurj_guardedLabelSubst_at_nat_root

/-- The finite-Boolean benchmark is exactly the same as bottom-world validity on every
finite join-semilattice with bottom. Composed with the `Nat`-root guarded transfer, this
is the strongest fully internal semantic upper-bound theorem now present in the repo. -/
theorem infsets_formulaic_finiteJoinSemilattice_upper_bound_at_nat_root
    {ι : Type u} {phi : Formula ι} :
    FiniteLatticeCharacterization.ValidAtBottomAllFiniteJoinSemilattices phi ↔
      ∀ n val, HoldsInfAll (fun k : Nat => k)
        (PropSubst.translate (Buttons.guardedLabelSubst n val) phi) := by
  rw [← FiniteLatticeCharacterization.validOnAllFiniteBooleanFrames_iff_validAtBottom]
  exact infsets_formulaic_boolean_upper_bound_at_nat_root

/-- Surjective analogue of `infsets_formulaic_finiteJoinSemilattice_upper_bound_at_nat_root`. -/
theorem infsurj_formulaic_finiteJoinSemilattice_upper_bound_at_nat_root
    {ι : Type u} {phi : Formula ι} :
    FiniteLatticeCharacterization.ValidAtBottomAllFiniteJoinSemilattices phi ↔
      ∀ n val, HoldsInfSurj (fun k : Nat => k)
        (PropSubst.translate (Buttons.guardedLabelSubst n val) phi) := by
  rw [← FiniteLatticeCharacterization.validOnAllFiniteBooleanFrames_iff_validAtBottom]
  exact infsurj_formulaic_boolean_upper_bound_at_nat_root

/-- Final internal semantic form of the paper's `Grz.2` upper bound for `InfSets`:
the formulas true at the canonical `Nat` root under every guarded-label translation are
exactly the formulas in the semantic `Grz.2` theory. -/
theorem infsets_formulaic_grz2_upper_bound_at_nat_root
    {ι : Type u} {phi : Formula ι} :
    FormulaTheory.Grz2 phi ↔
      ∀ n val, HoldsInfAll (fun k : Nat => k)
        (PropSubst.translate (Buttons.guardedLabelSubst n val) phi) :=
  infsets_formulaic_boolean_upper_bound_at_nat_root

/-- Surjective analogue of `infsets_formulaic_grz2_upper_bound_at_nat_root`. -/
theorem infsurj_formulaic_grz2_upper_bound_at_nat_root
    {ι : Type u} {phi : Formula ι} :
    FormulaTheory.Grz2 phi ↔
      ∀ n val, HoldsInfSurj (fun k : Nat => k)
        (PropSubst.translate (Buttons.guardedLabelSubst n val) phi) :=
  infsurj_formulaic_boolean_upper_bound_at_nat_root

/-- Equivalent finite-semilattice presentation of
`infsets_formulaic_grz2_upper_bound_at_nat_root`. -/
theorem infsets_formulaic_grz2_finiteJoinSemilattice_at_nat_root
    {ι : Type u} {phi : Formula ι} :
    FormulaTheory.Grz2FiniteJoinSemilattice phi ↔
      ∀ n val, HoldsInfAll (fun k : Nat => k)
        (PropSubst.translate (Buttons.guardedLabelSubst n val) phi) := by
  rw [← FormulaTheory.grz2_iff_validAtBottomAllFiniteJoinSemilattices]
  exact infsets_formulaic_grz2_upper_bound_at_nat_root

/-- Surjective analogue of `infsets_formulaic_grz2_finiteJoinSemilattice_at_nat_root`. -/
theorem infsurj_formulaic_grz2_finiteJoinSemilattice_at_nat_root
    {ι : Type u} {phi : Formula ι} :
    FormulaTheory.Grz2FiniteJoinSemilattice phi ↔
      ∀ n val, HoldsInfSurj (fun k : Nat => k)
        (PropSubst.translate (Buttons.guardedLabelSubst n val) phi) := by
  rw [← FormulaTheory.grz2_iff_validAtBottomAllFiniteJoinSemilattices]
  exact infsurj_formulaic_grz2_upper_bound_at_nat_root

end HeytingLean.ModalCategorySets.Validities
