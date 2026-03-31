import HeytingLean.ModalCategorySets.Basic

namespace HeytingLean.Tests.ModalCategorySets

open HeytingLean.ModalCategorySets.Propositional
open HeytingLean.ModalCategorySets.Framework
open HeytingLean.ModalCategorySets.Framework.Equality
open HeytingLean.ModalCategorySets.Validities

def unitNonemptyWorld : HeytingLean.ModalCategorySets.Framework.NonemptyType where
  carrier := PUnit
  property := ⟨PUnit.unit⟩

def natValuation : Equality.Valuation Nat := fun n => n

def sententialSubst : Bool → EqAssertion
  | true => EqAssertion.top
  | false => EqAssertion.falsum

private theorem realizedPartition_natValuation_two :
    realizedPartition natValuation 2 = discretePartition 2 := by
  ext i j
  fin_cases i <;> fin_cases j
  · change natValuation 0 = natValuation 0 ↔ ((0 : Fin 2) = 0)
    simp [natValuation]
  · change natValuation 0 = natValuation 1 ↔ ((0 : Fin 2) = 1)
    simp [natValuation]
  · change natValuation 1 = natValuation 0 ↔ ((1 : Fin 2) = 0)
    simp [natValuation]
  · change natValuation 1 = natValuation 1 ↔ ((1 : Fin 2) = 1)
    simp [natValuation]

example {α : Type} (p q : α) :
    (allFunctions.toKripkeCategory.toFrame).Valid (axiomK p q) :=
  axiomK_valid _ _ _

example :
    ValidatesS4 (surjections.toKripkeCategory.toFrame) :=
  s4_valid_in_kripke_category _

example {α : Type} (p : α) :
    identityFrame.Valid (axiomTriv p) :=
  axiomTriv_valid_on_identityFrame p

example {α : Type} (p : α) :
    identityFrame.ValidAt PUnit (axiomGrz p) := by
  have hRefl : Reflexive identityFrame := by
    intro w
    exact (identityFrame_isIdentityRelation w w).2 rfl
  have hTrans : Transitive identityFrame := by
    intro u v w huv hvw
    have huvEq : u = v := (identityFrame_isIdentityRelation u v).1 huv
    have hvwEq : v = w := (identityFrame_isIdentityRelation v w).1 hvw
    exact (identityFrame_isIdentityRelation u w).2 (huvEq.trans hvwEq)
  have hIso : IsolatedAt identityFrame PUnit := by
    intro v
    constructor
    · intro h
      exact (identityFrame_isIdentityRelation PUnit v).1 h |> Eq.symm
    · intro h
      exact (identityFrame_isIdentityRelation PUnit v).2 h.symm
  exact axiomGrz_validAt_of_coneControlled
    (F := identityFrame)
    (w := PUnit)
    hRefl
    hTrans
    p
    (fun val => coneControlled_of_isolatedAt hIso val (.var p))

example {α : Type} (p : α) :
    OrderedFrames.orderFrame (Fin 3) |>.Valid (axiomGrz p) :=
  OrderedFrames.axiomGrz_valid_on_finite_partialOrder (W := Fin 3) p

example :
    ValidatesGrzDot2Core (partitionFrame 3) :=
  partitionFrame_validatesGrzDot2Core 3

example :
    ValidatesS4Dot2 (prepartitionFrame 2 3) :=
  prepartitionFrame_validatesS4Dot2 2 3

example :
    ValidatesS5 (bijections.toKripkeCategory.toFrame) :=
  s5_valid_on_bijections

example :
    ModalTheory.Validates identityCategory.toFrame .Triv :=
  identityCategory_validate_Triv

example :
    ModalTheory.ValidatesAt nonemptyFunctionsCategory.toFrame unitNonemptyWorld .S5 :=
  nonemptyFunctions_validateAt_S5 unitNonemptyWorld

example {Obj : Type} (S : AssertionSemantics Obj) :
    S.TruthInvariant ↔ S.PossibleTrivializes ∧ S.NecessaryTrivializes :=
  S.truthInvariant_iff_modalitiesTrivialize

example :
    HoldsInfAll natValuation (partitionFormulaOf (discretePartition 2)) := by
  exact (holdsInfAll_partitionFormulaOf_iff_realizedPartition
    (ρ := natValuation)
    (P := discretePartition 2)).mpr realizedPartition_natValuation_two

example :
    HoldsInfAll natValuation (infPartitionElimAll Nat 2 (Equality.EqAssertion.neg (.atomEq 0 1))) ↔
      HoldsInfAll natValuation (Equality.EqAssertion.neg (.atomEq 0 1)) := by
  have hUses : Equality.UsesOnlyLT 2 (Equality.EqAssertion.neg (.atomEq 0 1)) := by
    exact And.intro (And.intro (by decide) (by decide)) trivial
  simpa using
    (holdsInfAll_infPartitionElim_iff
      (ρ := natValuation)
      (n := 2)
      (φ := Equality.EqAssertion.neg (.atomEq 0 1))
      hUses)

example :
    HoldsInfSurj natValuation (infPartitionElimSurj Nat 2 (Equality.EqAssertion.neg (.atomEq 0 1))) ↔
      HoldsInfSurj natValuation (Equality.EqAssertion.neg (.atomEq 0 1)) := by
  have hUses : Equality.UsesOnlyLT 2 (Equality.EqAssertion.neg (.atomEq 0 1)) := by
    exact And.intro (And.intro (by decide) (by decide)) trivial
  simpa using
    (holdsInfSurj_infPartitionElim_iff
      (ρ := natValuation)
      (n := 2)
      (φ := Equality.EqAssertion.neg (.atomEq 0 1))
      hUses)

example :
    HoldsInfAll natValuation (Equality.EqAssertion.neg (.atomEq 0 1)) ↔
      HoldsInfAll natValuation
        (Equality.disjList ((infSatisfyingPartitionsAll Nat 2 (Equality.EqAssertion.neg (.atomEq 0 1))).map partitionFormulaOf)) := by
  have hUses : Equality.UsesOnlyLT 2 (Equality.EqAssertion.neg (.atomEq 0 1)) := by
    exact And.intro (And.intro (by decide) (by decide)) trivial
  simpa using infsets_formulas_partition_normal_form (ρ := natValuation) hUses

example :
    HoldsInfAll (fun _ => (0 : Nat)) Equality.EqAssertion.top ↔
      HoldsInfAll (fun _ => (1 : Nat)) Equality.EqAssertion.top := by
  have hUsesTop : Equality.UsesOnlyLT 0 Equality.EqAssertion.top := by
    trivial
  simpa using
    (infsets_sentences_truth_invariant
      (ρ := fun _ => (0 : Nat))
      (σ := fun _ => (1 : Nat))
      (φ := Equality.EqAssertion.top)
      hUsesTop)

example :
    HoldsInfSurj (fun _ => (0 : Nat)) Equality.EqAssertion.top ↔
      HoldsInfSurj (fun _ => (1 : Nat)) Equality.EqAssertion.top := by
  have hUsesTop : Equality.UsesOnlyLT 0 Equality.EqAssertion.top := by
    trivial
  simpa using
    (infsurj_sentences_truth_invariant
      (ρ := fun _ => (0 : Nat))
      (σ := fun _ => (1 : Nat))
      (φ := Equality.EqAssertion.top)
      hUsesTop)

example :
    PropSubst.IsSentential sententialSubst := by
  intro b
  cases b <;> trivial

example :
    HoldsInfAll (fun _ => (0 : Nat))
      (PropSubst.translate sententialSubst (axiomTriv true)) := by
  exact infsets_sentential_triv_instance
    (ρ := fun _ => (0 : Nat))
    (τ := sententialSubst)
    (by intro b; cases b <;> trivial)
    true

example :
    HoldsInfSurj (fun _ => (0 : Nat))
      (PropSubst.translate sententialSubst (axiomTriv true)) := by
  exact infsurj_sentential_triv_instance
    (ρ := fun _ => (0 : Nat))
    (τ := sententialSubst)
    (by intro b; cases b <;> trivial)
    true

example :
    HoldsInfAll (fun _ => (0 : Nat))
      (PropSubst.translate sententialSubst (.dia (.var true))) ↔
      HoldsInfAll (fun _ => (1 : Nat))
        (PropSubst.translate sententialSubst (.dia (.var true))) := by
  exact infsets_sentential_substitution_truth_invariant
    (ρ := fun _ => (0 : Nat))
    (σ := fun _ => (1 : Nat))
    (τ := sententialSubst)
    (φ := .dia (.var true))
    (by intro b; cases b <;> trivial)

example :
    HoldsInfAll (fun _ => (0 : Nat))
      (PropSubst.translate sententialSubst (axiomDot2 true)) := by
  exact infsets_formulaic_dot2_instance
    (ρ := fun _ => (0 : Nat))
    (n := 0)
    (τ := sententialSubst)
    (p := true)
    (by intro b; cases b <;> trivial)

example :
    HoldsInfSurj (fun _ => (0 : Nat))
      (PropSubst.translate sententialSubst (axiomDot2 true)) := by
  exact infsurj_formulaic_dot2_instance
    (ρ := fun _ => (0 : Nat))
    (n := 0)
    (τ := sententialSubst)
    (p := true)
    (by intro b; cases b <;> trivial)

example :
    Nonempty (Buttons.AllButtonPatternWitness
      (ρ := fun k : Nat => k)
      (s := (∅ : Finset (Fin 2)))) :=
  Buttons.nat_admits_allFunctions_button_pattern (n := 2) ∅

example :
    Buttons.ButtonPatternAll
      (σ := Buttons.crossCoupledNatValuation)
      (n := 2)
      (∅ : Finset (Fin 2)) :=
  Buttons.crossCoupledNat_pattern_empty_all

example :
    ¬ Nonempty (Buttons.AllButtonPatternWitness
      (ρ := Buttons.crossCoupledNatValuation)
      (s := ({Buttons.buttonZero} : Finset (Fin 2)))) :=
  Buttons.crossCoupledNat_no_singleton_zero_extension_all

example :
    ¬ Nonempty (Buttons.SurjButtonPatternWitness
      (ρ := Buttons.crossCoupledNatValuation)
      (s := ({Buttons.buttonZero} : Finset (Fin 2)))) :=
  Buttons.crossCoupledNat_no_singleton_zero_extension_surj

example :
    Nonempty (Buttons.SurjButtonPatternWitness
      (ρ := fun k : Nat => k)
      (s := ({(0 : Fin 1)} : Finset (Fin 1)))) :=
  Buttons.nat_admits_surjections_button_pattern ({(0 : Fin 1)} : Finset (Fin 1))

example :
    Nonempty (Buttons.AllGuardedButtonPatternWitness
      (ρ := fun k : Nat => k)
      (s := ({(0 : Fin 1)} : Finset (Fin 1)))) :=
  Buttons.nat_admits_allFunctions_guardedButton_pattern ({(0 : Fin 1)} : Finset (Fin 1))

example :
    Nonempty (Buttons.SurjGuardedButtonPatternWitness
      (ρ := fun k : Nat => k)
      (s := ({(0 : Fin 1)} : Finset (Fin 1)))) :=
  Buttons.nat_admits_surjections_guardedButton_pattern ({(0 : Fin 1)} : Finset (Fin 1))

example :
    ¬ HoldsInfAll (fun k : Nat => k) (Buttons.guardedButton (0 : Fin 1)) :=
  Buttons.allFunctions_guardedButton_unpushed_at_root
    (ρ := fun k : Nat => k)
    (hInj := by
      intro i j h
      exact Fin.ext h)
    (i := (0 : Fin 1))

example :
    ¬ HoldsInfSurj (fun k : Nat => k) (Buttons.guardedButton (0 : Fin 1)) :=
  Buttons.surjections_guardedButton_unpushed_at_root
    (ρ := fun k : Nat => k)
    (hInj := by
      intro i j h
      exact Fin.ext h)
    (i := (0 : Fin 1))

example :
    HoldsInfAll (fun k : Nat => k) (.diaQ (.boxQ (Buttons.guardedButton (0 : Fin 1)))) :=
  Buttons.nat_guardedButton_is_button_all (0 : Fin 1)

example :
    HoldsInfSurj (fun k : Nat => k) (.diaQ (.boxQ (Buttons.guardedButton (0 : Fin 1)))) :=
  Buttons.nat_guardedButton_is_button_surj (0 : Fin 1)

example :
    HoldsInfAll (fun _ => (0 : Nat))
      (PropSubst.translate sententialSubst (axiomGrz true)) := by
  exact infsets_formulaic_grz_instance
    (ρ := fun _ => (0 : Nat))
    (n := 0)
    (τ := sententialSubst)
    (p := true)
    (by intro b; cases b <;> trivial)

example :
    HoldsInfSurj (fun _ => (0 : Nat))
      (PropSubst.translate sententialSubst (axiomGrz true)) := by
  exact infsurj_formulaic_grz_instance
    (ρ := fun _ => (0 : Nat))
    (n := 0)
    (τ := sententialSubst)
    (p := true)
    (by intro b; cases b <;> trivial)

example :
    HoldsInfAll (fun _ => (0 : Nat)) (PropSubst.translate sententialSubst (axiomT true)) ∧
      HoldsInfAll (fun _ => (0 : Nat)) (PropSubst.translate sententialSubst (axiom4 true)) ∧
        HoldsInfAll (fun _ => (0 : Nat)) (PropSubst.translate sententialSubst (axiomDot2 true)) := by
  exact infsets_formulaic_s4Dot2_package
    (ρ := fun _ => (0 : Nat))
    (n := 0)
    (τ := sententialSubst)
    true
    (by intro b; cases b <;> trivial)

example :
    HoldsInfSurj (fun _ => (0 : Nat)) (PropSubst.translate sententialSubst (axiomT true)) ∧
      HoldsInfSurj (fun _ => (0 : Nat)) (PropSubst.translate sententialSubst (axiom4 true)) ∧
        HoldsInfSurj (fun _ => (0 : Nat)) (PropSubst.translate sententialSubst (axiomDot2 true)) := by
  exact infsurj_formulaic_s4Dot2_package
    (ρ := fun _ => (0 : Nat))
    (n := 0)
    (τ := sententialSubst)
    true
    (by intro b; cases b <;> trivial)

example :
    HoldsInfAll (fun _ => (0 : Nat)) (PropSubst.translate sententialSubst (axiomT true)) ∧
      HoldsInfAll (fun _ => (0 : Nat)) (PropSubst.translate sententialSubst (axiom4 true)) ∧
        HoldsInfAll (fun _ => (0 : Nat)) (PropSubst.translate sententialSubst (axiomDot2 true)) ∧
          HoldsInfAll (fun _ => (0 : Nat)) (PropSubst.translate sententialSubst (axiomGrz true)) := by
  exact infsets_formulaic_grzDot2Core_package
    (ρ := fun _ => (0 : Nat))
    (n := 0)
    (τ := sententialSubst)
    true
    (by intro b; cases b <;> trivial)

example :
    HoldsInfSurj (fun _ => (0 : Nat)) (PropSubst.translate sententialSubst (axiomT true)) ∧
      HoldsInfSurj (fun _ => (0 : Nat)) (PropSubst.translate sententialSubst (axiom4 true)) ∧
        HoldsInfSurj (fun _ => (0 : Nat)) (PropSubst.translate sententialSubst (axiomDot2 true)) ∧
          HoldsInfSurj (fun _ => (0 : Nat)) (PropSubst.translate sententialSubst (axiomGrz true)) := by
  exact infsurj_formulaic_grzDot2Core_package
    (ρ := fun _ => (0 : Nat))
    (n := 0)
    (τ := sententialSubst)
    true
    (by intro b; cases b <;> trivial)

end HeytingLean.Tests.ModalCategorySets
