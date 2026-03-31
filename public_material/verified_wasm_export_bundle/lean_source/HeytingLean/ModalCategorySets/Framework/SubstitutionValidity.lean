import HeytingLean.ModalCategorySets.Framework.InfinitePartitionElimination
import HeytingLean.ModalCategorySets.Propositional.Axioms

namespace HeytingLean.ModalCategorySets.Framework

open HeytingLean.ModalCategorySets.Propositional
open HeytingLean.ModalCategorySets.Framework.Equality

universe u v

namespace PropSubst

/-- Translate a propositional modal formula to the equality-modal language by
substituting an equality assertion for each propositional variable. -/
def translate {ι : Type v} (tau : ι → EqAssertion) : Formula ι → EqAssertion
  | .var p => tau p
  | .bot => .falsum
  | .imp phi psi => .impl (translate tau phi) (translate tau psi)
  | .conj phi psi => .conj (translate tau phi) (translate tau psi)
  | .disj phi psi => .disj (translate tau phi) (translate tau psi)
  | .box phi => .boxQ (translate tau phi)
  | .dia phi => .diaQ (translate tau phi)

/-- Sentential substitutions are substitutions by closed equality assertions. -/
def IsSentential {ι : Type v} (tau : ι → EqAssertion) : Prop :=
  ∀ p, Equality.UsesOnlyLT 0 (tau p)

/-- Finite-window substitutions only mention variables below `n`. -/
def UsesOnlyLT {ι : Type v} (n : Nat) (tau : ι → EqAssertion) : Prop :=
  ∀ p, Equality.UsesOnlyLT n (tau p)

theorem translate_usesOnlyLT {ι : Type v} {n : Nat} {tau : ι → EqAssertion} {phi : Formula ι}
    (hTau : UsesOnlyLT n tau) :
    Equality.UsesOnlyLT n (translate tau phi) := by
  induction phi with
  | var p =>
      exact hTau p
  | bot =>
      trivial
  | imp phi psi ihPhi ihPsi =>
      exact And.intro ihPhi ihPsi
  | conj phi psi ihPhi ihPsi =>
      exact And.intro ihPhi ihPsi
  | disj phi psi ihPhi ihPsi =>
      exact And.intro ihPhi ihPsi
  | box phi ih =>
      exact ih
  | dia phi ih =>
      exact ih

abbrev HoldsInfAllSubst {ι : Type v} {alpha : Type u} [Infinite alpha]
    (rho : Valuation alpha) (tau : ι → EqAssertion) (phi : Formula ι) : Prop :=
  HoldsInfAll rho (translate tau phi)

abbrev HoldsInfSurjSubst {ι : Type v} {alpha : Type u} [Infinite alpha]
    (rho : Valuation alpha) (tau : ι → EqAssertion) (phi : Formula ι) : Prop :=
  HoldsInfSurj rho (translate tau phi)

theorem holdsInfAll_translate_sentential_irrel {ι : Type v} {alpha beta : Type u}
    [Infinite alpha] [Infinite beta] (rho : Valuation alpha) (sigma : Valuation beta)
    {tau : ι → EqAssertion} {phi : Formula ι}
    (hTau : IsSentential tau) :
    HoldsInfAllSubst rho tau phi ↔ HoldsInfAllSubst sigma tau phi :=
  holdsInfAll_sentence_irrel rho sigma (translate_usesOnlyLT (n := 0) hTau)

theorem holdsInfSurj_translate_sentential_irrel {ι : Type v} {alpha beta : Type u}
    [Infinite alpha] [Infinite beta] (rho : Valuation alpha) (sigma : Valuation beta)
    {tau : ι → EqAssertion} {phi : Formula ι}
    (hTau : IsSentential tau) :
    HoldsInfSurjSubst rho tau phi ↔ HoldsInfSurjSubst sigma tau phi :=
  holdsInfSurj_sentence_irrel rho sigma (translate_usesOnlyLT (n := 0) hTau)

theorem holdsInfAll_box_sentential_iff {alpha : Type u} [Infinite alpha]
    (rho : Valuation alpha) {phi : EqAssertion}
    (hSent : Equality.UsesOnlyLT 0 phi) :
    HoldsInfAll rho (EqAssertion.boxQ phi) ↔ HoldsInfAll rho phi := by
  constructor
  · intro hBox
    exact hBox alpha (show Infinite alpha from inferInstance) id trivial
  · intro hPhi beta hBeta f hf
    exact (holdsInfAll_sentence_irrel rho (fun x => f (rho x)) (φ := phi) hSent).mp hPhi

theorem holdsInfSurj_box_sentential_iff {alpha : Type u} [Infinite alpha]
    (rho : Valuation alpha) {phi : EqAssertion}
    (hSent : Equality.UsesOnlyLT 0 phi) :
    HoldsInfSurj rho (EqAssertion.boxQ phi) ↔ HoldsInfSurj rho phi := by
  constructor
  · intro hBox
    exact hBox alpha (show Infinite alpha from inferInstance) id Function.surjective_id
  · intro hPhi beta hBeta f hf
    exact (holdsInfSurj_sentence_irrel rho (fun x => f (rho x)) (φ := phi) hSent).mp hPhi

theorem holdsInfAll_dia_sentential_iff {alpha : Type u} [Infinite alpha]
    (rho : Valuation alpha) {phi : EqAssertion}
    (hSent : Equality.UsesOnlyLT 0 phi) :
    HoldsInfAll rho (EqAssertion.diaQ phi) ↔ HoldsInfAll rho phi := by
  constructor
  · rintro ⟨beta, hBeta, f, hf, hPhi⟩
    exact (holdsInfAll_sentence_irrel rho (fun x => f (rho x)) (φ := phi) hSent).mpr hPhi
  · intro hPhi
    refine Exists.intro alpha ?_
    refine Exists.intro (show Infinite alpha from inferInstance) ?_
    refine Exists.intro id ?_
    exact And.intro trivial hPhi

theorem holdsInfSurj_dia_sentential_iff {alpha : Type u} [Infinite alpha]
    (rho : Valuation alpha) {phi : EqAssertion}
    (hSent : Equality.UsesOnlyLT 0 phi) :
    HoldsInfSurj rho (EqAssertion.diaQ phi) ↔ HoldsInfSurj rho phi := by
  constructor
  · rintro ⟨beta, hBeta, f, hf, hPhi⟩
    exact (holdsInfSurj_sentence_irrel rho (fun x => f (rho x)) (φ := phi) hSent).mpr hPhi
  · intro hPhi
    refine Exists.intro alpha ?_
    refine Exists.intro (show Infinite alpha from inferInstance) ?_
    refine Exists.intro id ?_
    exact And.intro Function.surjective_id hPhi

theorem holdsInfAll_translate_axiomTriv_of_sentential {ι : Type v} {alpha : Type u}
    [Infinite alpha] (rho : Valuation alpha) {tau : ι → EqAssertion}
    (hTau : IsSentential tau) (p : ι) :
    HoldsInfAll rho (translate tau (axiomTriv p)) := by
  change HoldsInfAll rho
    (EqAssertion.conj
      (EqAssertion.impl (tau p) (EqAssertion.boxQ (tau p)))
      (EqAssertion.impl (EqAssertion.boxQ (tau p)) (tau p)))
  refine And.intro ?_ ?_
  · intro hPhi
    exact (holdsInfAll_box_sentential_iff (rho := rho) (phi := tau p) (hSent := hTau p)).2 hPhi
  · intro hBox
    exact (holdsInfAll_box_sentential_iff (rho := rho) (phi := tau p) (hSent := hTau p)).1 hBox

theorem holdsInfSurj_translate_axiomTriv_of_sentential {ι : Type v} {alpha : Type u}
    [Infinite alpha] (rho : Valuation alpha) {tau : ι → EqAssertion}
    (hTau : IsSentential tau) (p : ι) :
    HoldsInfSurj rho (translate tau (axiomTriv p)) := by
  change HoldsInfSurj rho
    (EqAssertion.conj
      (EqAssertion.impl (tau p) (EqAssertion.boxQ (tau p)))
      (EqAssertion.impl (EqAssertion.boxQ (tau p)) (tau p)))
  refine And.intro ?_ ?_
  · intro hPhi
    exact (holdsInfSurj_box_sentential_iff (rho := rho) (phi := tau p) (hSent := hTau p)).2 hPhi
  · intro hBox
    exact (holdsInfSurj_box_sentential_iff (rho := rho) (phi := tau p) (hSent := hTau p)).1 hBox

/-- The `.2` axiom holds in the infinite-only functions semantics for any equality
assertion whose free variables lie below `n`. -/
theorem holdsInfAll_axiomDot2_of_usesOnlyLT {alpha : Type u} [Infinite alpha]
    (rho : Valuation alpha) {n : Nat} {phi : EqAssertion}
    (hUses : Equality.UsesOnlyLT n phi) :
    HoldsInfAll rho
      (EqAssertion.impl (EqAssertion.diaQ (EqAssertion.boxQ phi))
        (EqAssertion.boxQ (EqAssertion.diaQ phi))) := by
  intro hDiaBox gamma hGamma g hg
  rcases hDiaBox with ⟨beta, hBeta, f, hf, hBox⟩
  let q : FinPartition n := indiscretePartition n
  let rhoBeta : Valuation beta := fun i => f (rho i)
  let rhoGamma : Valuation gamma := fun i => g (rho i)
  have hRefBeta : Refines (realizedPartition rhoBeta n) q :=
    refines_indiscretePartition (realizedPartition rhoBeta n)
  have hRefGamma : Refines (realizedPartition rhoGamma n) q :=
    refines_indiscretePartition (realizedPartition rhoGamma n)
  let kBeta : beta → ULift (InfinitePartitionWitnessWorld q) :=
    fun a => ULift.up (allFunctionsInfiniteCoarseningMap rhoBeta hRefBeta a)
  let kGamma : gamma → ULift (InfinitePartitionWitnessWorld q) :=
    fun a => ULift.up (allFunctionsInfiniteCoarseningMap rhoGamma hRefGamma a)
  have hPhiBeta : HoldsInfAll (fun i => kBeta (rhoBeta i)) phi := by
    exact hBox (ULift (InfinitePartitionWitnessWorld q)) inferInstance kBeta trivial
  have hPartBeta : realizedPartition (fun i => kBeta (rhoBeta i)) n = q := by
    change realizedPartition
      (fun i => ULift.up (allFunctionsInfiniteCoarseningMap rhoBeta hRefBeta (rhoBeta i))) n = q
    rw [realizedPartition_ulift]
    exact realizedPartition_allFunctionsInfiniteCoarseningMap rhoBeta hRefBeta
  have hPartGamma : realizedPartition (fun i => kGamma (rhoGamma i)) n = q := by
    change realizedPartition
      (fun i => ULift.up (allFunctionsInfiniteCoarseningMap rhoGamma hRefGamma (rhoGamma i))) n = q
    rw [realizedPartition_ulift]
    exact realizedPartition_allFunctionsInfiniteCoarseningMap rhoGamma hRefGamma
  have hPhiGamma : HoldsInfAll (fun i => kGamma (rhoGamma i)) phi := by
    exact (holdsInfAll_of_realizedPartition_eq
      (n := n)
      (φ := phi)
      (ρ := fun i => kBeta (rhoBeta i))
      (σ := fun i => kGamma (rhoGamma i))
      hUses
      (hPartBeta.trans hPartGamma.symm)).1 hPhiBeta
  refine Exists.intro (ULift (InfinitePartitionWitnessWorld q)) ?_
  refine Exists.intro (inferInstance : Infinite (ULift (InfinitePartitionWitnessWorld q))) ?_
  refine Exists.intro kGamma ?_
  exact And.intro trivial hPhiGamma

/-- Finite-window propositional substitution instances of `.2` hold in the
infinite-only functions semantics. -/
theorem holdsInfAll_translate_axiomDot2_of_usesOnlyLT {ι : Type v} {alpha : Type u}
    [Infinite alpha] (rho : Valuation alpha) {n : Nat} {tau : ι → EqAssertion}
    (hTau : UsesOnlyLT n tau) (p : ι) :
    HoldsInfAll rho (translate tau (axiomDot2 p)) := by
  change HoldsInfAll rho
    (EqAssertion.impl (EqAssertion.diaQ (EqAssertion.boxQ (tau p)))
      (EqAssertion.boxQ (EqAssertion.diaQ (tau p))))
  exact holdsInfAll_axiomDot2_of_usesOnlyLT (rho := rho) (n := n) (phi := tau p) (hUses := hTau p)

/-- The `.2` axiom holds in the infinite-only surjection semantics for any equality
assertion whose free variables lie below `n`. -/
theorem holdsInfSurj_axiomDot2_of_usesOnlyLT {alpha : Type u} [Infinite alpha]
    (rho : Valuation alpha) {n : Nat} {phi : EqAssertion}
    (hUses : Equality.UsesOnlyLT n phi) :
    HoldsInfSurj rho
      (EqAssertion.impl (EqAssertion.diaQ (EqAssertion.boxQ phi))
        (EqAssertion.boxQ (EqAssertion.diaQ phi))) := by
  intro hDiaBox gamma hGamma g hg
  rcases hDiaBox with ⟨beta, hBeta, f, hf, hBox⟩
  let q : FinPartition n := indiscretePartition n
  let rhoBeta : Valuation beta := fun i => f (rho i)
  let rhoGamma : Valuation gamma := fun i => g (rho i)
  have hRefBeta : Refines (realizedPartition rhoBeta n) q :=
    refines_indiscretePartition (realizedPartition rhoBeta n)
  have hRefGamma : Refines (realizedPartition rhoGamma n) q :=
    refines_indiscretePartition (realizedPartition rhoGamma n)
  let kBeta : beta → InfiniteSurjCoarseningWorld rhoBeta q :=
    surjectionInfiniteCoarseningMap rhoBeta hRefBeta
  let kGamma : gamma → InfiniteSurjCoarseningWorld rhoGamma q :=
    surjectionInfiniteCoarseningMap rhoGamma hRefGamma
  have hPhiBeta : HoldsInfSurj (fun i => kBeta (rhoBeta i)) phi := by
    exact hBox (InfiniteSurjCoarseningWorld rhoBeta q) inferInstance kBeta
      (surjectionInfiniteCoarseningMap_surjective rhoBeta hRefBeta)
  have hPartBeta : realizedPartition (fun i => kBeta (rhoBeta i)) n = q := by
    exact realizedPartition_surjectionInfiniteCoarseningMap rhoBeta hRefBeta
  have hPartGamma : realizedPartition (fun i => kGamma (rhoGamma i)) n = q := by
    exact realizedPartition_surjectionInfiniteCoarseningMap rhoGamma hRefGamma
  have hPhiGamma : HoldsInfSurj (fun i => kGamma (rhoGamma i)) phi := by
    exact (holdsInfSurj_of_realizedPartition_eq
      (n := n)
      (φ := phi)
      (ρ := fun i => kBeta (rhoBeta i))
      (σ := fun i => kGamma (rhoGamma i))
      hUses
      (hPartBeta.trans hPartGamma.symm)).1 hPhiBeta
  refine Exists.intro (InfiniteSurjCoarseningWorld rhoGamma q) ?_
  refine Exists.intro inferInstance ?_
  refine Exists.intro kGamma ?_
  exact And.intro
    (surjectionInfiniteCoarseningMap_surjective rhoGamma hRefGamma)
    hPhiGamma

/-- Finite-window propositional substitution instances of `.2` hold in the
infinite-only surjection semantics. -/
theorem holdsInfSurj_translate_axiomDot2_of_usesOnlyLT {ι : Type v} {alpha : Type u}
    [Infinite alpha] (rho : Valuation alpha) {n : Nat} {tau : ι → EqAssertion}
    (hTau : UsesOnlyLT n tau) (p : ι) :
    HoldsInfSurj rho (translate tau (axiomDot2 p)) := by
  change HoldsInfSurj rho
    (EqAssertion.impl (EqAssertion.diaQ (EqAssertion.boxQ (tau p)))
      (EqAssertion.boxQ (EqAssertion.diaQ (tau p))))
  exact holdsInfSurj_axiomDot2_of_usesOnlyLT (rho := rho) (n := n) (phi := tau p) (hUses := hTau p)

end PropSubst

end HeytingLean.ModalCategorySets.Framework
