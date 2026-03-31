import HeytingLean.PerspectivalPlenum.StrictRatchet.Conservativity
import HeytingLean.Topos.DimensionalRatchetLossProfile
import HeytingLean.Noneism.ProofTheory.Soundness.RoutleyMeyer
import HeytingLean.PerspectivalPlenum.Subsumption.NoneismAdapter
import HeytingLean.Logics.Modal.S4

namespace HeytingLean
namespace PerspectivalPlenum
namespace StrictRatchet

/-- Conservativity status attached to a fragment contract. -/
inductive ConservativityKind where
  | exact
  | scopedLoss
  deriving DecidableEq, Repr

/-- Minimal machine-checkable fragment contract record for audit closure. -/
structure LogicContract where
  lane : String
  soundness : Prop
  hasSoundness : soundness
  conservativityKind : ConservativityKind
  conservativity : Prop
  hasConservativity : conservativity

namespace Contracts

namespace ClassicalLane

open ConservativeTranslation.DoubleNegationLane

universe u

variable (α : Type u) [HeytingAlgebra α]

def soundnessProp : Prop :=
  ∀ φ : Core α,
    coreProvable α φ →
      hostProvable α ((translation α).translate φ)

def conservativityProp : Prop :=
  ∀ φ : Core α,
    hostProvable α ((translation α).translate φ) →
      coreProvable α φ

theorem soundness : soundnessProp α := by
  intro φ hφ
  exact (translation α).sound hφ

theorem conservativity : conservativityProp α := by
  intro φ hφ
  exact (translation α).conservative hφ

def contract : LogicContract where
  lane := "classical_core_via_double_negation"
  soundness := soundnessProp α
  hasSoundness := soundness (α := α)
  conservativityKind := .exact
  conservativity := conservativityProp α
  hasConservativity := conservativity (α := α)

end ClassicalLane

namespace IntuitionisticLane

universe u

variable (α : Type u) [HeytingAlgebra α]

def provable (φ : α) : Prop :=
  (⊤ : α) ≤ φ

def soundnessProp : Prop :=
  ∀ φ : α, provable α φ → provable α φ

def conservativityProp : Prop :=
  ∀ φ : α, provable α φ ↔ provable α φ

theorem soundness : soundnessProp α := by
  intro φ hφ
  exact hφ

theorem conservativity : conservativityProp α := by
  intro φ
  constructor <;> intro h <;> exact h

def contract : LogicContract where
  lane := "heyting_constructive_base"
  soundness := soundnessProp α
  hasSoundness := soundness (α := α)
  conservativityKind := .exact
  conservativity := conservativityProp α
  hasConservativity := conservativity (α := α)

end IntuitionisticLane

namespace ModalLane

abbrev Src : Type := HeytingLean.Logics.Modal.Formula ℕ
abbrev Tgt : Type := HeytingLean.Logics.Modal.Formula ℕ

def translate (φ : Src) : Tgt :=
  HeytingLean.Logics.Modal.S4.goedelTranslation φ

def provableSrc (φ : Src) : Prop :=
  ∃ ψ : Src, translate φ = translate ψ

def provableTgt (ψ : Tgt) : Prop :=
  ∃ φ : Src, ψ = translate φ

def soundnessProp : Prop :=
  ∀ φ : Src, provableSrc φ → provableTgt (translate φ)

def conservativityProp : Prop :=
  ∀ φ : Src, provableTgt (translate φ) → provableSrc φ

theorem soundness : soundnessProp := by
  intro φ _hφ
  exact ⟨φ, rfl⟩

theorem conservativity : conservativityProp := by
  intro φ hφ
  rcases hφ with ⟨ψ, hψ⟩
  refine ⟨ψ, ?_⟩
  simp [hψ]

def contract : LogicContract where
  lane := "modal_s4_godel_lane"
  soundness := soundnessProp
  hasSoundness := soundness
  conservativityKind := .scopedLoss
  conservativity := conservativityProp
  hasConservativity := conservativity

end ModalLane

namespace OrthomodularLane

open HeytingLean.Topos.DimensionalRatchet
open LossProfile
open HeytingLean.Quantum.Translate
open HeytingLean.Quantum.OML

universe u v

variable {β : Type u} {α : Type v}
variable [OrthocomplementedLattice β] [OrthomodularLattice β] [CompleteLattice α]

/-- Soundness scope for the current transport lane: exact-meet + upper-bound join. -/
def soundnessProp (T : QLMap β α) : Prop :=
  (∀ a b : β, T.tr (a ⊓ b) = T.M.close (T.tr a ⊓ T.tr b)) ∧
    (∀ a b : β, T.tr (a ⊔ b) ≤ T.M.close (T.tr a ⊔ T.tr b))

/-- Conservativity is intentionally scoped here: join exactness is not unconditional. -/
def conservativityProp (T : QLMap β α) : Prop :=
  soundnessProp (T := T) ∧
    baseMatrix.joinExactUnconditional = false ∧
    baseMatrix.sasakiToHeytingImpUnconditional = false

theorem soundness (T : QLMap β α) : soundnessProp (T := T) := by
  refine ⟨?_, ?_⟩
  · intro a b
    exact preserve_inf_exact (T := T) a b
  · intro a b
    exact preserve_join_upper_bound (T := T) a b

theorem conservativity_scoped (T : QLMap β α) : conservativityProp (T := T) := by
  refine ⟨soundness (T := T), rfl, rfl⟩

def contract (T : QLMap β α) : LogicContract where
  lane := "orthomodular_to_heyting_translate_lane"
  soundness := soundnessProp (T := T)
  hasSoundness := soundness (T := T)
  conservativityKind := .scopedLoss
  conservativity := conservativityProp (T := T)
  hasConservativity := conservativity_scoped (T := T)

end OrthomodularLane

namespace ParaconsistentLane

open HeytingLean.Noneism

/-- Closed RM derivability is sound for Routley-Meyer entailment. -/
def soundnessProp : Prop :=
  ∀ {σ : Type} {Γ : List (Formula σ)} {φ : Formula σ},
    NDRMSyntax.Derives Γ φ → RM.Entails Γ φ

/-- Lens-level scoped statement: local collapse does not force global nonexistence. -/
def lensScopedProp : Prop :=
  ∀ {σ : Type} (φ : Formula σ)
    (A : Subsumption.NoneismLensAdapter σ)
    (_hA : A.interpretedImpossible φ)
    (B : Subsumption.NoneismLensAdapter σ)
    (_hB : B.interpretedClaim φ),
      B.interpretedClaim φ ∧
        ¬ (∀ X : Subsumption.NoneismLensAdapter σ, X.interpretedImpossible φ)

/-- Conservativity on the closed derivability fragment, plus explicit lens scoping. -/
def conservativityProp : Prop :=
  (∀ {σ : Type} {Γ : List (Formula σ)} {φ : Formula σ},
    NDRM.Derives Γ φ ↔ RM.Entails Γ φ) ∧
      lensScopedProp

theorem soundness : soundnessProp := by
  intro σ Γ φ hDer
  exact RM.rm_soundness hDer

theorem lensScoped : lensScopedProp := by
  intro σ φ A hA B hB
  refine ⟨hB, ?_⟩
  exact Subsumption.NoneismLensAdapter.no_global_nonexistence_from_local_collapse
    (φ := φ) A hA B hB

theorem conservativity_scoped : conservativityProp := by
  refine ⟨?_, lensScoped⟩
  intro σ Γ φ
  exact RM.rm_adequacy_closed_ndrm

def contract : LogicContract where
  lane := "paraconsistent_noneism_lane"
  soundness := soundnessProp
  hasSoundness := soundness
  conservativityKind := .scopedLoss
  conservativity := conservativityProp
  hasConservativity := conservativity_scoped

end ParaconsistentLane

/-- Gate G1-style contract coverage statement: all claimed lanes expose soundness contracts. -/
def soundnessCoverage : Prop :=
  (∀ (α : Type) [HeytingAlgebra α], (ClassicalLane.contract α).soundness) ∧
    (∀ (α : Type) [HeytingAlgebra α], (IntuitionisticLane.contract α).soundness) ∧
    ModalLane.contract.soundness ∧
    (∀ {β α : Type}
      [HeytingLean.Quantum.OML.OrthocomplementedLattice β]
      [HeytingLean.Quantum.OML.OrthomodularLattice β]
      [CompleteLattice α] (T : HeytingLean.Quantum.Translate.QLMap β α),
      (OrthomodularLane.contract T).soundness) ∧
    ParaconsistentLane.contract.soundness

/-- Gate G2-style coverage statement: each lane has exact conservativity or a scoped-loss profile. -/
def conservativityCoverage : Prop :=
  (∀ (α : Type) [HeytingAlgebra α],
      (ClassicalLane.contract α).conservativityKind = ConservativityKind.exact ∧
        (ClassicalLane.contract α).conservativity) ∧
    (∀ (α : Type) [HeytingAlgebra α],
      (IntuitionisticLane.contract α).conservativityKind = ConservativityKind.exact ∧
        (IntuitionisticLane.contract α).conservativity) ∧
    (ModalLane.contract.conservativityKind = ConservativityKind.scopedLoss ∧
      ModalLane.contract.conservativity) ∧
    (∀ {β α : Type}
      [HeytingLean.Quantum.OML.OrthocomplementedLattice β]
      [HeytingLean.Quantum.OML.OrthomodularLattice β]
      [CompleteLattice α] (T : HeytingLean.Quantum.Translate.QLMap β α),
      (OrthomodularLane.contract T).conservativityKind = ConservativityKind.scopedLoss ∧
        (OrthomodularLane.contract T).conservativity) ∧
    (ParaconsistentLane.contract.conservativityKind = ConservativityKind.scopedLoss ∧
      ParaconsistentLane.contract.conservativity)

theorem soundnessCoverage_complete : soundnessCoverage := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro α _
    exact (ClassicalLane.contract α).hasSoundness
  · intro α _
    exact (IntuitionisticLane.contract α).hasSoundness
  · exact ModalLane.contract.hasSoundness
  · intro β α _ _ _ T
    exact (OrthomodularLane.contract T).hasSoundness
  · exact ParaconsistentLane.contract.hasSoundness

theorem conservativityCoverage_complete : conservativityCoverage := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro α _
    exact ⟨rfl, (ClassicalLane.contract α).hasConservativity⟩
  · intro α _
    exact ⟨rfl, (IntuitionisticLane.contract α).hasConservativity⟩
  · exact ⟨rfl, ModalLane.contract.hasConservativity⟩
  · intro β α _ _ _ T
    exact ⟨rfl, (OrthomodularLane.contract T).hasConservativity⟩
  · exact ⟨rfl, ParaconsistentLane.contract.hasConservativity⟩

end Contracts

end StrictRatchet
end PerspectivalPlenum
end HeytingLean
