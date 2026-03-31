import HeytingLean.Noneism.Intentionality
import HeytingLean.PerspectivalPlenum.Lens.Collapse

namespace HeytingLean
namespace PerspectivalPlenum
namespace Subsumption

open Noneism

/--
Adapter that reinterprets noneist formulas through lens-relative satisfiability/collapse,
without altering the underlying noneist syntax/proof interfaces.
-/
structure NoneismLensAdapter (σ : Type) where
  lens : Lens.SemanticLens (Formula σ)

namespace NoneismLensAdapter

variable {σ : Type}

/-- Lens-relative reading of a noneist claim. -/
def interpretedClaim (A : NoneismLensAdapter σ) (φ : Formula σ) : Prop :=
  Lens.LocallySatisfiable A.lens φ

/-- Lens-relative reading of noneist impossibility. -/
def interpretedImpossible (A : NoneismLensAdapter σ) (φ : Formula σ) : Prop :=
  Lens.CollapseToBottom A.lens φ

/-- Lens-relative reading of object-level existence atom `E!(t)`. -/
def interpretedExistence (A : NoneismLensAdapter σ) (t : Term) : Prop :=
  interpretedClaim A (.eExists t)

/-- Reinterpret intentional-state witness requirement in a selected lens. -/
def requiresExistenceInLens (A : NoneismLensAdapter σ) (st : IntentionalState σ) : Prop :=
  interpretedExistence A st.object

@[simp] theorem interpretedImpossible_iff (A : NoneismLensAdapter σ) (φ : Formula σ) :
    interpretedImpossible A φ ↔ ¬ interpretedClaim A φ := Iff.rfl

@[simp] theorem interpretedExistence_def (A : NoneismLensAdapter σ) (t : Term) :
    interpretedExistence A t = Lens.LocallySatisfiable A.lens (.eExists t) := rfl

@[simp] theorem requiresExistence_formula
    (_A : NoneismLensAdapter σ) (st : IntentionalState σ) :
    st.requiresExistence = Formula.eExists st.object := rfl

/-- Local satisfiability in a lens prevents local collapse in that same lens. -/
theorem claim_not_impossible (A : NoneismLensAdapter σ) (φ : Formula σ)
    (h : interpretedClaim A φ) :
    ¬ interpretedImpossible A φ := by
  intro hImp
  exact hImp h

/-- A single local collapse does not force global nonexistence across all lenses. -/
theorem no_global_nonexistence_from_local_collapse
    (φ : Formula σ)
    (A : NoneismLensAdapter σ)
    (_hA : interpretedImpossible A φ)
    (B : NoneismLensAdapter σ)
    (hB : interpretedClaim B φ) :
    ¬ (∀ X : NoneismLensAdapter σ, interpretedImpossible X φ) := by
  intro hAll
  exact (hAll B) hB

/--
Compatibility theorem: if one strict lens marks a formula contradictory while another
permits contradictions, the formula can collapse in the former and survive in the latter.
-/
theorem collapse_is_lens_relative
    (A B : NoneismLensAdapter σ) (φ : Formula σ)
    (hAstrict : ¬ Lens.allowsContradictions A.lens.profile)
    (hAwitness : A.lens.witness φ)
    (hAcontra : A.lens.contradicts φ)
    (hBwitness : B.lens.witness φ)
    (hBallow : Lens.allowsContradictions B.lens.profile) :
    interpretedImpossible A φ ∧ interpretedClaim B φ := by
  exact Lens.lens_relative_collapse_and_survival A.lens B.lens φ
    hAstrict hAwitness hAcontra hBwitness hBallow

end NoneismLensAdapter

end Subsumption
end PerspectivalPlenum
end HeytingLean
