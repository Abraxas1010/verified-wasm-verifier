import HeytingLean.ClosingTheLoop.MR.ClosureOperator
import HeytingLean.LoF.MRSystems.Coalgebra
import HeytingLean.LoF.MRSystems.Nucleus
import HeytingLean.Varela.ReentryNucleus

/-!
# Varela ↔ `(M,R)` Semantic Closure Bridge

This file keeps the bridge honest: it reuses the existing selector-closure
operator and its lifted nucleus on predicates over selectors. It does not claim
that a categorical `β_b` theorem has already been formalized.
-/

namespace HeytingLean.Varela

open HeytingLean.ClosingTheLoop.MR
open HeytingLean.LoF.MRSystems

universe u v

abbrev SemanticClosureNucleus {S : MRSystem.{u, v}} (b : S.B) (RI : RightInverseAt S b) :=
  closedSelectorNucleus (S := S) (b := b) RI

theorem closeSelector_idempotent {S : MRSystem.{u, v}} {b : S.B}
    (RI : RightInverseAt S b) (Φ : Selector S) :
    closeSelector S b RI (closeSelector S b RI Φ) = closeSelector S b RI Φ :=
  closeSelector.idem (S := S) (b := b) (RI := RI) Φ

theorem selector_closed_iff_beta_image {S : MRSystem.{u, v}} {b : S.B}
    (RI : RightInverseAt S b) (Φ : Selector S) :
    IsClosed S b RI Φ ↔ ∃ g : AdmissibleMap S, RI.β g = Φ :=
  IsClosed.exists_eq_beta_iff (S := S) (b := b) (RI := RI) Φ

theorem semantic_closure_fixed_iff {S : MRSystem.{u, v}} {b : S.B}
    (RI : RightInverseAt S b) (U : Set (Selector S)) :
    SemanticClosureNucleus (S := S) b RI U = U ↔
      nonClosedCore (S := S) (b := b) RI ⊆ U :=
  closedSelectorNucleus_fixed_iff (S := S) (b := b) (RI := RI) U

noncomputable def semantic_closure_truth_values_equiv {S : MRSystem.{u, v}} {b : S.B}
    (RI : RightInverseAt S b) :
    ΩClosed (S := S) (b := b) RI ≃ Set (ClosedSelectorFixed (S := S) (b := b) RI) :=
  ΩClosed.equivClosedSubsets (S := S) (b := b) (RI := RI)

theorem closedDiag_is_reader_fixedpoint (m : MRCore.{u, v}) :
    m.ClosedDiag ↔ ∀ a : m.A, Function.IsFixedPt (fun b : m.B => m.R b a) (m.M a) :=
  MRCore.closedDiag_iff_isFixedPt (m := m)

end HeytingLean.Varela
