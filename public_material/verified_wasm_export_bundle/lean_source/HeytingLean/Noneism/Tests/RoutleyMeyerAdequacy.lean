import HeytingLean.Noneism.ProofTheory.Completeness.RoutleyMeyerBridge
import HeytingLean.Noneism.Tests.RoutleyMeyerClosed
import HeytingLean.PerspectivalPlenum.Subsumption

namespace HeytingLean
namespace Noneism
namespace Tests

open Noneism Formula NDRM NDRMSyntax RM

/-- Closed adequacy smoke for the baseline RM calculus. -/
theorem rm_adequacy_primary_closed_smoke {σ : Type}
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRM.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_primary_closed

/-- Closed adequacy smoke for the FO/Henkin syntax route. -/
theorem rm_adequacy_henkin_closed_smoke {σ : Type}
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_henkin_closed

/-- Fallback seqclass route remains available and type-aligned. -/
theorem rm_adequacy_fallback_seqclass_smoke {σ : Type}
    [RMSeq.HasFromCoreSeqCompleteness σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_fallback_seqclass

/-- ND/sequent route parity contract for the syntax adequacy lane. -/
theorem rm_adequacy_seqclass_route_parity_smoke {σ : Type}
    [RMSeq.HasFromCoreSeqCompleteness σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    ((RM.rm_adequacy_from_seqclass (σ := σ) (Γ := Γ) (φ := φ)).1 =
      (by
        letI : NDRMSyntax.HasCoreCompleteness σ := RMSeq.coreCompleteness_of_seqSynCompleteness σ
        exact (RM.rm_adequacy_ndsyntax (σ := σ) (Γ := Γ) (φ := φ)).1)) ∧
    ((RM.rm_adequacy_from_seqclass (σ := σ) (Γ := Γ) (φ := φ)).2 =
      (by
        letI : NDRMSyntax.HasCoreCompleteness σ := RMSeq.coreCompleteness_of_seqSynCompleteness σ
        exact (RM.rm_adequacy_ndsyntax (σ := σ) (Γ := Γ) (φ := φ)).2)) :=
  RM.rm_adequacy_from_seqclass_route_parity

/-- Closed non-explosion smoke for baseline RM derivability. -/
theorem rm_ndrm_non_explosion_closed_smoke :
    ¬ NDRM.Derives [(.and RMEx.A (.not RMEx.A))] RMEx.B :=
  rm_ndrm_non_explosion_conj_closed

/-- Closed non-explosion smoke for FO/Henkin syntax derivability. -/
theorem rm_ndsyntax_non_explosion_closed_smoke :
    ¬ NDRMSyntax.Derives [(.and RMEx.A (.not RMEx.A))] RMEx.B :=
  rm_ndsyntax_henkin_non_explosion_closed

namespace SubsumptionCompat

open HeytingLean.PerspectivalPlenum

abbrev rmConj : Formula RMEx.Atom := (.and RMEx.A (.not RMEx.A))

def strictAdapter : Subsumption.NoneismLensAdapter RMEx.Atom :=
  { lens :=
      { profile :=
          { name := "RM-Strict"
            contradictionPolicy := Lens.ContradictionPolicy.booleanStrict
            dimension := 2
            languageTag := "RM" }
        witness := fun _ => True
        contradicts := fun φ =>
          φ = (.bot : Formula RMEx.Atom) ∨ φ = rmConj } }

def permissiveAdapter : Subsumption.NoneismLensAdapter RMEx.Atom :=
  { lens :=
      { profile :=
          { name := "RM-Permissive"
            contradictionPolicy := Lens.ContradictionPolicy.paraconsistent
            dimension := 3
            languageTag := "RM" }
        witness := fun _ => True
        contradicts := fun φ =>
          φ = (.bot : Formula RMEx.Atom) ∨ φ = rmConj } }

def identityBridge : Subsumption.DerivabilityBridge RMEx.Atom where
  Derives Γ φ := Γ φ
  sound_local _hDer _A hΓ := hΓ _ _hDer

theorem strict_bottom_collapse :
    strictAdapter.interpretedImpossible (.bot : Formula RMEx.Atom) := by
  refine Lens.collapse_of_strict_contradiction strictAdapter.lens (.bot : Formula RMEx.Atom) ?_ ?_ ?_
  · simp [strictAdapter, Lens.allowsContradictions]
  · simp [strictAdapter]
  · simp [strictAdapter]

theorem permissive_conj_claim :
    permissiveAdapter.interpretedClaim rmConj := by
  exact Lens.satisfiable_of_allowed_contradiction permissiveAdapter.lens rmConj
    (by simp [permissiveAdapter, rmConj])
    (by simp [permissiveAdapter, Lens.allowsContradictions])

theorem conj_is_lens_relative :
    strictAdapter.interpretedImpossible rmConj ∧ permissiveAdapter.interpretedClaim rmConj := by
  exact Subsumption.NoneismLensAdapter.collapse_is_lens_relative
    strictAdapter permissiveAdapter rmConj
    (by simp [strictAdapter, Lens.allowsContradictions])
    (by simp [strictAdapter, rmConj])
    (by simp [strictAdapter, rmConj])
    (by simp [permissiveAdapter, rmConj])
    (by simp [permissiveAdapter, Lens.allowsContradictions])

theorem identityBridge_transfers_conj_claim :
    permissiveAdapter.interpretedClaim rmConj := by
  have hDer : identityBridge.Derives (fun ψ : Formula RMEx.Atom => ψ = rmConj) rmConj := by
    simp [identityBridge, rmConj]
  have hΓ :
      ∀ ψ : Formula RMEx.Atom,
        (fun χ : Formula RMEx.Atom => χ = rmConj) ψ →
          permissiveAdapter.interpretedClaim ψ := by
    intro ψ hψ
    subst hψ
    exact permissive_conj_claim
  exact Subsumption.DerivabilityBridge.derivable_to_local_claim
    identityBridge hDer permissiveAdapter hΓ

theorem rm_adequacy_preserved_under_subsumption {σ : Type}
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRM.Derives Γ φ ↔ RM.Entails Γ φ :=
  rm_adequacy_primary_closed_smoke

theorem rm_non_explosion_preserved_under_subsumption :
    ¬ NDRM.Derives [rmConj] RMEx.B :=
  rm_ndrm_non_explosion_closed_smoke

end SubsumptionCompat

end Tests
end Noneism
end HeytingLean
