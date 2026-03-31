import HeytingLean.Noneism.ProofTheory.NDRM
import HeytingLean.Noneism.ProofTheory.NDRMSyntax

namespace HeytingLean
namespace Noneism
namespace RM

open Noneism Formula

theorem rm_soundness_closed {σ : Type} {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRM.Derives Γ φ → Entails Γ φ := by
  intro h
  exact (NDRM.derives_iff_entails (Γ := Γ) (φ := φ)).1 h

theorem rm_completeness_closed {σ : Type} {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails Γ φ → NDRM.Derives Γ φ := by
  intro h
  exact (NDRM.derives_iff_entails (Γ := Γ) (φ := φ)).2 h

theorem rm_adequacy_closed_ndrm {σ : Type} {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRM.Derives Γ φ ↔ Entails Γ φ :=
  NDRM.derives_iff_entails (Γ := Γ) (φ := φ)

theorem rm_soundness {σ : Type} {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ → Entails Γ φ := by
  intro h
  exact NDRMSyntax.soundness h

theorem rm_core_soundness {σ : Type} {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.DerivesCore Γ φ → Entails Γ φ := by
  intro h
  exact NDRMSyntax.core_soundness h

theorem rm_soundness_syntax {σ : Type} {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ → Entails Γ φ := by
  intro h
  exact NDRMSyntax.soundness h

end RM
end Noneism
end HeytingLean
