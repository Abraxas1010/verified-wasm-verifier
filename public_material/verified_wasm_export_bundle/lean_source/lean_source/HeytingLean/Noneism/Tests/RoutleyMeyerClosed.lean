import HeytingLean.Noneism.ProofTheory.Completeness.RoutleyMeyerBridge
import HeytingLean.Noneism.Tests.Paraconsistent

namespace HeytingLean
namespace Noneism
namespace Tests

open Noneism Formula NDRM NDRMSyntax RM

/-- Closed adequacy for the baseline RM derivability surface. -/
theorem rm_ndrm_adequacy {σ : Type} {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRM.Derives Γ φ ↔ RM.Entails Γ φ :=
  RM.rm_adequacy_closed_ndrm

/-- Baseline proof-theoretic non-explosion on `NDRM.Derives`. -/
theorem rm_ndrm_non_explosion_closed :
    ¬ NDRM.Derives [RMEx.A, .not RMEx.A] RMEx.B := by
  intro hDer
  have hEnt : RM.Entails [RMEx.A, .not RMEx.A] RMEx.B :=
    RM.rm_soundness_closed hDer
  have hPrem : ∀ ψ ∈ [RMEx.A, .not RMEx.A], RM.sat RMEx.M RMEx.ρ RMEx.w0 ψ := by
    intro ψ hψ
    rcases List.mem_cons.1 hψ with hA | hTail
    · subst hA
      exact RMEx.A_true_at_w0
    · rcases List.mem_cons.1 hTail with hNotA | hNil
      · subst hNotA
        exact RMEx.notA_true_at_w0
      · cases hNil
  have hB : RM.sat RMEx.M RMEx.ρ RMEx.w0 RMEx.B :=
    hEnt RMEx.W RMEx.D RMEx.M RMEx.ρ RMEx.w0 hPrem
  exact RMEx.B_false_at_w0 hB

theorem rm_ndrm_non_explosion_conj_closed :
    ¬ NDRM.Derives [(.and RMEx.A (.not RMEx.A))] RMEx.B := by
  intro hDer
  have hEnt : RM.Entails [(.and RMEx.A (.not RMEx.A))] RMEx.B :=
    RM.rm_soundness_closed hDer
  have hPrem : ∀ ψ ∈ [(.and RMEx.A (.not RMEx.A))], RM.sat RMEx.M RMEx.ρ RMEx.w0 ψ := by
    intro ψ hψ
    simp at hψ
    subst hψ
    exact RMEx.conj_true_at_w0
  have hB : RM.sat RMEx.M RMEx.ρ RMEx.w0 RMEx.B :=
    hEnt RMEx.W RMEx.D RMEx.M RMEx.ρ RMEx.w0 hPrem
  exact RMEx.B_false_at_w0 hB

/-- Closed FO/Henkin lane non-explosion for `NDRMSyntax.Derives`. -/
theorem rm_ndsyntax_henkin_non_explosion_closed :
    ¬ NDRMSyntax.Derives [(.and RMEx.A (.not RMEx.A))] RMEx.B := by
  intro hDer
  have hEnt : RM.Entails [(.and RMEx.A (.not RMEx.A))] RMEx.B :=
    (RM.rm_adequacy_henkin_closed
      (Γ := [(.and RMEx.A (.not RMEx.A))]) (φ := RMEx.B)).1 hDer
  have hPrem : ∀ ψ ∈ [(.and RMEx.A (.not RMEx.A))], RM.sat RMEx.M RMEx.ρ RMEx.w0 ψ := by
    intro ψ hψ
    simp at hψ
    subst hψ
    exact RMEx.conj_true_at_w0
  have hB : RM.sat RMEx.M RMEx.ρ RMEx.w0 RMEx.B :=
    hEnt RMEx.W RMEx.D RMEx.M RMEx.ρ RMEx.w0 hPrem
  exact RMEx.B_false_at_w0 hB

end Tests
end Noneism
end HeytingLean
