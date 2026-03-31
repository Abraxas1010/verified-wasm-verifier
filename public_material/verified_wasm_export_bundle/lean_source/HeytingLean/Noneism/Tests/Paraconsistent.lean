import HeytingLean.Noneism.Semantics.RoutleyMeyer
import HeytingLean.Noneism.Semantics.LP
import HeytingLean.Noneism.ProofTheory.NDRMSyntax
import HeytingLean.Noneism.ProofTheory.RMSeq
import HeytingLean.Noneism.ProofTheory.Completeness.RoutleyMeyerBridge

namespace HeytingLean
namespace Noneism
namespace Tests

open Noneism RM LP

namespace RMEx
open RM

inductive Atom where | A | B deriving DecidableEq, Repr, Inhabited

def W := Bool
def w0 : W := false

def frame : Frame W := { star := fun | false => true | true => false,
                          R := fun w u v => w = false ∧ u = false ∧ v = false }

def D := Unit
def ρ : Valuation D := fun _ => ()

def interp : W → Atom → (List D → Prop)
  | false, Atom.A => fun _ => True
  | true,  Atom.A => fun _ => False
  | false, Atom.B => fun _ => False
  | true,  Atom.B => fun _ => False

def existsP : W → D → Prop := fun _ _ => True

def M : Model Atom W D := { F := frame, interp := interp, existsP := existsP }

open Noneism Formula

def A : Formula Atom := .pred Atom.A []
def B : Formula Atom := .pred Atom.B []

theorem A_true_at_w0 : sat M ρ w0 A := by
  simp [sat, A, M, interp, w0]

theorem notA_true_at_w0 : sat M ρ w0 (.not A) := by
  simp [sat, A, M, interp, frame, w0]

theorem B_false_at_w0 : ¬ sat M ρ w0 B := by
  simp [sat, B, M, interp, w0]

theorem conj_true_at_w0 : sat M ρ w0 (.and A (.not A)) := by
  simpa [sat] using And.intro (A_true_at_w0) (notA_true_at_w0)

theorem impl_fails_at_w0 : ¬ sat M ρ w0 (.imp (.and A (.not A)) B) := by
  intro h
  change ∀ u v, frame.R w0 u v → (sat M ρ u (.and A (.not A)) → sat M ρ v B) at h
  have hR : frame.R w0 w0 w0 := by simp [frame, w0]
  have hConj : sat M ρ w0 (.and A (.not A)) := conj_true_at_w0
  have : sat M ρ w0 B := (h w0 w0 hR) hConj
  exact B_false_at_w0 this

end RMEx

/-- RM: contradiction without triviality at w0. -/
theorem rm_non_explosion :
    RM.sat RMEx.M RMEx.ρ RMEx.w0 (.and RMEx.A (.not RMEx.A)) ∧
    ¬ RM.sat RMEx.M RMEx.ρ RMEx.w0 RMEx.B := by
  exact And.intro RMEx.conj_true_at_w0 RMEx.B_false_at_w0

/-- RM: `(A ∧ ¬A) → B` is not satisfied at w0 in the countermodel. -/
theorem rm_impl_fails :
    ¬ RM.sat RMEx.M RMEx.ρ RMEx.w0 (.imp (.and RMEx.A (.not RMEx.A)) RMEx.B) :=
  RMEx.impl_fails_at_w0

theorem rm_not_entails_explosion :
    ¬ RM.Entails [(.and RMEx.A (.not RMEx.A))] RMEx.B := by
  intro hEnt
  have hPrem : ∀ ψ ∈ [(.and RMEx.A (.not RMEx.A))], RM.sat RMEx.M RMEx.ρ RMEx.w0 ψ := by
    intro ψ hψ
    simp at hψ
    subst hψ
    exact RMEx.conj_true_at_w0
  have hB : RM.sat RMEx.M RMEx.ρ RMEx.w0 RMEx.B :=
    hEnt RMEx.W RMEx.D RMEx.M RMEx.ρ RMEx.w0 hPrem
  exact RMEx.B_false_at_w0 hB

theorem rm_ndrm_non_explosion :
    ¬ NDRM.Derives [(.and RMEx.A (.not RMEx.A))] RMEx.B := by
  intro hDer
  have hEnt : RM.Entails [(.and RMEx.A (.not RMEx.A))] RMEx.B :=
    (NDRM.derives_iff_entails
      (Γ := [(.and RMEx.A (.not RMEx.A))]) (φ := RMEx.B)).1 hDer
  exact rm_not_entails_explosion hEnt

theorem rm_seq_valid_non_explosion :
    ¬ RMSeq.Derives (RMSeq.fromCore [(.and RMEx.A (.not RMEx.A))] RMEx.B) := by
  intro hDer
  have hEnt : RM.Entails [(.and RMEx.A (.not RMEx.A))] RMEx.B :=
    (RMSeq.derives_fromCore_iff_entails
      (Γ := [(.and RMEx.A (.not RMEx.A))]) (φ := RMEx.B)).1 hDer
  exact rm_not_entails_explosion hEnt

theorem rm_counterexample_explosion_witness :
    ∃ (W D : Type) (M : RM.Model RMEx.Atom W D) (ρ : RM.Valuation D) (w : W),
      (∀ ψ ∈ [(.and RMEx.A (.not RMEx.A))], RM.sat M ρ w ψ) ∧
        ¬ RM.sat M ρ w RMEx.B := by
  refine ⟨RMEx.W, RMEx.D, RMEx.M, RMEx.ρ, RMEx.w0, ?_⟩
  refine ⟨?_, RMEx.B_false_at_w0⟩
  intro ψ hψ
  simp at hψ
  subst hψ
  exact RMEx.conj_true_at_w0

theorem rm_ndsyntax_non_explosion :
    ¬ NDRMSyntax.Derives [(.and RMEx.A (.not RMEx.A))] RMEx.B := by
  exact RM.rm_not_derives_of_countermodel
    (Γ := [(.and RMEx.A (.not RMEx.A))]) (φ := RMEx.B)
    rm_counterexample_explosion_witness

theorem rm_ndsyntax_non_explosion_via_soundness :
    ¬ NDRMSyntax.Derives [(.and RMEx.A (.not RMEx.A))] RMEx.B := by
  exact RM.rm_not_derives_of_not_entails
    (Γ := [(.and RMEx.A (.not RMEx.A))]) (φ := RMEx.B)
    rm_not_entails_explosion

theorem rm_ndsyntax_core_non_explosion :
    ¬ NDRMSyntax.DerivesCore [(.and RMEx.A (.not RMEx.A))] RMEx.B := by
  exact RM.rm_not_derivesCore_of_countermodel
    (Γ := [(.and RMEx.A (.not RMEx.A))]) (φ := RMEx.B)
    rm_counterexample_explosion_witness

theorem rm_ndsyntax_core_non_explosion_via_soundness :
    ¬ NDRMSyntax.DerivesCore [(.and RMEx.A (.not RMEx.A))] RMEx.B := by
  exact RM.rm_not_derivesCore_of_not_entails
    (Γ := [(.and RMEx.A (.not RMEx.A))]) (φ := RMEx.B)
    rm_not_entails_explosion

theorem rm_seq_non_explosion :
    ¬ RMSeq.DerivesSyn (RMSeq.fromCore [(.and RMEx.A (.not RMEx.A))] RMEx.B) := by
  exact RM.rmseq_not_derivesSyn_from_countermodel
    (Γ := [(.and RMEx.A (.not RMEx.A))]) (φ := RMEx.B)
    rm_counterexample_explosion_witness

theorem rm_seq_non_explosion_via_soundness :
    ¬ RMSeq.DerivesSyn (RMSeq.fromCore [(.and RMEx.A (.not RMEx.A))] RMEx.B) := by
  exact RM.rmseq_not_derivesSyn_of_not_entails
    (Γ := [(.and RMEx.A (.not RMEx.A))]) (φ := RMEx.B)
    rm_not_entails_explosion

-- LP smoke: we only assert the definitions compile; deeper tests to be added later.

end Tests
end Noneism
end HeytingLean
