import HeytingLean.Noneism.ProofTheory.NDRMSyntax
import HeytingLean.Noneism.ProofTheory.RMSeq
import HeytingLean.Noneism.ProofTheory.Completeness.RoutleyMeyerCore
import HeytingLean.Noneism.Tests.Paraconsistent

namespace HeytingLean
namespace Noneism
namespace Tests

open Noneism Formula RM NDRMSyntax

/--
Proof-theoretic non-explosion for the syntactic RM labelled core, obtained from:
1. `NDRMSyntax.soundness`
2. the existing RM semantic countermodel.
-/
theorem rm_syntax_non_explosion :
    ¬ NDRMSyntax.Derives [RMEx.A, .not RMEx.A] RMEx.B := by
  intro hDer
  have hEnt : RM.Entails [RMEx.A, .not RMEx.A] RMEx.B := NDRMSyntax.soundness hDer
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

/--
Core syntactic non-explosion (without using the temporary completeness constructor).
-/
theorem rm_syntax_core_non_explosion :
    ¬ NDRMSyntax.DerivesCore [RMEx.A, .not RMEx.A] RMEx.B := by
  intro hDer
  have hEnt : RM.Entails [RMEx.A, .not RMEx.A] RMEx.B := NDRMSyntax.core_soundness hDer
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

/--
Native sequent-syntactic non-explosion for `RMSeq.DerivesSyn`.
-/
theorem rm_seqsyn_non_explosion :
    ¬ RMSeq.DerivesSyn (RMSeq.fromCore [RMEx.A, .not RMEx.A] RMEx.B) := by
  intro hDer
  have hValid : RMSeq.Valid (RMSeq.fromCore [RMEx.A, .not RMEx.A] RMEx.B) :=
    RMSeq.derivesSyn_sound hDer
  have hEnt : RM.Entails [RMEx.A, .not RMEx.A] RMEx.B :=
    (RMSeq.valid_fromCore_iff_entails
      (Γ := [RMEx.A, .not RMEx.A]) (φ := RMEx.B)).1 hValid
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

/--
Conjunctive-form native sequent-syntactic non-explosion.
-/
theorem rm_seqsyn_non_explosion_conj :
    ¬ RMSeq.DerivesSyn (RMSeq.fromCore [(.and RMEx.A (.not RMEx.A))] RMEx.B) := by
  intro hDer
  have hValid : RMSeq.Valid (RMSeq.fromCore [(.and RMEx.A (.not RMEx.A))] RMEx.B) :=
    RMSeq.derivesSyn_sound hDer
  have hEnt : RM.Entails [(.and RMEx.A (.not RMEx.A))] RMEx.B :=
    (RMSeq.valid_fromCore_iff_entails
      (Γ := [(.and RMEx.A (.not RMEx.A))]) (φ := RMEx.B)).1 hValid
  have hPrem :
      ∀ ψ ∈ [(.and RMEx.A (.not RMEx.A))], RM.sat RMEx.M RMEx.ρ RMEx.w0 ψ := by
    intro ψ hψ
    simp at hψ
    subst hψ
    exact RMEx.conj_true_at_w0
  have hB : RM.sat RMEx.M RMEx.ρ RMEx.w0 RMEx.B :=
    hEnt RMEx.W RMEx.D RMEx.M RMEx.ρ RMEx.w0 hPrem
  exact RMEx.B_false_at_w0 hB

/--
Formula-only modus ponens is not derivable in the RM core.

`impE` requires an explicit relational premise `rel w u v`; this theorem
locks in that `[φ → ψ, φ] ⊬ ψ` at the formula-only core surface.
-/
theorem rm_syntax_core_impE_needs_rel :
    ¬ NDRMSyntax.DerivesCore [(.imp RMEx.A RMEx.B), RMEx.A] RMEx.B := by
  intro hDer
  have hEnt : RM.Entails [(.imp RMEx.A RMEx.B), RMEx.A] RMEx.B :=
    NDRMSyntax.core_soundness hDer
  let W : Type := Unit
  let D : Type := Unit
  let frame : RM.Frame W := {
    star := fun _ => ()
    R := fun _ _ _ => False
  }
  let interp : W → RMEx.Atom → (List D → Prop)
    | _, RMEx.Atom.A => fun _ => True
    | _, RMEx.Atom.B => fun _ => False
  let existsP : W → D → Prop := fun _ _ => True
  let M : RM.Model RMEx.Atom W D := { F := frame, interp := interp, existsP := existsP }
  let ρ : RM.Valuation D := fun _ => ()
  let w : W := ()
  have hPrem : ∀ ψ ∈ [(.imp RMEx.A RMEx.B), RMEx.A], RM.sat M ρ w ψ := by
    intro ψ hψ
    rcases List.mem_cons.1 hψ with hImp | hTail
    · subst hImp
      simp [RM.sat, RMEx.A, RMEx.B, M, frame]
    · rcases List.mem_cons.1 hTail with hA | hNil
      · subst hA
        simp [RM.sat, RMEx.A, M, interp]
      · cases hNil
  have hB : RM.sat M ρ w RMEx.B := hEnt W D M ρ w hPrem
  have hBFalse : ¬ RM.sat M ρ w RMEx.B := by
    simp [RM.sat, RMEx.B, M, interp]
  exact hBFalse hB

/--
No global set-level implication-elimination bridge exists for the current RM core profile.

This follows from `rm_syntax_core_impE_needs_rel`: if such a bridge existed, it would force
formula-only modus ponens at core level, contradicting that theorem.
-/
theorem rm_no_global_derivable_impElim_instance :
    ¬ (∀ {T : Set (Formula RMEx.Atom)} {φ ψ : Formula RMEx.Atom},
        RM.Derivable T (.imp φ ψ) → RM.Derivable T φ → RM.Derivable T ψ) := by
  intro hImpElim
  let T : Set (Formula RMEx.Atom) :=
    fun χ => χ = (.imp RMEx.A RMEx.B) ∨ χ = RMEx.A
  have hDerImp : RM.Derivable (T := T) (.imp RMEx.A RMEx.B) :=
    RM.derivable_of_mem (T := T) (Or.inl rfl)
  have hDerA : RM.Derivable (T := T) RMEx.A :=
    RM.derivable_of_mem (T := T) (Or.inr rfl)
  have hDerB : RM.Derivable (T := T) RMEx.B :=
    hImpElim (T := T) (φ := RMEx.A) (ψ := RMEx.B) hDerImp hDerA
  rcases hDerB with ⟨Γ, hΓ, hCore⟩
  have hSub : Γ ⊆ [(.imp RMEx.A RMEx.B), RMEx.A] := by
    intro χ hχ
    have hMemT : χ ∈ T := hΓ χ hχ
    rcases hMemT with hEqImp | hEqA
    · subst hEqImp
      simp
    · subst hEqA
      simp
  have hCoreList : NDRMSyntax.DerivesCore [(.imp RMEx.A RMEx.B), RMEx.A] RMEx.B :=
    RM.core_weaken hCore hSub
  exact rm_syntax_core_impE_needs_rel hCoreList

/--
`⊥`-elimination is explicitly available in the RM syntactic calculus.
-/
theorem rm_syntax_bot_explosion :
    NDRMSyntax.Derives [(.bot : Formula RMEx.Atom)] RMEx.B := by
  refine NDRMSyntax.Derives.core ?_
  have hBot :
      NDRMSyntax.DerivesL
        (NDRM.embedAtZero [(.bot : Formula RMEx.Atom)])
        (.frm 0 (.bot : Formula RMEx.Atom)) :=
    NDRMSyntax.DerivesL.hyp (by simp [NDRM.embedAtZero])
  exact NDRMSyntax.DerivesL.botE hBot

/--
Semantic counterpart: entailment from `⊥` is valid (vacuously) in RM semantics.
-/
theorem rm_sem_entails_from_bot :
    RM.Entails [(.bot : Formula RMEx.Atom)] RMEx.B := by
  intro W D M ρ w hPrem
  have hBot : RM.sat M ρ w (.bot : Formula RMEx.Atom) := hPrem _ (by simp)
  exact False.elim hBot

theorem rm_syntax_piE_entails
    {σ : Type} {x a : Noneism.Var} {φ : Formula σ}
    (ha : a ∉ Syntax.varsFormula (σ := σ) φ) :
    RM.Entails [(.pi x φ)] (Syntax.substFormula (σ := σ) x (.var a) φ) := by
  have hDer :
      NDRMSyntax.Derives [(.pi x φ)] (Syntax.substFormula (σ := σ) x (.var a) φ) := by
    refine NDRMSyntax.Derives.core ?_
    have hPi :
        NDRMSyntax.DerivesL (NDRM.embedAtZero [(.pi x φ)]) (.frm 0 (.pi x φ)) :=
      NDRMSyntax.DerivesL.hyp (by simp [NDRM.embedAtZero])
    exact NDRMSyntax.DerivesL.piE ha hPi
  exact NDRMSyntax.soundness hDer

theorem rm_syntax_piE_bound_entails
    {σ : Type} {x a : Noneism.Var} {φ : Formula σ}
    (ha : a ∉ Syntax.boundVars (σ := σ) φ) :
    RM.Entails [(.pi x φ)] (Syntax.substFormula (σ := σ) x (.var a) φ) := by
  have hDer :
      NDRMSyntax.Derives [(.pi x φ)] (Syntax.substFormula (σ := σ) x (.var a) φ) := by
    refine NDRMSyntax.Derives.core ?_
    have hPi :
        NDRMSyntax.DerivesL (NDRM.embedAtZero [(.pi x φ)]) (.frm 0 (.pi x φ)) :=
      NDRMSyntax.DerivesL.hyp (by simp [NDRM.embedAtZero])
    exact NDRMSyntax.DerivesL.piEbound ha hPi
  exact NDRMSyntax.soundness hDer

theorem rm_syntax_sigmaI_entails
    {σ : Type} {x a : Noneism.Var} {φ : Formula σ}
    (ha : a ∉ Syntax.varsFormula (σ := σ) φ) :
    RM.Entails [Syntax.substFormula (σ := σ) x (.var a) φ] (.sigma x φ) := by
  have hDer :
      NDRMSyntax.Derives [Syntax.substFormula (σ := σ) x (.var a) φ] (.sigma x φ) := by
    refine NDRMSyntax.Derives.core ?_
    have hInst :
        NDRMSyntax.DerivesL
          (NDRM.embedAtZero [Syntax.substFormula (σ := σ) x (.var a) φ])
          (.frm 0 (Syntax.substFormula (σ := σ) x (.var a) φ)) :=
      NDRMSyntax.DerivesL.hyp (by simp [NDRM.embedAtZero])
    exact NDRMSyntax.DerivesL.sigmaI ha hInst
  exact NDRMSyntax.soundness hDer

theorem rm_syntax_sigmaI_bound_entails
    {σ : Type} {x a : Noneism.Var} {φ : Formula σ}
    (ha : a ∉ Syntax.boundVars (σ := σ) φ) :
    RM.Entails [Syntax.substFormula (σ := σ) x (.var a) φ] (.sigma x φ) := by
  have hDer :
      NDRMSyntax.Derives [Syntax.substFormula (σ := σ) x (.var a) φ] (.sigma x φ) := by
    refine NDRMSyntax.Derives.core ?_
    have hInst :
        NDRMSyntax.DerivesL
          (NDRM.embedAtZero [Syntax.substFormula (σ := σ) x (.var a) φ])
          (.frm 0 (Syntax.substFormula (σ := σ) x (.var a) φ)) :=
      NDRMSyntax.DerivesL.hyp (by simp [NDRM.embedAtZero])
    exact NDRMSyntax.DerivesL.sigmaIbound ha hInst
  exact NDRMSyntax.soundness hDer

theorem rm_syntax_piE_self_entails
    {σ : Type} {x : Noneism.Var} {φ : Formula σ} :
    RM.Entails [(.pi x φ)] φ := by
  have hDer : NDRMSyntax.Derives [(.pi x φ)] φ := by
    refine NDRMSyntax.Derives.core ?_
    have hPi :
        NDRMSyntax.DerivesL (NDRM.embedAtZero [(.pi x φ)]) (.frm 0 (.pi x φ)) :=
      NDRMSyntax.DerivesL.hyp (by simp [NDRM.embedAtZero])
    exact NDRMSyntax.DerivesL.piEself hPi
  exact NDRMSyntax.soundness hDer

theorem rm_syntax_sigmaI_self_entails
    {σ : Type} {x : Noneism.Var} {φ : Formula σ} :
    RM.Entails [φ] (.sigma x φ) := by
  have hDer : NDRMSyntax.Derives [φ] (.sigma x φ) := by
    refine NDRMSyntax.Derives.core ?_
    have hBody :
        NDRMSyntax.DerivesL (NDRM.embedAtZero [φ]) (.frm 0 φ) :=
      NDRMSyntax.DerivesL.hyp (by simp [NDRM.embedAtZero])
    exact NDRMSyntax.DerivesL.sigmaIself hBody
  exact NDRMSyntax.soundness hDer

end Tests
end Noneism
end HeytingLean
