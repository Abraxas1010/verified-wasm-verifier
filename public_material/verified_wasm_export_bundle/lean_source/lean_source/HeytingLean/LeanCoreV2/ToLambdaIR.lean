import HeytingLean.LeanCoreV2.Syntax
import HeytingLean.LeanCoreV2.Semantics
import HeytingLean.LambdaIR.Syntax
import HeytingLean.LambdaIR.Semantics

namespace HeytingLean
namespace LeanCoreV2
namespace ToLambdaIR

open HeytingLean.Core
open LeanCoreV2
open LambdaIR

@[simp] theorem intOfNat_eq_iff (x y : Nat) :
    (Int.ofNat x = Int.ofNat y) ↔ x = y := by
  constructor
  · intro h; exact Int.ofNat.inj h
  · intro h; simp [h]

@[simp] theorem natCast_eq_natCast_iff (x y : Nat) :
    ((x : Int) = (y : Int)) ↔ x = y := by
  constructor
  · intro h; exact Int.ofNat.inj h
  · intro h; simp [h]

/-- Structural translation from LeanCoreV2 terms to LambdaIR terms. -/
@[simp] def translateTerm :
    ∀ {Γ τ}, LeanCoreV2.Term Γ τ → LambdaIR.Term Γ τ
  | _, _, Term.var v           => LambdaIR.Term.var v
  | _, _, Term.lam body        => LambdaIR.Term.lam (translateTerm body)
  | _, _, Term.app f t         => LambdaIR.Term.app (translateTerm f) (translateTerm t)
  | _, _, Term.pair t₁ t₂      => LambdaIR.Term.pair (translateTerm t₁) (translateTerm t₂)
  | _, _, Term.fst t           => LambdaIR.Term.fst (translateTerm t)
  | _, _, Term.snd t           => LambdaIR.Term.snd (translateTerm t)
  | _, _, Term.inl t           => LambdaIR.Term.inl (translateTerm t)
  | _, _, Term.inr t           => LambdaIR.Term.inr (translateTerm t)
  | _, _, Term.matchSum s k₁ k₂ =>
      LambdaIR.Term.matchSum (translateTerm s) (translateTerm k₁) (translateTerm k₂)
  | _, _, Term.if_ c t₁ t₂     =>
      LambdaIR.Term.if_ (translateTerm c) (translateTerm t₁) (translateTerm t₂)
  | _, _, Term.constNat n      => LambdaIR.Term.constNat n
  | _, _, Term.constBool b     => LambdaIR.Term.constBool b
  | _, _, Term.primAddNat      => LambdaIR.Term.primAddNat
  | _, _, Term.primEqNat       => LambdaIR.Term.primEqNat

@[simp] theorem translate_eval
    {Γ τ} (t : LeanCoreV2.Term Γ τ) (ρ : Env Γ) :
        LambdaIR.eval (translateTerm t) ρ = LeanCoreV2.eval t ρ :=
by
  revert ρ
  induction t with
  | var v =>
      intro ρ
      simp [translateTerm]
  | lam body ih =>
      intro ρ
      funext x
      have hx := ih (extendEnv ρ x)
      simpa [translateTerm, LambdaIR.eval, LeanCoreV2.eval] using hx
  | app f t ihf iht =>
      intro ρ
      have hf := ihf ρ
      have ht := iht ρ
      simp [translateTerm, LambdaIR.eval, LeanCoreV2.eval, hf, ht]
  | pair t₁ t₂ ih₁ ih₂ =>
      intro ρ
      have h₁ := ih₁ ρ
      have h₂ := ih₂ ρ
      simp [translateTerm, LambdaIR.eval, LeanCoreV2.eval, h₁, h₂]
  | fst t ih =>
      intro ρ
      have ht := ih ρ
      simp [translateTerm, LambdaIR.eval, LeanCoreV2.eval, ht]
  | snd t ih =>
      intro ρ
      have ht := ih ρ
      simp [translateTerm, LambdaIR.eval, LeanCoreV2.eval, ht]
  | inl t ih =>
      intro ρ
      have ht := ih ρ
      simp [translateTerm, LambdaIR.eval, LeanCoreV2.eval, ht]
  | inr t ih =>
      intro ρ
      have ht := ih ρ
      simp [translateTerm, LambdaIR.eval, LeanCoreV2.eval, ht]
  | constNat n =>
      intro ρ
      simp [translateTerm, LambdaIR.eval, LeanCoreV2.eval]
  | constBool b =>
      intro ρ
      simp [translateTerm, LambdaIR.eval, LeanCoreV2.eval]
  | primAddNat =>
      intro ρ
      simp [translateTerm, LambdaIR.eval, LeanCoreV2.eval]
  | primEqNat =>
      intro ρ
      funext x y
      simp [translateTerm, LambdaIR.eval, LeanCoreV2.eval]
  | matchSum s k₁ k₂ ihs ih₁ ih₂ =>
      intro ρ
      have hs := ihs ρ
      cases h : LeanCoreV2.eval s ρ with
      | inl a =>
          have hsIR : LambdaIR.eval (translateTerm s) ρ = Sum.inl a := by
            simpa [translateTerm, LambdaIR.eval, LeanCoreV2.eval, h] using hs
          have hk := ih₁ (extendEnv ρ a)
          simpa [translateTerm, LambdaIR.eval, LeanCoreV2.eval, extendEnv, hsIR, h] using hk
      | inr b =>
          have hsIR : LambdaIR.eval (translateTerm s) ρ = Sum.inr b := by
            simpa [translateTerm, LambdaIR.eval, LeanCoreV2.eval, h] using hs
          have hk := ih₂ (extendEnv ρ b)
          simpa [translateTerm, LambdaIR.eval, LeanCoreV2.eval, extendEnv, hsIR, h] using hk
  | if_ c t₁ t₂ ihc ih₁ ih₂ =>
      intro ρ
      have hc := ihc ρ
      cases h : LeanCoreV2.eval c ρ with
      | false =>
          have hcIR : LambdaIR.eval (translateTerm c) ρ = false := by
            simpa [translateTerm, LambdaIR.eval, LeanCoreV2.eval, h] using hc
          have ht := ih₂ ρ
          simpa [translateTerm, LambdaIR.eval, LeanCoreV2.eval, h, hcIR] using ht
      | true =>
          have hcIR : LambdaIR.eval (translateTerm c) ρ = true := by
            simpa [translateTerm, LambdaIR.eval, LeanCoreV2.eval, h] using hc
          have ht := ih₁ ρ
          simpa [translateTerm, LambdaIR.eval, LeanCoreV2.eval, h, hcIR] using ht

@[simp] theorem translate_eval_closed {τ} (t : LeanCoreV2.Term [] τ) :
    LambdaIR.evalClosed (translateTerm t) = LeanCoreV2.evalClosed t :=
by
  simp [LambdaIR.evalClosed, LeanCoreV2.evalClosed, translate_eval]

end ToLambdaIR
end LeanCoreV2
end HeytingLean
