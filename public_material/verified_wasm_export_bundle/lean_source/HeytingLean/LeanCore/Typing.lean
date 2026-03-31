import HeytingLean.LeanCore.Syntax
import HeytingLean.LeanCore.Primitives

namespace HeytingLean
namespace LeanCore

/-- Typing judgement for LeanCore terms (extrinsic). -/
inductive HasType (prim : PrimEnv) : Ctx → ∀ {τ : Ty}, Term τ → Prop where
  | var {Γ : Ctx} {τ : Ty} {idx : Nat}
      (h : lookup Γ idx = some τ) :
      HasType prim Γ (Term.var idx)
  | lam {Γ : Ctx} {α β : Ty} {body : Term β}
      (h : HasType prim (α :: Γ) body) :
      HasType prim Γ (Term.lam body)
  | app {Γ : Ctx} {α β : Ty} {f : Term (Ty.arrow α β)} {x : Term α}
      (hf : HasType prim Γ f)
      (hx : HasType prim Γ x) :
      HasType prim Γ (Term.app f x)
  | pair {Γ : Ctx} {α β : Ty} {t₁ : Term α} {t₂ : Term β}
      (h₁ : HasType prim Γ t₁)
      (h₂ : HasType prim Γ t₂) :
      HasType prim Γ (Term.pair t₁ t₂)
  | fst {Γ : Ctx} {α β : Ty} {t : Term (Ty.prod α β)}
      (h : HasType prim Γ t) :
      HasType prim Γ (Term.fst t)
  | snd {Γ : Ctx} {α β : Ty} {t : Term (Ty.prod α β)}
      (h : HasType prim Γ t) :
      HasType prim Γ (Term.snd t)
  | inl {Γ : Ctx} {α β : Ty} {t : Term α}
      (h : HasType prim Γ t) :
      HasType prim Γ (Term.inl t)
  | inr {Γ : Ctx} {α β : Ty} {t : Term β}
      (h : HasType prim Γ t) :
      HasType prim Γ (Term.inr t)
  | matchSum {Γ : Ctx} {α β γ : Ty}
      {scrut : Term (Ty.sum α β)}
      {k₁ k₂ : Term γ}
      (hs : HasType prim Γ scrut)
      (hk₁ : HasType prim Γ k₁)
      (hk₂ : HasType prim Γ k₂) :
      HasType prim Γ (Term.matchSum scrut k₁ k₂)
  | const {Γ : Ctx} {τ : Ty} {name : String}
      (h : PrimEnv.lookupTy prim name = some τ) :
      HasType prim Γ (Term.const (τ:=τ) name)

end LeanCore
end HeytingLean
