import HeytingLean.Compilation.LambdaIR.Layout

/-!
# Compilation.LambdaIR.Typing (bundle slice)

This file defines a small typing judgment for the layout-aware λ-IR introduced
in `Compilation/LambdaIR/Layout.lean`.

The goal is to provide a stable interface for later compilation correctness
work, while remaining executable-first and lightweight.
-/

namespace HeytingLean
namespace Compilation
namespace LambdaIR

/-- Typing context (name → type). -/
abbrev Context := List (String × LType)

namespace Context

/-- Lookup a variable in a context. -/
def lookup (ctx : Context) (name : String) : Option LType :=
  (ctx.find? (fun p => p.1 = name)).map Prod.snd

end Context

/-- Typing judgment (lightweight, layout-aware). -/
inductive HasType : Context → LExpr → LType → Prop where
  | var : ∀ ctx name τ,
      Context.lookup ctx name = some τ →
      HasType ctx (.var name) τ
  | nat_lit : ∀ ctx n,
      HasType ctx (.lit n) .nat
  | lam : ∀ ctx name σ body τ,
      HasType ((name, σ) :: ctx) body τ →
      HasType ctx (.lam name σ body) (.fn σ τ)
  | app : ∀ ctx f x σ τ,
      HasType ctx f (.fn σ τ) →
      HasType ctx x σ →
      HasType ctx (.app f x) τ

  | tensorAlloc : ∀ ctx ann,
      -- Bundle default: allocate a Nat tensor.
      HasType ctx (.tensorAlloc ann) (.tensor .nat ann)
  | tensorIndex : ∀ ctx t idxs τ ann,
      HasType ctx t (.tensor τ ann) →
      (∀ x, x ∈ idxs → HasType ctx x .nat) →
      HasType ctx (.tensorIndex t idxs) τ
  | tensorStore : ∀ ctx t idxs v τ ann,
      HasType ctx t (.tensor τ ann) →
      (∀ x, x ∈ idxs → HasType ctx x .nat) →
      HasType ctx v τ →
      HasType ctx (.tensorStore t idxs v) (.tensor τ ann)

end LambdaIR
end Compilation
end HeytingLean
