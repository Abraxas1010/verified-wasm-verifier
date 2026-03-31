import HeytingLean.Core.Types

namespace HeytingLean
namespace LeanCoreV2

open HeytingLean.Core

/-- Types for LeanCore v2 programs. -/
abbrev Ty  := Core.Ty
/-- Contexts (lists of shared types). -/
abbrev Ctx := Core.Ctx
/-- De Bruijn variables (shared definition). -/
abbrev Var := Core.Var

/-- Intrinsically typed terms covering λ-calculus with sums/products and primitives. -/
inductive Term : Ctx → Ty → Type where
  | var  : Var Γ τ → Term Γ τ
  | lam  : Term (α :: Γ) β → Term Γ (Ty.arrow α β)
  | app  : Term Γ (Ty.arrow α β) → Term Γ α → Term Γ β
  | pair : Term Γ α → Term Γ β → Term Γ (Ty.prod α β)
  | fst  : Term Γ (Ty.prod α β) → Term Γ α
  | snd  : Term Γ (Ty.prod α β) → Term Γ β
  | inl  : Term Γ α → Term Γ (Ty.sum α β)
  | inr  : Term Γ β → Term Γ (Ty.sum α β)
  | matchSum :
      Term Γ (Ty.sum α β) →
      Term (α :: Γ) γ →
      Term (β :: Γ) γ →
      Term Γ γ
  | if_  : Term Γ Ty.bool → Term Γ τ → Term Γ τ → Term Γ τ
  -- primitives
  | constNat  : Nat → Term Γ Ty.nat
  | constBool : Bool → Term Γ Ty.bool
  | primAddNat : Term Γ (Ty.arrow Ty.nat (Ty.arrow Ty.nat Ty.nat))
  | primEqNat  : Term Γ (Ty.arrow Ty.nat (Ty.arrow Ty.nat Ty.bool))

end LeanCoreV2
end HeytingLean
