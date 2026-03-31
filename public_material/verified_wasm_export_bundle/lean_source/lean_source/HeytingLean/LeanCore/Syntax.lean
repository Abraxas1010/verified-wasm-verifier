import Lean

namespace HeytingLean
namespace LeanCore

/-- Base types for LeanCore. Keep this finite so indexed pattern matching
can eliminate impossible branches definitionally. -/
inductive BaseTy where
  | nat
  | bool
  deriving DecidableEq, Repr

/-- Simple type language for LeanCore. -/
inductive Ty where
  | base  (name : BaseTy)
  | prod  (α β : Ty)
  | sum   (α β : Ty)
  | arrow (α β : Ty)
  deriving DecidableEq, Repr

/-- Typing contexts are snoc lists of types (head = most recent binder). -/
abbrev Ctx := List Ty

/-- Lookup helper for contexts. Returns the type at the given index, if present. -/
def lookup (Γ : Ctx) (idx : Nat) : Option Ty :=
  match Γ, idx with
  | [], _ => none
  | τ :: _, 0 => some τ
  | _ :: Γ', Nat.succ i => lookup Γ' i

/-- Raw terms for the LeanCore calculus (de Bruijn indices). -/
inductive Term : Ty → Type where
  | var   : ∀ {τ}, Nat → Term τ
  | lam   : ∀ {α β}, Term β → Term (Ty.arrow α β)
  | app   : ∀ {α β}, Term (Ty.arrow α β) → Term α → Term β
  | pair  : ∀ {α β}, Term α → Term β → Term (Ty.prod α β)
  | fst   : ∀ {α β}, Term (Ty.prod α β) → Term α
  | snd   : ∀ {α β}, Term (Ty.prod α β) → Term β
  | inl   : ∀ {α β}, Term α → Term (Ty.sum α β)
  | inr   : ∀ {α β}, Term β → Term (Ty.sum α β)
  | matchSum
      : ∀ {α β γ},
        Term (Ty.sum α β) →
        Term γ →
        Term γ →
        Term γ
  | const : ∀ {τ}, String → Term τ
  deriving Repr

namespace Term

/-- Helper for shifting indices (classic de Bruijn weakening). -/
private def shiftIndex (cutoff inc idx : Nat) : Nat :=
  if idx ≥ cutoff then idx + inc else idx

/-- Shift all free indices greater-or-equal than `cutoff` by `inc`. -/
def shift : ∀ {τ}, Term τ → Nat → Nat → Term τ
  | _, var i, c, d => var (shiftIndex c d i)
  | _, lam body, c, d => lam (shift body (c + 1) d)
  | _, app f x, c, d => app (shift f c d) (shift x c d)
  | _, pair t₁ t₂, c, d => pair (shift t₁ c d) (shift t₂ c d)
  | _, fst t, c, d => fst (shift t c d)
  | _, snd t, c, d => snd (shift t c d)
  | _, inl t, c, d => inl (shift t c d)
  | _, inr t, c, d => inr (shift t c d)
  | _, matchSum s k₁ k₂, c, d =>
      matchSum (shift s c d) (shift k₁ c d) (shift k₂ c d)
  | _, const n, _, _ => const n

/-- Classic weakening: raise all free indices. -/
def weaken {τ} (t : Term τ) : Term τ :=
  shift t 0 1

end Term

end LeanCore
end HeytingLean
