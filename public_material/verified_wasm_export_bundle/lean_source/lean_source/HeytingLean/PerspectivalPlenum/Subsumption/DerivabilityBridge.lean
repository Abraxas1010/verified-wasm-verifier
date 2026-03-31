import HeytingLean.Noneism.Syntax
import HeytingLean.PerspectivalPlenum.Subsumption.NoneismAdapter

namespace HeytingLean
namespace PerspectivalPlenum
namespace Subsumption

open Noneism

/--
Interface bridge: keep a noneist derivability relation while interpreting semantic consequences
through a chosen lens adapter.
-/
abbrev Ctx (σ : Type) := Formula σ → Prop

structure DerivabilityBridge (σ : Type) where
  Derives : Ctx σ → Formula σ → Prop
  sound_local : ∀ {Γ : Ctx σ} {φ : Formula σ}
    (_hDer : Derives Γ φ)
    (A : NoneismLensAdapter σ),
    (∀ ψ, Γ ψ → A.interpretedClaim ψ) →
      A.interpretedClaim φ

namespace DerivabilityBridge

variable {σ : Type}

/-- Transport a derivation into lens-local satisfiability via bridge soundness. -/
theorem derivable_to_local_claim
    (B : DerivabilityBridge σ)
    {Γ : Ctx σ} {φ : Formula σ}
    (hDer : B.Derives Γ φ)
    (A : NoneismLensAdapter σ)
    (hΓ : ∀ ψ, Γ ψ → A.interpretedClaim ψ) :
    A.interpretedClaim φ :=
  B.sound_local hDer A hΓ

/--
If `⊥` is derivable in context and a strict lens marks `⊥` contradictory,
then `⊥` collapses in that lens under the subsumed semantics.
-/
theorem collapse_bottom_of_derivable_bottom
    (B : DerivabilityBridge σ)
    {Γ : Ctx σ}
    (hDerBot : B.Derives Γ (.bot : Formula σ))
    (A : NoneismLensAdapter σ)
    (hΓ : ∀ ψ, Γ ψ → A.interpretedClaim ψ)
    (hStrict : ¬ Lens.allowsContradictions A.lens.profile)
    (hBotContra : A.lens.contradicts (.bot : Formula σ)) :
    A.interpretedImpossible (.bot : Formula σ) := by
  have hBotClaim : A.interpretedClaim (.bot : Formula σ) :=
    derivable_to_local_claim B hDerBot A hΓ
  exact Lens.collapse_of_strict_contradiction A.lens (.bot : Formula σ)
    hStrict hBotClaim.1 hBotContra

end DerivabilityBridge

end Subsumption
end PerspectivalPlenum
end HeytingLean
