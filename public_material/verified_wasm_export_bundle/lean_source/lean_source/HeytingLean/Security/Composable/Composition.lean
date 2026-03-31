import HeytingLean.Security.Composable.UC

/-!
# Universal Composability (UC), interface-first: composition kit

We avoid asserting a global UC composition theorem. Instead we package whatever composition
machinery a future development chooses to provide as a structure.
-/

namespace HeytingLean
namespace Security
namespace Composable

universe u v w u' v' w'

/-- A minimal interface for stating a UC-style composition theorem. -/
structure CompositionKit
    (F₁ : IdealFunctionality.{u, v, w})
    (F₂ : IdealFunctionality.{u', v', w'}) where
  /-- A notion of using `F₁` as a subroutine (abstract). -/
  UsesSubroutine : Protocol F₂ → Prop
  /-- Protocol-level composition (abstract). -/
  compose : Protocol F₂ → Protocol F₁ → Protocol F₂
  /-- The composition theorem (provided as data, not as a global postulate). -/
  comp :
      ∀ {π₁ : Protocol F₁} {π₂ : Protocol F₂},
        UCSecure F₁ π₁ → UCSecure F₂ π₂ → UsesSubroutine π₂ → UCSecure F₂ (compose π₂ π₁)

def uc_composition
    {F₁ : IdealFunctionality.{u, v, w}}
    {F₂ : IdealFunctionality.{u', v', w'}}
    (kit : CompositionKit F₁ F₂)
    {π₁ : Protocol F₁} {π₂ : Protocol F₂}
    (h₁ : UCSecure F₁ π₁)
    (h₂ : UCSecure F₂ π₂)
    (h_uses : kit.UsesSubroutine π₂) :
    UCSecure F₂ (kit.compose π₂ π₁) :=
  kit.comp h₁ h₂ h_uses

end Composable
end Security
end HeytingLean
