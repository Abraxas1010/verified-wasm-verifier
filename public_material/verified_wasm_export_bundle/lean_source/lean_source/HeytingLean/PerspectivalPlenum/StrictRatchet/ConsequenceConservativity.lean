import HeytingLean.PerspectivalPlenum.StrictRatchet.Conservativity

namespace HeytingLean
namespace PerspectivalPlenum
namespace StrictRatchet

universe u v

/--
Consequence-level conservativity contract.

This lifts fragment conservativity from formula-level predicates to
context-sensitive consequence relations over mapped contexts.
-/
structure ConsequenceConservativeTranslation (Src : Type u) (Tgt : Type v) where
  translate : Src → Tgt
  DerivesSrc : List Src → Src → Prop
  DerivesTgt : List Tgt → Tgt → Prop
  sound : ∀ {Γ : List Src} {φ : Src}, DerivesSrc Γ φ → DerivesTgt (Γ.map translate) (translate φ)
  conservative : ∀ {Γ : List Src} {φ : Src}, DerivesTgt (Γ.map translate) (translate φ) → DerivesSrc Γ φ

namespace ConsequenceConservativeTranslation

/--
Canonical lift of a formula-level conservative translation to a
context-sensitive consequence relation.
-/
def fromFormulaTranslation
    {Src : Type u} {Tgt : Type v}
    (T : ConservativeTranslation Src Tgt) :
    ConsequenceConservativeTranslation Src Tgt where
  translate := T.translate
  DerivesSrc := fun Γ φ => (∀ ψ, ψ ∈ Γ → T.ProvableSrc ψ) → T.ProvableSrc φ
  DerivesTgt := fun Δ χ => (∀ ξ, ξ ∈ Δ → T.ProvableTgt ξ) → T.ProvableTgt χ
  sound := by
    intro Γ φ hDer hMapped
    apply T.sound
    apply hDer
    intro ψ hψ
    apply T.conservative
    exact hMapped (T.translate ψ) (by
      exact List.mem_map.mpr ⟨ψ, hψ, rfl⟩)
  conservative := by
    intro Γ φ hDerT hΓ
    apply T.conservative
    apply hDerT
    intro ξ hξ
    rcases List.mem_map.mp hξ with ⟨ψ, hψ, rfl⟩
    exact T.sound (hΓ ψ hψ)

/-- Consequence-level iff for the mapped context. -/
theorem iff_for_mapped
    {Src : Type u} {Tgt : Type v}
    (T : ConsequenceConservativeTranslation Src Tgt)
    (Γ : List Src) (φ : Src) :
    T.DerivesSrc Γ φ ↔ T.DerivesTgt (Γ.map T.translate) (T.translate φ) := by
  exact ⟨T.sound, T.conservative⟩

namespace DoubleNegationLane

open ConservativeTranslation.DoubleNegationLane

variable (α : Type u) [HeytingAlgebra α]

/-- Context-level conservative translation for the double-negation classical-core lane. -/
def translationCtx :
    ConsequenceConservativeTranslation (Core α) α :=
  fromFormulaTranslation (translation α)

theorem conservativityCtx_exact
    (Γ : List (Core α)) (φ : Core α) :
    (translationCtx α).DerivesSrc Γ φ
      ↔ (translationCtx α).DerivesTgt
          (Γ.map (translationCtx α).translate)
          ((translationCtx α).translate φ) := by
  exact iff_for_mapped (translationCtx α) Γ φ

/-- Formula-level conservativity is recovered as the empty-context special case. -/
theorem formula_level_as_empty_context
    (φ : Core α) :
    (translation α).ProvableSrc φ
      ↔ (translationCtx α).DerivesSrc [] φ := by
  constructor
  · intro hφ _h
    exact hφ
  · intro hDer
    exact hDer (by
      intro ψ hψ
      cases hψ)

end DoubleNegationLane

end ConsequenceConservativeTranslation

end StrictRatchet
end PerspectivalPlenum
end HeytingLean
