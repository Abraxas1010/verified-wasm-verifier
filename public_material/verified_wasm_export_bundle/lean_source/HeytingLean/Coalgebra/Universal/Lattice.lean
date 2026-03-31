/-!
# Universal coalgebra — greatest fixed points for relations

We define the greatest fixed point of a monotone operator on binary relations.

This is used to define “greatest bisimulation” relations in a constructive way:
the greatest fixed point is implemented as the union of all post-fixed points.
-/

namespace HeytingLean
namespace Coalgebra
namespace Universal

universe u v

/-- Binary relations `α → β → Prop`. -/
abbrev Rel (α : Type u) (β : Type v) : Type (max u v) :=
  α → β → Prop

/-- Pointwise implication between relations. -/
def RelLe {α : Type u} {β : Type v} (R S : Rel α β) : Prop :=
  ∀ a b, R a b → S a b

infix:50 " ≤ᵣ " => RelLe

/-- A relation transformer is monotone if it preserves `≤ᵣ`. -/
def RelMonotone {α : Type u} {β : Type v} (Φ : Rel α β → Rel α β) : Prop :=
  ∀ {R S : Rel α β}, R ≤ᵣ S → Φ R ≤ᵣ Φ S

/-- Post-fixed point: `R ≤ᵣ Φ R`. -/
def PostFixed {α : Type u} {β : Type v} (Φ : Rel α β → Rel α β) (R : Rel α β) : Prop :=
  R ≤ᵣ Φ R

/-- Greatest fixed point as the union of all post-fixed points. -/
def gfp {α : Type u} {β : Type v} (Φ : Rel α β → Rel α β) : Rel α β :=
  fun a b => ∃ R : Rel α β, PostFixed Φ R ∧ R a b

theorem gfp_intro {α : Type u} {β : Type v} {Φ : Rel α β → Rel α β}
    {R : Rel α β} (hR : PostFixed Φ R) {a : α} {b : β} (h : R a b) :
    gfp Φ a b :=
  ⟨R, hR, h⟩

theorem gfp_isGreatest {α : Type u} {β : Type v} {Φ : Rel α β → Rel α β}
    {R : Rel α β} (hR : PostFixed Φ R) :
    R ≤ᵣ gfp Φ := by
  intro a b hab
  exact gfp_intro (Φ := Φ) hR hab

theorem gfp_postFixed {α : Type u} {β : Type v} {Φ : Rel α β → Rel α β}
    (hmono : RelMonotone (α := α) (β := β) Φ) :
    PostFixed Φ (gfp Φ) := by
  intro a b hab
  rcases hab with ⟨R, hR, hab⟩
  have : Φ R a b := hR a b hab
  -- Monotonicity gives `Φ R ≤ Φ (gfp Φ)` since `R ≤ gfp Φ`.
  have hle : R ≤ᵣ gfp Φ := gfp_isGreatest (Φ := Φ) hR
  exact (hmono hle) a b this

theorem gfp_fixed {α : Type u} {β : Type v} {Φ : Rel α β → Rel α β}
    (hmono : RelMonotone (α := α) (β := β) Φ) :
    (∀ a b, Φ (gfp Φ) a b ↔ gfp Φ a b) := by
  intro a b
  constructor
  · intro hΦ
    -- Show `Φ (gfp Φ)` is post-fixed, then use maximality.
    have hPost : PostFixed Φ (Φ (gfp Φ)) := by
      intro a' b' h'
      -- Apply monotonicity to `gfp Φ ≤ Φ (gfp Φ)`.
      have hle : gfp Φ ≤ᵣ Φ (gfp Φ) := gfp_postFixed (Φ := Φ) hmono
      exact (hmono hle) a' b' h'
    have : Φ (gfp Φ) ≤ᵣ gfp Φ := gfp_isGreatest (Φ := Φ) hPost
    exact this a b hΦ
  · intro h
    exact (gfp_postFixed (Φ := Φ) hmono) a b h
