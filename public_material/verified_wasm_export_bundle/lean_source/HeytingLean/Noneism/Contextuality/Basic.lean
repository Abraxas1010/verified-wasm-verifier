import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Basic

namespace HeytingLean
namespace Noneism
namespace Contextuality

abbrev Context (M : Type u) := Finset M

abbrev LocalAssign {M : Type u} (C : Context M) (O : Type v) := {m // m ∈ C} → O

/-- Restrict a global assignment to a finite context. -/
def restrict {M : Type u} {O : Type v} (g : M → O) (C : Context M) : LocalAssign C O :=
  fun m => g m.1

/-- Finite contextuality scenario: contexts plus admissible local sections. -/
structure Scenario (M : Type u) (O : Type v) [Fintype M] [DecidableEq M] where
  cover : Finset (Context M)
  covers_all : ∀ m : M, ∃ C ∈ cover, m ∈ C
  Allowed : ∀ C : Context M, LocalAssign C O → Prop

/-- A global section is an assignment whose restriction is allowed on each context in the cover. -/
def IsGlobalSection {M : Type u} {O : Type v} [Fintype M] [DecidableEq M]
    (S : Scenario M O) (g : M → O) : Prop :=
  ∀ C ∈ S.cover, S.Allowed C (restrict g C)

/-- Contextual means no global section exists. -/
def Contextual {M : Type u} {O : Type v} [Fintype M] [DecidableEq M]
    (S : Scenario M O) : Prop :=
  ¬ ∃ g : M → O, IsGlobalSection S g

theorem IsGlobalSection.ext {M : Type u} {O : Type v} [Fintype M] [DecidableEq M]
    {S : Scenario M O} {g₁ g₂ : M → O} (hg : g₁ = g₂) :
    IsGlobalSection S g₁ ↔ IsGlobalSection S g₂ := by
  cases hg
  simp [IsGlobalSection]

theorem restrict_agree_on_overlap {M : Type u} {O : Type v}
    {g : M → O} {C D : Context M} {x : M}
    (hxC : x ∈ C) (hxD : x ∈ D) :
    restrict g C ⟨x, hxC⟩ = restrict g D ⟨x, hxD⟩ := rfl

end Contextuality
end Noneism
end HeytingLean
