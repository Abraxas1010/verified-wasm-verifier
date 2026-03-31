import Mathlib.Data.Set.Image
import Mathlib.Order.CompleteLattice.Basic

/-!
# CPP weakness functional

This module defines the algebraic core of the CPP-style “weakness” functional:

`w(H, μ) = sSup { μ u ⊗ μ v | (u,v) ∈ H }`

We keep it polymorphic over a complete lattice `V` equipped with a binary operation `(*)`.
No quantale-specific distributivity assumptions are required for the basic API below.
-/

namespace HeytingLean
namespace CPP

universe u v

/-- CPP-style weakness: supremum of `μ u * μ v` over pairs in an indistinction relation `H`. -/
def weakness {U : Type u} {V : Type v} [CompleteLattice V] [Mul V]
    (H : Set (U × U)) (μ : U → V) : V :=
  sSup ((fun p : U × U => μ p.1 * μ p.2) '' H)

theorem weakness_mono_rel {U : Type u} {V : Type v} [CompleteLattice V] [Mul V]
    {H H' : Set (U × U)} {μ : U → V} (h : H ⊆ H') :
    weakness H μ ≤ weakness H' μ := by
  unfold weakness
  refine sSup_le_sSup ?_
  intro x hx
  rcases hx with ⟨p, hp, rfl⟩
  exact ⟨p, h hp, rfl⟩

@[simp] lemma weakness_empty {U : Type u} {V : Type v} [CompleteLattice V] [Mul V]
    (μ : U → V) :
    weakness (∅ : Set (U × U)) μ = (⊥ : V) := by
  simp [weakness]

theorem mul_le_weakness {U : Type u} {V : Type v} [CompleteLattice V] [Mul V]
    {H : Set (U × U)} {μ : U → V} {u v : U} (h : (u, v) ∈ H) :
    μ u * μ v ≤ weakness H μ := by
  unfold weakness
  refine le_sSup ?_
  exact ⟨(u, v), h, rfl⟩

theorem weakness_union {U : Type u} {V : Type v} [CompleteLattice V] [Mul V]
    (H₁ H₂ : Set (U × U)) (μ : U → V) :
    weakness (H₁ ∪ H₂) μ = weakness H₁ μ ⊔ weakness H₂ μ := by
  unfold weakness
  simp [Set.image_union, sSup_union]

end CPP
end HeytingLean
