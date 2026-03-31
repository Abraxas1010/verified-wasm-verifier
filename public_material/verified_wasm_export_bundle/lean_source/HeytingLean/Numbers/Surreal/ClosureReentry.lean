import Mathlib.Order.Nucleus
import Mathlib.Order.Sublocale
import Mathlib.Data.Set.Lattice
import HeytingLean.LoF.PrimaryAlgebra
import HeytingLean.Numbers.Surreal.Nucleus
import HeytingLean.Numbers.SurrealCore

/-!
# Surreal Closure Reentry (Option A)

A meet‑preserving closure nucleus on `Set PreGame` built by adjoining the
canonical legal core `Int.C`. Its fixed points form a Heyting algebra via
mathlib’s sublocale machinery. We also expose a minimal Reentry‑style wrapper
that only carries the underlying `Nucleus`.
-/

namespace HeytingLean
namespace Numbers
namespace Surreal

open Set
open HeytingLean.Numbers
open HeytingLean.Numbers.SurrealCore

/-! ### Core nucleus: `R(S) = S ∪ Int.C` on `Set PreGame` -/

-- Canonical legal core for Surreal pre‑games (replicated here to avoid extra deps).
def canonicalCore : Set SurrealCore.PreGame :=
  { g | SurrealCore.legal g ∧ SurrealCore.canonicalize g = g }

def closureCore : Nucleus (Set SurrealCore.PreGame) where
  toFun S := S ∪ canonicalCore
  le_apply' := by
    intro S; exact subset_union_left
  idempotent' := by
    intro S x hx
    rcases hx with hx | hC
    · -- x ∈ (S ∪ C) implies x ∈ S ∪ C
      exact hx
    · -- x ∈ C also lies in S ∪ C
      exact Or.inr hC
  map_inf' := by
    intro S T; ext x; constructor
    · intro hx
      rcases hx with hx | hC
      · rcases hx with ⟨hS, hT⟩
        exact And.intro (Or.inl hS) (Or.inl hT)
      · exact And.intro (Or.inr hC) (Or.inr hC)
    · intro hx
      rcases hx with ⟨h1, h2⟩
      cases h1 with
      | inl hS =>
        cases h2 with
        | inl hT => exact Or.inl ⟨hS, hT⟩
        | inr hC => exact Or.inr hC
      | inr hC => exact Or.inr hC

/-! ### Minimal Reentry‑style wrapper (axioms relaxed) -/

structure ClosureReentry (α : Type u) [HeytingLean.LoF.PrimaryAlgebra α] where
  nucleus : Nucleus α

namespace ClosureReentry

variable {α : Type u} [HeytingLean.LoF.PrimaryAlgebra α]

instance : CoeFun (ClosureReentry α) (fun _ => α → α) where
  coe R := R.nucleus

-- Fixed points of the nucleus (`Ω_R`) inherit a Heyting algebra.
abbrev Omega (R : ClosureReentry α) : Type u := R.nucleus.toSublocale

instance (R : ClosureReentry α) : HeytingAlgebra (R.Omega) := inferInstance

end ClosureReentry

/-! ### Surreal specializations -/

-- Package the closure nucleus as a `ClosureReentry` on `Set PreGame`.
def surrealClosureReentry : ClosureReentry (Set SurrealCore.PreGame) :=
  ⟨closureCore⟩

@[simp] def Ω_closure : Type _ := (surrealClosureReentry).Omega

end Surreal
end Numbers
end HeytingLean
