import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Lattice
-- Analytic hull (Moore family) is specified in the plan doc; this minimal
-- nucleus and its general lemmas are provided here to keep strict builds fast.

/-!
Calculus Lens (Phase 1)

Lightweight nucleus-style scaffolding for function spaces. This pass
keeps proofs minimal (no analysis-heavy imports) and provides a very
simple instance where the operator is the identity, so that we can
wire the API without slowing strict builds.
-/

namespace HeytingLean
namespace Calculus

open Set

universe u

/-- Minimal nucleus-style record used by the calculus lens. -/
structure CalculusNucleus (α : Type u) [CompleteLattice α] where
  R : α → α
  extensive   : ∀ a, a ≤ R a
  idempotent  : ∀ a, R (R a) = R a
  map_inf     : ∀ a b, R (a ⊓ b) = R a ⊓ R b

namespace CalculusNucleus

variable {α : Type u} [CompleteLattice α]

/-- Fixed points (the analytic "Ω"). -/
def Omega (N : CalculusNucleus α) : Set α := {a | N.R a = a}

@[simp] lemma mem_Omega {N : CalculusNucleus α} {a : α} :
    a ∈ N.Omega ↔ N.R a = a := Iff.rfl

@[simp] lemma R_id_of_mem {N : CalculusNucleus α} {a : α}
    (h : a ∈ N.Omega) : N.R a = a := h

@[simp] lemma le_R (N : CalculusNucleus α) (a : α) : a ≤ N.R a :=
  N.extensive a

@[simp] lemma R_idem (N : CalculusNucleus α) (a : α) : N.R (N.R a) = N.R a :=
  N.idempotent a

lemma monotone_R (N : CalculusNucleus α) : Monotone N.R := by
  intro a b h
  have h': a ⊓ b = a := inf_eq_left.mpr h
  have hmap : N.R (a ⊓ b) = N.R a ⊓ N.R b := N.map_inf a b
  have hEq : N.R a = N.R a ⊓ N.R b := by simpa [h'] using hmap
  have hEq' : N.R a ⊓ N.R b = N.R a := hEq.symm
  exact (inf_eq_left.mp hEq')

lemma omega_inf_closed {N : CalculusNucleus α} {a b : α}
    (ha : a ∈ N.Omega) (hb : b ∈ N.Omega) : (a ⊓ b) ∈ N.Omega := by
  -- Show N.R (a ⊓ b) = a ⊓ b
  have hmap : N.R (a ⊓ b) = N.R a ⊓ N.R b := N.map_inf a b
  have : N.R (a ⊓ b) = a ⊓ b := by simpa [ha, hb]
    using hmap
  exact this

end CalculusNucleus

/-! ### A minimal instance: identity operator on `Set (ℝ → ℝ)` -/

namespace Instances

@[simp] def smoothClosureId : CalculusNucleus (Set (ℝ → ℝ)) where
  R := id
  extensive := by intro a; exact le_of_eq rfl
  idempotent := by intro a; rfl
  map_inf := by intro a b; rfl

@[simp] lemma smoothClosureId_fix (S : Set (ℝ → ℝ)) :
    smoothClosureId.R S = S := rfl

@[simp] lemma smoothClosureId_all_fixed (S : Set (ℝ → ℝ)) :
    S ∈ (smoothClosureId).Omega := by
  change smoothClosureId.R S = S
  simp

end Instances

/-! ### Analytic Hull nucleus (spec-level) -/

-- Note: We expose analyticHull and its properties from AnalyticHull.

end Calculus
end HeytingLean
