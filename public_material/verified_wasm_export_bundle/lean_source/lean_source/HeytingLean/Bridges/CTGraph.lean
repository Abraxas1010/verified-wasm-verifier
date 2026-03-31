import HeytingLean.Constructor.CT.Core
import HeytingLean.Constructor.CT.Nucleus
import HeytingLean.Bridges.Graph

/-
# CT ↔ Graph bridge (minimal scaffold)

Tiny bridge from Constructor Theory tasks to the existing graph model:
* for a fixed CT nucleus `J` on tasks over `σ`, we define a graph-model
  style carrier given by the CT fixed-point algebra `Ω_{J_CT}`;
* provide a trivial encoding from CT tasks into this carrier by sending
  a task `T` to the singleton `{T}` closed under `J`;
* expose a simple adjacency relation where two CT task-sets are related
  when they are ordered by subset.

This is intentionally lightweight; richer connections to the full
`Bridges.Graph.Alexandroff` machinery can be added as the CT layer
evolves.
-/

namespace HeytingLean
namespace Bridges
namespace CTGraph

open Constructor
open Constructor.CT

universe u

variable {σ : Type u}

/-- Minimal CT graph model: carrier is the CT fixed-point algebra
`Ω_{J_CT}` on sets of tasks. -/
structure Model (σ : Type u) where
  J : CTNucleus σ

namespace Model

variable (M : Model σ)

/-! We view `Omega J` as the type of fixed points of the nucleus
`J.toNucleus` on `Set (CT.Task σ)`, following the `Nucleus.toSublocale`
construction in Mathlib. -/

/-- Carrier of the CT graph model: CT nucleus fixed points. -/
abbrev Carrier (M : Model σ) : Type u :=
  Omega M.J

/-!  We treat `Omega M.J` as the fixed points of the Mathlib nucleus
`M.J.toNucleus` on `Set (CT.Task σ)`, so inhabitants consist of a set
of tasks together with a proof that it is stable under `J`. -/

/-- Trivial encoding of a CT task as the least CT-closed family
containing it, represented as the CT nucleus applied to the singleton. -/
def encode (T : CT.Task σ) : Carrier M :=
  ⟨M.J.J {T}, by
    -- Show that `M.J.J {T}` lies in the range of `toNucleus`.
    change ∃ Y, CTNucleus.toNucleus (σ := σ) M.J Y = M.J.J {T}
    refine ⟨M.J.J {T}, ?_⟩
    -- `toNucleus` is defined by `toFun := J`; use idempotence.
    simp [CTNucleus.toNucleus, CTNucleus.idempotent]⟩

/-- Simple adjacency relation on CT task-sets: subset ordering. -/
def adjacency (A B : Carrier M) : Prop :=
  (A : Set (CT.Task σ)) ⊆ (B : Set (CT.Task σ))

@[simp] lemma adjacency_refl (A : Carrier M) :
    adjacency M A A := by
  intro T hT; exact hT

@[simp] lemma adjacency_trans {A B C : Carrier M}
    (hAB : adjacency M A B) (hBC : adjacency M B C) :
    adjacency M A C := by
  intro T hT
  exact hBC (hAB hT)

end Model

end CTGraph
end Bridges
end HeytingLean
