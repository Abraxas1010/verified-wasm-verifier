import HeytingLean.Bridges.Nucleus.Extensions.DragalinFrame
import HeytingLean.Bridges.JRatchet.JRatchetCore

/-!
# DragalinRatchet

This module connects Dragalin-frame path growth to ratchet witnesses,
following Bezhanishvili-Holliday (2016) style path semantics.
-/

namespace HeytingLean
namespace Bridges
namespace JRatchet
namespace Extensions
namespace DragalinRatchet

open HeytingLean.Bridges.Nucleus.Extensions

universe u

/-- A ratchet witness generated from Dragalin-frame path-depth growth. -/
structure DragalinRatchetWitness (α : Type u) where
  /-- Underlying Dragalin frame. -/
  frame : DragalinFrame α
  /-- Distinguished origin for trajectory interpretation. -/
  origin : α
  /-- Fuel-indexed path-depth measure. -/
  pathLength : Nat → Nat
  /-- Monotonicity of the path-depth trajectory. -/
  pathLength_monotone : HeytingLean.Topos.JRatchet.RatchetTrajectory pathLength

/-- Convert Dragalin witness data to the unified `RatchetWitness` interface. -/
def dragalinToWitness {α : Type u} (D : DragalinRatchetWitness α) :
    HeytingLean.Bridges.JRatchet.RatchetWitness where
  level := D.pathLength
  monotone := D.pathLength_monotone

/-- A path-extension ratchet step on Dragalin frames. -/
structure DragalinRatchetStep (α : Type u) where
  /-- Path-extension action. -/
  extendPaths : DragalinFrame α → DragalinFrame α
  /-- Existing paths are preserved (irreversibility). -/
  paths_grow : ∀ F : DragalinFrame α, ∀ x y : α,
      F.Path x y → (extendPaths F).Path x y
  /-- Core elements are preserved under extension. -/
  core_stable : ∀ F : DragalinFrame α, F.core ⊆ (extendPaths F).core

/-- Generated cores grow monotonically under Dragalin path-extension steps. -/
theorem dragalinRatchetStep_monotone_on_nuclei
    {α : Type u} (D : DragalinRatchetStep α) (F : DragalinFrame α) :
    DragalinFrame.generatedCore F ⊆ DragalinFrame.generatedCore (D.extendPaths F) := by
  intro x hx
  rcases hx with ⟨y, hyCore, hPath⟩
  exact ⟨y, D.core_stable F hyCore, D.paths_grow F x y hPath⟩

/-- Path irreversibility lemma: once present, paths cannot be removed by the ratchet step. -/
theorem dragalinPathIrreversibility
    {α : Type u} (D : DragalinRatchetStep α) (F : DragalinFrame α)
    {x y : α} (hxy : F.Path x y) :
    (D.extendPaths F).Path x y :=
  D.paths_grow F x y hxy

end DragalinRatchet
end Extensions
end JRatchet
end Bridges
end HeytingLean
