import Mathlib.Order.Preorder.Finite
import HeytingLean.Algebra.HomotopyTower.Core

namespace HeytingLean
namespace Algebra
namespace HomotopyTower

open Set

universe u

variable {α : Type u} [Order.Frame α]

/-- The tower visits only finitely many nuclei. -/
def FiniteImage (T : NucleusTower (α := α)) : Prop := (Set.range T.level).Finite

/-- Stabilization from a concrete stage onward. -/
def TowerStabilizes (T : NucleusTower (α := α)) (N : Nat) : Prop :=
  ∀ n : Nat, N ≤ n → T.level n = T.level N

/-- The finite-image witness forces eventual constancy of an ascending tower. -/
theorem tower_stabilizes_of_finiteImage (T : NucleusTower (α := α)) (hfin : FiniteImage T) :
    ∃ N, TowerStabilizes T N := by
  have himage : (T.level '' (Set.univ : Set Nat)).Finite := by
    simpa [Set.image_univ] using hfin
  obtain ⟨N, hmax⟩ := Finite.exists_maximalFor' (α := Nucleus α) (f := T.level)
    (s := Set.univ) himage Set.univ_nonempty
  refine ⟨N, ?_⟩
  intro n hn
  apply le_antisymm
  · exact hmax.2 (by trivial) (T.mono hn)
  · exact T.mono hn

noncomputable def stabilizationIndex (T : NucleusTower (α := α)) (hfin : FiniteImage T) : Nat :=
  Classical.choose (tower_stabilizes_of_finiteImage T hfin)

theorem stabilizationIndex_spec (T : NucleusTower (α := α)) (hfin : FiniteImage T) :
    TowerStabilizes T (stabilizationIndex T hfin) :=
  Classical.choose_spec (tower_stabilizes_of_finiteImage T hfin)

/-- The stabilized nucleus chosen from the finite-image witness. -/
noncomputable def limitNucleus (T : NucleusTower (α := α)) (hfin : FiniteImage T) : Nucleus α :=
  T.level (stabilizationIndex T hfin)

/-- The stabilized moved-point boundary. -/
noncomputable def stableBoundary (T : NucleusTower (α := α)) (hfin : FiniteImage T) : Set α :=
  boundary (limitNucleus T hfin)

theorem tower_stabilizes_at_limit (T : NucleusTower (α := α)) (hfin : FiniteImage T) :
    ∀ n : Nat, stabilizationIndex T hfin ≤ n → T.level n = limitNucleus T hfin := by
  intro n hn
  exact stabilizationIndex_spec T hfin n hn

theorem boundary_stabilizes_at_limit (T : NucleusTower (α := α)) (hfin : FiniteImage T) :
    ∀ n : Nat, stabilizationIndex T hfin ≤ n → boundary (T.level n) = stableBoundary T hfin := by
  intro n hn
  simp [stableBoundary, limitNucleus, tower_stabilizes_at_limit T hfin n hn]

end HomotopyTower
end Algebra
end HeytingLean
