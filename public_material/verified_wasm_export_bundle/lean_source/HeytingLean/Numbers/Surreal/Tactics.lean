import HeytingLean.Numbers.Surreal.BoundaryLogic
import HeytingLean.Numbers.Surreal.Operations

/-!
# Surreal.Tactics

SN-021 baseline: lightweight tactic wrappers for common Surreal/Noneist rewrites.
-/

namespace HeytingLean
namespace Numbers
namespace Surreal

open Lean Elab Tactic

/-- Boundary-focused simplification tactic for Noneist/bi-Heyting goals. -/
macro "noneist_simp" : tactic =>
  `(tactic| simp [
    HeytingLean.Numbers.Surreal.BoundaryOps.nonExistent,
    HeytingLean.Numbers.Surreal.BoundaryOps.impossible,
    HeytingLean.Numbers.Surreal.set_boundary_eq_empty,
    HeytingLean.Numbers.Surreal.set_boundary_eq_inter_compl,
    HeytingLean.Numbers.Surreal.set_nonExistent_all,
    HeytingLean.Numbers.Surreal.set_not_impossible
  ])

/-- Core Surreal simplification tactic for zero/normalization arithmetic shells. -/
macro "surreal_simp" : tactic =>
  `(tactic| simp [
    HeytingLean.Numbers.Surreal.addConway,
    HeytingLean.Numbers.Surreal.mulConway,
    HeytingLean.Numbers.Surreal.normalize,
    HeytingLean.Numbers.Surreal.zero
  ])

end Surreal
end Numbers
end HeytingLean
