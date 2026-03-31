import HeytingLean.Representations.Radial.Core
import Mathlib.Data.Nat.Dist

/-!
# Radial distances (scaffold)

The “radial distance” is the absolute ring-distance between states.

This file also defines a `stepDistance` hook. In the initial scaffold, `stepDistance` is defined
to be `radialDistance` so theorems are executable and total; later work can replace it with a
graph-theoretic shortest-path distance derived from a concrete transition matrix.
-/

namespace HeytingLean
namespace Representations
namespace Radial
namespace Distance

open HeytingLean.Representations.Radial

variable {G : RadialGraph}

def radialDistance (G : RadialGraph) (s t : G.StateIdx) : Nat :=
  Nat.dist (G.assemblyIndex s) (G.assemblyIndex t)

/-- Hook for the “true” step distance; initially identical to `radialDistance`. -/
def stepDistance (G : RadialGraph) (s t : G.StateIdx) : Nat :=
  radialDistance G s t

theorem radial_le_step (G : RadialGraph) (s t : G.StateIdx) :
    radialDistance G s t ≤ stepDistance G s t := by
  simp [stepDistance]

def distanceFromR (G : RadialGraph) (s : G.StateIdx) : Nat :=
  radialDistance G (G.ring0State) s

theorem distanceFromR_eq_assembly (G : RadialGraph) (s : G.StateIdx) :
    distanceFromR G s = G.assemblyIndex s := by
  have h0' : (G.ringOf (G.ring0State)).val = (G.ring0Idx).val :=
    congrArg Fin.val (G.ringOf_ring0State)
  have h0 : G.assemblyIndex (G.ring0State) = 0 := by
    simpa [RadialGraph.assemblyIndex, RadialGraph.ring0Idx] using h0'
  simp [distanceFromR, radialDistance, h0, Nat.dist_zero_left]

theorem stepDistance_eq_radial (G : RadialGraph) (s t : G.StateIdx) :
    stepDistance G s t = radialDistance G s t := rfl

end Distance
end Radial
end Representations
end HeytingLean

