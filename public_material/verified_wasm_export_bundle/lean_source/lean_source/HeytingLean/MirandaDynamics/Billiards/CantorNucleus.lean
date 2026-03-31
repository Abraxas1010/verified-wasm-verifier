import Mathlib.Topology.Instances.CantorSet
import HeytingLean.MirandaDynamics.FixedPoint.PeriodicNucleus

/-!
# MirandaDynamics.Billiards: Cantor nucleus (inflationary)

The closure-operator/nucleus convention in this repo follows `Mathlib.Order.Nucleus`:

* inflationary,
* idempotent,
* inf-preserving.

For a fixed closed set `C ⊆ ℝ`, the standard nucleus for the **closed sublocale** determined by `C`
is the “union with complement” operator

`R_C(S) := S ∪ Cᶜ`.

Fixed points are exactly the supersets of `Cᶜ`, i.e. the sets “forced to contain the outside”.
For the Cantor set `cantorSet`, this models the idea of “working relative to Cantor data” without
using topological closure (which generally does not preserve `inf`).
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

open Set

/-- The complement of the ternary Cantor set. -/
def cantorCompl : Set ℝ :=
  cantorSetᶜ

/-- The Cantor nucleus on `Set ℝ`: `S ↦ S ∪ cantorSetᶜ`. -/
def cantorNucleus : Nucleus (Set ℝ) :=
  MirandaDynamics.FixedPoint.unionNucleus (α := ℝ) cantorCompl

theorem cantorNucleus_fixed_iff (S : Set ℝ) :
    cantorNucleus S = S ↔ cantorCompl ⊆ S := by
  simpa [cantorNucleus, cantorCompl] using
    (MirandaDynamics.FixedPoint.isFixedPoint_unionNucleus_iff (α := ℝ) cantorCompl S)

end Billiards
end MirandaDynamics
end HeytingLean

