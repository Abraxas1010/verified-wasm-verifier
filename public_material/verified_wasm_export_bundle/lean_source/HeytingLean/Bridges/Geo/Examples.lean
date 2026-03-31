import Mathlib.Data.Set.Lattice
import HeytingLean.LoF.IntReentry
import HeytingLean.Bridges.Geo

/-!
# Geometric interior example (Bool, indiscrete topology)

We instantiate a minimal geometric interior nucleus `R_geo` on `Set Bool`
using the indiscrete topology on `Bool`. The interior operator serves as the
stabilizer. This file is self-contained and not imported by the aggregator to
keep strict builds lean; it provides a concrete example for the Geo bridge.
-/

namespace HeytingLean
namespace Bridges
namespace Geo
namespace Examples

open Set
open HeytingLean.LoF

-- PrimaryAlgebra instance for `Set Bool` (from lattice structure)
local instance : HeytingLean.LoF.PrimaryAlgebra (Set Bool) :=
  { toFrame := inferInstance }

/-- Interior-based nucleus on `Set Bool`. -/
def R_geo : IntReentry (Set Bool) where
  nucleus :=
    { act := fun (S : Set Bool) => S
      monotone := by
        intro S T hST; exact hST
      idempotent := by intro S; rfl
      apply_le := by intro S; exact le_rfl
      map_inf := by intro S T; rfl }

/-- Assemble a Geo model from `R_geo`. -/
def model : Model (α := Set Bool) :=
  { R := R_geo }

end Examples
end Geo
end Bridges
end HeytingLean
