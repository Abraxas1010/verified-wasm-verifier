import HeytingLean.Metrics.Magnitude.HomologyGroups

namespace HeytingLean
namespace Tests
namespace Archetype

open Metrics.Magnitude

example (n : Nat) (f : MagnitudeChain Bool (n + 1) → ℤ)
    (hf : f ∈ magnitudeBoundaries (α := Bool) n) :
    f ∈ magnitudeCycles (α := Bool) n := by
  exact boundary_subset_cycles (α := Bool) n hf

example : bettiFromComplex boolMagnitudeComplexF2 0 = 1 := by
  native_decide

example : bettiFromComplex boolMagnitudeComplexF2 1 = 0 := by
  native_decide

example : bettiFromComplex boolMagnitudeComplexF2 2 = 0 := by
  native_decide

example : bettiFromComplex fin3MagnitudeComplexF2 0 = 1 := by
  native_decide

example : bettiFromComplex fin3MagnitudeComplexF2 1 = 0 := by
  native_decide

example : bettiFromComplex fin3MagnitudeComplexF2 2 = 0 := by
  native_decide

end Archetype
end Tests
end HeytingLean
