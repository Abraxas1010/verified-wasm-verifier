import HeytingLean.Numbers.Surreal.ReentryFixedPoint

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Numbers.Surreal
open HeytingLean.Numbers.SurrealCore

example : step canonicalCore = canonicalCore := by
  exact canonicalCore_fixed

example : canonicalCore ∈ FixedPoints := by
  exact canonicalCore_mem_fixed

example : IsLeast FixedPoints canonicalCore := by
  exact canonicalCore_isLeast_fixed

example : oscillate (∅ : Carrier) = canonicalCoreᶜ := by
  simpa using oscillate_empty_eq_core_compl

example : oscillate (oscillate (∅ : Carrier)) = (∅ : Carrier) := by
  simpa using oscillate_twice_empty

end Numbers
end Tests
end HeytingLean
