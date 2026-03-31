import Mathlib.RingTheory.HahnSeries.Basic
import HeytingLean.Hyperseries.WellBased

namespace HeytingLean
namespace Hyperseries
namespace HahnTools

variable {Γ R : Type*} [PartialOrder Γ] [Zero R]

/-- Hahn-series support is well-based in the local sense. -/
theorem support_wellBased (x : HahnSeries Γ R) : WellBased x.support := by
  exact x.isPWO_support

/-- Hahn-series support is also well-founded. -/
theorem support_isWF (x : HahnSeries Γ R) : x.support.IsWF := by
  exact x.isWF_support

end HahnTools
end Hyperseries
end HeytingLean
