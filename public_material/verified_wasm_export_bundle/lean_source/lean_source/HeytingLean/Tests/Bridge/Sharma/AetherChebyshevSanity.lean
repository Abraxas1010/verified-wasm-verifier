import HeytingLean.Bridge.Sharma.AetherChebyshev

namespace HeytingLean.Tests.Bridge.Sharma

open HeytingLean.Bridge.Sharma.AetherChebyshev

#check fmean
#check fvariance
#check fstddev
#check @chebyshev_finite
#check @gc_25_percent_bound
#check @uniform_decay_preserves_guard
#check @impulse_strengthens_guard
#check @touch_protects

def sample4 : Fin 4 → Real := fun i => i.1

example : 0 ≤ fstddev sample4 := by
  simpa [sample4] using fstddev_nonneg sample4

end HeytingLean.Tests.Bridge.Sharma
