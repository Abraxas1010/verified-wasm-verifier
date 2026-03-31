import HeytingLean.IteratedVirtual.Spiral

/-!
Compile-only sanity: spiral embedding functions elaborate.
-/

namespace HeytingLean
namespace Tests
namespace IteratedVirtual

open HeytingLean.IteratedVirtual

#check HeytingLean.IteratedVirtual.Point3
#check HeytingLean.IteratedVirtual.embedSteps

example : (HeytingLean.IteratedVirtual.embedSteps 0).length = 1 := by
  simp [HeytingLean.IteratedVirtual.embedSteps]

end IteratedVirtual
end Tests
end HeytingLean

