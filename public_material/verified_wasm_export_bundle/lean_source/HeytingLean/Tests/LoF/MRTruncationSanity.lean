import HeytingLean.LoF.MRSystems.Truncation

/-!
# Smoke test: (M,R) selector “truncation”

This is a compile-only sanity check that the kernel-quotient equivalence for
`closeSelector` is available.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.ClosingTheLoop.MR

universe u v

variable {S : MRSystem.{u, v}} {b : S.B} (RI : RightInverseAt S b)

-- Kernel quotient ↔ closed range
#check HeytingLean.LoF.MRSystems.closeQuotEquivClosed (S := S) (b := b) RI

-- Range ↔ fixed points
#check HeytingLean.LoF.MRSystems.closedRangeEquivFixed (S := S) (b := b) RI

end LoF
end Tests
end HeytingLean
