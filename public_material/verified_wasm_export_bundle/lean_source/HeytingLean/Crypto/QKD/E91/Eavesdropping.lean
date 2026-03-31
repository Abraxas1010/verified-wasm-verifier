import HeytingLean.Crypto.ConstructiveHardness.Security
import HeytingLean.Crypto.QKD.E91.Superinfo

/-!
# E91 eavesdropping strategies (toy, interface-first)

At this abstraction layer, we model a “perfect” eavesdropper as one who can
copy the combined alphabet `XY` (i.e. `copyAll`). This is enough to invoke the
generic no-cloning security theorem.
-/

namespace HeytingLean
namespace Crypto
namespace QKD
namespace E91

open HeytingLean.Constructor.CT
open HeytingLean.Crypto.ConstructiveHardness

def eveInterceptTask : CTask E91Substrate :=
  copyAll

def interceptStrategy : EavesdroppingStrategy E91Substrate e91TaskCT where
  intercept := eveInterceptTask
  gains_info := True
  sound := fun _ => trivial

theorem intercept_requires_copyAll :
    e91TaskCT.possible interceptStrategy.intercept → e91TaskCT.possible copyAll := by
  intro h
  exact h

end E91
end QKD
end Crypto
end HeytingLean

