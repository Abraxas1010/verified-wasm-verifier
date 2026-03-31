import Mathlib.Tactic
import HeytingLean.LoF.MRSystems.Nucleus

/-!
Sanity checks for `LoF/MRSystems/Nucleus.lean`.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.ClosingTheLoop.MR
open HeytingLean.LoF.MRSystems

universe u v

variable {S : MRSystem.{u, v}} {b : S.B} (RI : RightInverseAt S b)

#check nonClosedCore (S := S) (b := b) RI
#check closedSelectorNucleus (S := S) (b := b) RI
#check closedSelectorNucleus_fixed_iff (S := S) (b := b) RI
#check mem_closedSelectorNucleus_toSublocale_iff (S := S) (b := b) RI

#check ΩClosed (S := S) (b := b) RI
#check ΩClosed.restrict (S := S) (b := b) RI
#check ΩClosed.extend (S := S) (b := b) RI
#check ΩClosed.equivClosedSubsets (S := S) (b := b) RI

end LoF
end Tests
end HeytingLean

