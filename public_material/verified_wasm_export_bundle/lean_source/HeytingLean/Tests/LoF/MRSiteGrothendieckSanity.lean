import Mathlib.Tactic
import HeytingLean.LoF.MRSystems.Site

/-!
Sanity checks for `LoF/MRSystems/Site.lean` (Phase E.1).
-/

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.ClosingTheLoop.MR
open HeytingLean.LoF.MRSystems

universe u v

variable {S : MRSystem.{u, v}} {b : S.B} (RI : RightInverseAt S b)

#check HeytingLean.LoF.MRSystems.SelectorSite.Obj (S := S)
#check HeytingLean.LoF.MRSystems.SelectorSite.leafHom (S := S)

#check HeytingLean.LoF.MRSystems.SelectorSite.topology (S := S) (b := b) RI
#check HeytingLean.LoF.MRSystems.SelectorSite.mem_topology_leaf_iff (S := S) (b := b) (RI := RI)
#check HeytingLean.LoF.MRSystems.SelectorSite.close_leafHom_iff (S := S) (b := b) (RI := RI)

#check HeytingLean.LoF.MRSystems.SelectorSite.hubSieveOfSet (S := S)
#check HeytingLean.LoF.MRSystems.SelectorSite.leafSet (S := S)
#check HeytingLean.LoF.MRSystems.SelectorSite.equivΩClosedHubClosedSieve (S := S) (b := b) RI

end LoF
end Tests
end HeytingLean

