import HeytingLean.Numbers.Surreal.Experimental.SyncLogic

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Numbers.Surreal
open HeytingLean.Numbers.SurrealCore
open HeytingLean.Numbers.Surreal.Experimental

private def wA : KinematicWorld := { stage := 0, velocity := 2 }
private def wB : KinematicWorld := { stage := 3, velocity := 4 }

example (h : irreducibleCertificate 1 wA wB) : unobtainable 1 wA wB := by
  exact irreducibleCertificate_implies_unobtainable h

example (A : Set PreGame) : setBoundaryOps.nonExistent A := by
  sync_logic

example (A : Set PreGame) : ¬ setBoundaryOps.impossible A := by
  sync_logic

end Numbers
end Tests
end HeytingLean
