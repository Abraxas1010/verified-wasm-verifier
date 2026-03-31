import HeytingLean.Representations.Radial.Core
import HeytingLean.ATheory.AssemblyCore

/-!
# Assembly theory connection (scaffold)

In the radial architecture, “assembly index” is represented by the ring number.
This file provides a minimal bridge so later work can connect `HeytingLean.ATheory` objects
to radial state spaces.
-/

namespace HeytingLean
namespace Representations
namespace Radial
namespace Assembly

open HeytingLean.Representations.Radial

/-- A minimal “assembly system” described only by ring sizes (scaffold). -/
structure AssemblySystem where
  ringSizes : List Nat
  ring0_nonempty : ringSizes.getD 0 0 > 0
  deriving Repr

/-- Build a radial graph from an assembly system (scaffold). -/
def assemblySpace (sys : AssemblySystem) : RadialGraph :=
  { ringSizes := sys.ringSizes
    ring0_nonempty := sys.ring0_nonempty }

theorem ring_eq_assembly (G : RadialGraph) (s : G.StateIdx) :
    (G.ringOf s).val = G.assemblyIndex s := rfl

end Assembly
end Radial
end Representations
end HeytingLean

