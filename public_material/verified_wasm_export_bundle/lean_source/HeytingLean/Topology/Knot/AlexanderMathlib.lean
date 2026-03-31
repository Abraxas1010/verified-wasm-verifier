import HeytingLean.Topology.Knot.Alexander

/-!
# Knot theory: Alexander derived laws

Proof-facing derived identities linking Alexander and Conway evaluators.
-/

namespace HeytingLean
namespace Topology
namespace Knot

namespace Kauffman
namespace SignedPDGraph

theorem alexanderWithFuel_eq_comp (fuel : Nat) (s : SignedPDGraph) :
    alexanderWithFuel fuel s = (conwayWithFuel fuel s).map alexanderOfConway := by
  exact alexanderWithFuel_eq_map_conwayWithFuel fuel s

theorem alexander_eq_comp_conway (s : SignedPDGraph) :
    alexander s = (conway s).map alexanderOfConway := by
  exact alexander_eq_map_conway s

end SignedPDGraph
end Kauffman

end Knot
end Topology
end HeytingLean
