import HeytingLean.Topology.Knot.Conway

/-!
# Knot theory: Alexander layer (executable)

This phase keeps Alexander and Conway in the same executable Laurent polynomial carrier,
interpreting the result under an Alexander variable name.
-/

namespace HeytingLean
namespace Topology
namespace Knot

namespace Kauffman

abbrev AlexanderPoly := LaurentPoly

/-- Alexander variable `t`. -/
def t : AlexanderPoly := LaurentPoly.mon 1 1

namespace SignedPDGraph

/-- Variable-renaming map from Conway form into Alexander form (same carrier in this phase). -/
def alexanderOfConway (p : ConwayPoly) : AlexanderPoly := p

/-- Fuel-bounded Alexander evaluator. -/
def alexanderWithFuel (fuel : Nat) (s : SignedPDGraph) : Except String AlexanderPoly := do
  let p ← conwayWithFuel fuel s
  pure (alexanderOfConway p)

/-- Executable Alexander evaluator. -/
def alexander (s : SignedPDGraph) : Except String AlexanderPoly :=
  alexanderWithFuel (conwayBudget s) s

@[simp] theorem alexanderWithFuel_eq_map_conwayWithFuel (fuel : Nat) (s : SignedPDGraph) :
    alexanderWithFuel fuel s = (conwayWithFuel fuel s).map alexanderOfConway := by
  unfold alexanderWithFuel
  cases h : conwayWithFuel fuel s <;> rfl

@[simp] theorem alexander_eq_map_conway (s : SignedPDGraph) :
    alexander s = (conway s).map alexanderOfConway := by
  unfold alexander conway
  exact alexanderWithFuel_eq_map_conwayWithFuel (conwayBudget s) s

end SignedPDGraph

end Kauffman

end Knot
end Topology
end HeytingLean
