import HeytingLean.Topology.Knot.Conway

/-!
# Knot theory: Conway evaluator laws

Theorems in this file are proof-facing wrappers around the executable Conway evaluator.
-/

namespace HeytingLean
namespace Topology
namespace Knot

namespace Kauffman
namespace SignedPDGraph

/-- Local positive-branch step law (proof-facing alias). -/
theorem conwayWithFuel_pos_step_eq
    {fuel : Nat} {sp : SignedPDGraph}
    (hValid : validate sp = .ok ())
    (hn : sp.graph.n ≠ 0)
    (hSign : sp.sign[sp.graph.n - 1]! = .pos) :
    conwayWithFuel (fuel + 1) sp =
      (do
        let s0 ← lZeroLast sp
        let p0 ← conwayWithFuel fuel s0
        let sm ← lMinusLast sp
        let pm ← conwayWithFuel fuel sm
        pure (pm + z * p0)) := by
  rw [conwayWithFuel_unfold_succ]
  simp [hValid, hn, hSign, Bind.bind, Except.bind, Pure.pure, Except.pure]

end SignedPDGraph
end Kauffman

end Knot
end Topology
end HeytingLean
