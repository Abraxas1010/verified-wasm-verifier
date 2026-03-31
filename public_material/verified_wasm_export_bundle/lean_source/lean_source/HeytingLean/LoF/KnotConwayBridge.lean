import HeytingLean.Topology.Knot.ConwayMathlib

/-!
# LoF bridge for Conway local skein dynamics

This file exposes a concrete bridge theorem:
"difference of marked alternatives equals variable-scaled smoothing"
for the executable local Conway evaluator.
-/

namespace HeytingLean
namespace LoF
namespace KnotConwayBridge

open HeytingLean.Topology.Knot
open HeytingLean.Topology.Knot.Kauffman

theorem mark_difference_eq_scaled_unmark
    {fuel : Nat} {sp : SignedPDGraph}
    (hValid : SignedPDGraph.validate sp = .ok ())
    (hn : sp.graph.n ≠ 0)
    (hSign : sp.sign[sp.graph.n - 1]! = .pos) :
    SignedPDGraph.conwayWithFuel (fuel + 1) sp =
      (do
        let s0 ← SignedPDGraph.lZeroLast sp
        let p0 ← SignedPDGraph.conwayWithFuel fuel s0
        let sm ← SignedPDGraph.lMinusLast sp
        let pm ← SignedPDGraph.conwayWithFuel fuel sm
        pure (pm + z * p0)) :=
  SignedPDGraph.conwayWithFuel_pos_step_eq
    (fuel := fuel) (sp := sp)
    hValid hn hSign

end KnotConwayBridge
end LoF
end HeytingLean
