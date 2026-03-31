import HeytingLean.LoF.Combinators.Rewriting.StepAtCompute

/-!
# Smoke test: computable cube enumeration from disjoint SKY events

This file checks that `Comb.cubesList` computes at least one cube on a tiny term with three
pairwise-disjoint `K`-redexes.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.LoF
open HeytingLean.LoF.Comb

private def rK (x y : Comb) : Comb :=
  Comb.app (Comb.app .K x) y

-- Term shape: (r1 r2) r3, with redexes at paths [L,L], [L,R], [R].
private def demo : Comb :=
  Comb.app (Comb.app (rK .K .S) (rK .S .K)) (rK .Y .K)

-- Sanity: there are at least three one-step edges and at least one cube.
#eval (stepEdgesList demo).length
#eval (cubesList demo).length

end LoF
end Tests
end HeytingLean

