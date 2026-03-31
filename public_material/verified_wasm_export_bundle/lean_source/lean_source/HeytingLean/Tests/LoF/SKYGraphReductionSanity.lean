import HeytingLean.LoF.Combinators.GraphReduction

/-!
Sanity checks for `HeytingLean.LoF.Combinators.GraphReduction`.

This is compile-only + tiny proof checks.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.LoF
open HeytingLean.LoF.Combinators
open HeytingLean.LoF.Combinators.SKYGraph

namespace SKYGraphReductionSanity

def gK : SKYGraph.Graph Unit :=
  { nodes := #[SKYGraph.Node.combK], root := 0 }

example : SKYGraph.Realizes (oracle := fun _ => Comb.K) gK 0 Comb.K := by
  refine SKYGraph.Realizes.K (oracle := fun _ => Comb.K) (g := gK) (i := 0) ?_
  -- `nodes[0]? = some combK`
  simp [gK, SKYGraph.Graph.node?]

end SKYGraphReductionSanity

end LoF
end Tests
end HeytingLean

