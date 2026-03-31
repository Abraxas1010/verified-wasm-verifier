import HeytingLean.LoF.Combinators.GraphReduction

/-!
Sanity checks for the Phase 3 `StepOracle.oracle_select` root rule.

This is compile-only + tiny proof checks.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.LoF
open HeytingLean.LoF.Combinators
open HeytingLean.LoF.Combinators.SKYGraph

namespace SKYGraphReductionOracleSelectSanity

def oracleEvalTrue : Unit → Bool := fun _ => true
def oracleEvalFalse : Unit → Bool := fun _ => false

/--
Heap:

* `0`: `oracle ()`
* `1`: `K`  (then-branch)
* `2`: `S`  (else-branch)
* `3`: `(oracle ()  K)`
* `4`: `((oracle () K) S)`  ← root
-/
def g : SKYGraph.Graph Unit :=
  { nodes :=
      #[
        SKYGraph.Node.oracle (),
        SKYGraph.Node.combK,
        SKYGraph.Node.combS,
        SKYGraph.Node.app 0 1,
        SKYGraph.Node.app 3 2
      ]
    root := 4
  }

def gThen : SKYGraph.Graph Unit := { g with root := 1 }
def gElse : SKYGraph.Graph Unit := { g with root := 2 }

example : SKYGraph.Graph.StepOracle (OracleRef := Unit) oracleEvalTrue g gThen := by
  refine
    SKYGraph.Graph.StepOracle.oracle_select (oracleEval := oracleEvalTrue) (g := g) (g' := gThen)
      (rootL := 3) (rootR := 2) (leftL := 0) (leftR := 1) (ref := ()) ?_ ?_ ?_ ?_
  · simp [SKYGraph.Graph.node?, g]
  · simp [SKYGraph.Graph.node?, g]
  · simp [SKYGraph.Graph.node?, g]
  · simp [gThen, oracleEvalTrue]

example : SKYGraph.Graph.StepOracle (OracleRef := Unit) oracleEvalFalse g gElse := by
  refine
    SKYGraph.Graph.StepOracle.oracle_select (oracleEval := oracleEvalFalse) (g := g) (g' := gElse)
      (rootL := 3) (rootR := 2) (leftL := 0) (leftR := 1) (ref := ()) ?_ ?_ ?_ ?_
  · simp [SKYGraph.Graph.node?, g]
  · simp [SKYGraph.Graph.node?, g]
  · simp [SKYGraph.Graph.node?, g]
  · simp [gElse, oracleEvalFalse]

end SKYGraphReductionOracleSelectSanity

end LoF
end Tests
end HeytingLean
