import HeytingLean.LoF.Correspondence.LoFPrimaryAIGOracleGraphReduction

/-!
# LoFPrimaryAIGOracleGraphReductionSanity

Smoke checks for the Phase 3 “oracle selection” bridge for graph reduction.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.LoF
open HeytingLean.LoF.Comb
open HeytingLean.LoF.Combinators
open HeytingLean.LoF.Correspondence

namespace LoFPrimaryAIGOracleGraphReductionSanity

open LoFPrimaryAIGOracleGraphReduction

def ref0 : OracleRef :=
  ⟨0, { expr := LoFPrimary.Expr.void, inputs := fun i => nomatch i }⟩

example (x y : Comb) :
    Comb.Steps (Comb.app (Comb.app (oracleComb ref0) x) y) (if oracleEval ref0 then x else y) := by
  simpa using oracle_select_steps ref0 x y

-- Ensure the bundled graph-level oracle soundness theorem type-checks.
#check LoFPrimaryAIGOracleGraphReduction.stepOracle_sound

end LoFPrimaryAIGOracleGraphReductionSanity

end LoF
end Tests
end HeytingLean

