import HeytingLean.LoF.Combinators.GraphReduction
import HeytingLean.LoF.Combinators.AIGOracle
import HeytingLean.LoF.Correspondence.LoFPrimaryAIGOracleSKYBool
import HeytingLean.LoF.Correspondence.GraphReductionOracleSoundness

/-!
# LoFPrimaryAIGOracleGraphReduction — using LoFPrimary AIG evaluation as a graph-reduction oracle

This file connects the Phase 1 graph reducer to the Phase 3 “boolean oracle” idea:

* `GraphReduction` provides a rooted graph-stepper with an `oracle` node.
* `LoFPrimaryAIGOracleSKYBool.aigOracle` computes a Church-boolean via the verified AIG pipeline.

We package an `OracleRef` that carries a LoF expression + environment, and prove the
term-level behavior needed to justify `Graph.StepOracle.oracle_select`.
-/

namespace HeytingLean
namespace LoF
namespace Correspondence

open HeytingLean.LoF
open HeytingLean.LoF.Comb
open HeytingLean.LoF.LoFPrimary
open HeytingLean.LoF.Combinators

open LoFPrimary.Expr
open SKYGraph

namespace LoFPrimaryAIGOracleGraphReduction

/-- An oracle reference: a primary LoF expression paired with its Boolean environment. -/
abbrev OracleRef := Σ n : Nat, AIGOracle.Ref n

def oracleEval : OracleRef → Bool
  | ⟨_, r⟩ => AIGOracle.eval r

def oracleComb : OracleRef → Comb
  | ⟨n, r⟩ => LoFPrimaryAIGOracleSKYBool.aigOracle (n := n) r.expr r.inputs

theorem oracle_select_steps (ref : OracleRef) (x y : Comb) :
    Comb.Steps (Comb.app (Comb.app (oracleComb ref) x) y)
      (if oracleEval ref then x else y) := by
  rcases ref with ⟨n, r⟩
  have hEval : oracleEval ⟨n, r⟩ = LoFPrimary.eval (n := n) r.expr r.inputs := by
    simpa [oracleEval] using (AIGOracle.eval_eq_lof_eval (n := n) r)
  -- reduce `oracleComb` to the canonical `ofBool (eval A ρ)`
  have hBool :
      Comb.Steps (oracleComb ⟨n, r⟩) (SKYBool.ofBool (LoFPrimary.eval (n := n) r.expr r.inputs)) := by
    simpa [oracleComb] using
      (LoFPrimaryAIGOracleSKYBool.aigOracle_correct (n := n) r.expr r.inputs)

  have hApp :
      Comb.Steps
        (Comb.app (Comb.app (oracleComb ⟨n, r⟩) x) y)
        (Comb.app (Comb.app (SKYBool.ofBool (LoFPrimary.eval (n := n) r.expr r.inputs)) x) y) := by
    have h1 : Comb.Steps (Comb.app (oracleComb ⟨n, r⟩) x)
        (Comb.app (SKYBool.ofBool (LoFPrimary.eval (n := n) r.expr r.inputs)) x) :=
      StepsLemmas.steps_app_left (a := x) hBool
    exact StepsLemmas.steps_app_left (a := y) h1

  cases hcase : LoFPrimary.eval (n := n) r.expr r.inputs with
  | false =>
      have hSel : Comb.Steps (Comb.app (Comb.app (SKYBool.ofBool false) x) y) y := by
        simpa [SKYBool.ofBool] using SKYBool.ff_select (x := x) (y := y)
      exact StepsLemmas.steps_transitive hApp (by
        simpa [hEval, hcase] using hSel)
  | true =>
      have hSel : Comb.Steps (Comb.app (Comb.app (SKYBool.ofBool true) x) y) x := by
        simpa [SKYBool.ofBool] using SKYBool.tt_select (x := x) (y := y)
      exact StepsLemmas.steps_transitive hApp (by
        simpa [hEval, hcase] using hSel)

theorem stepOracle_sound {g g' : SKYGraph.Graph OracleRef} {t : Comb}
    (hstep : SKYGraph.Graph.StepOracle (OracleRef := OracleRef) oracleEval g g')
    (hreal : SKYGraph.Realizes (OracleRef := OracleRef) oracleComb g g.root t) :
    ∃ t', Comb.Steps t t' ∧ SKYGraph.Realizes (OracleRef := OracleRef) oracleComb g' g'.root t' := by
  exact
    GraphReductionOracleSoundness.stepOracle_sound (OracleRef := OracleRef) (oracleEval := oracleEval)
      (oracle := oracleComb) (g := g) (g' := g') (t := t) hstep hreal oracle_select_steps

end LoFPrimaryAIGOracleGraphReduction

end Correspondence
end LoF
end HeytingLean
