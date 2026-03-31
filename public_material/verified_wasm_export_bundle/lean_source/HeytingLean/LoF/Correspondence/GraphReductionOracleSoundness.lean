import HeytingLean.LoF.Combinators.GraphReduction

/-!
# GraphReductionOracleSoundness — soundness of `StepOracle` via term-level oracle behavior

`GraphReduction` provides:

* `Graph.Step` — SKY (K/S/Y) graph reduction at the root, with `Graph.step_sound`
* `Graph.StepOracle` — an extension adding a rooted “oracle selection” rule

This file proves a generic soundness theorem for `StepOracle`, assuming the oracle node is
implemented by a term that, when applied to two arguments, reduces to the chosen branch.
-/

namespace HeytingLean
namespace LoF
namespace Correspondence

open HeytingLean.LoF
open HeytingLean.LoF.Comb
open HeytingLean.LoF.Combinators

open SKYGraph

namespace GraphReductionOracleSoundness

theorem stepOracle_sound
    {OracleRef : Type} {oracleEval : OracleRef → Bool} {oracle : OracleRef → Comb}
    {g g' : SKYGraph.Graph OracleRef} {t : Comb}
    (hstep : SKYGraph.Graph.StepOracle (OracleRef := OracleRef) oracleEval g g')
    (hreal : SKYGraph.Realizes (OracleRef := OracleRef) oracle g g.root t)
    (horacle :
      ∀ (ref : OracleRef) (x y : Comb),
        Comb.Steps (Comb.app (Comb.app (oracle ref) x) y) (if oracleEval ref then x else y)) :
    ∃ t', Comb.Steps t t' ∧ SKYGraph.Realizes (OracleRef := OracleRef) oracle g' g'.root t' := by
  classical
  refine
    match hstep with
    | .base h =>
        by
          rcases SKYGraph.Graph.step_sound (OracleRef := OracleRef) (oracle := oracle) (g := g) (g' := g')
              (t := t) h hreal with ⟨t', htStep, htReal⟩
          exact ⟨t', Comb.Steps.trans htStep (Comb.Steps.refl _), htReal⟩
    | @SKYGraph.Graph.StepOracle.oracle_select _ _ _ _
        rootL rootR leftL leftR ref hRoot hL hO hNew =>
        by
          subst hNew
          -- The graph did not change (only the root pointer), so we can reuse existing realizations.
          cases hreal with
          | app hRoot' hRootL hRootR =>
              rename_i rootLId rootRId tRootL tElse
              have hRoot'' : g.node? g.root = some (SKYGraph.Node.app (OracleRef := OracleRef) rootLId rootRId) := by
                simpa using hRoot'
              have hNodeEq :
                  SKYGraph.Node.app (OracleRef := OracleRef) rootLId rootRId =
                    SKYGraph.Node.app (OracleRef := OracleRef) rootL rootR :=
                Option.some.inj (hRoot''.symm.trans hRoot)
              injection hNodeEq with hRootLId hRootRId
              subst rootL
              subst rootR

              cases hRootL with
              | app hL' hLeftL hLeftR =>
                  rename_i leftLId leftRId tFun tThen
                  have hL'' : g.node? rootLId = some (SKYGraph.Node.app (OracleRef := OracleRef) leftLId leftRId) := by
                    simpa using hL'
                  have hNodeEq2 :
                      SKYGraph.Node.app (OracleRef := OracleRef) leftLId leftRId =
                        SKYGraph.Node.app (OracleRef := OracleRef) leftL leftR :=
                    Option.some.inj (hL''.symm.trans hL)
                  injection hNodeEq2 with hLeftLId hLeftRId
                  subst leftL
                  subst leftR

                  cases hLeftL with
                  | oracle refId hO' =>
                      have hO'' : g.node? leftLId = some (SKYGraph.Node.oracle (OracleRef := OracleRef) refId) := by
                        simpa using hO'
                      have hNodeEq3 :
                          SKYGraph.Node.oracle (OracleRef := OracleRef) refId =
                            SKYGraph.Node.oracle (OracleRef := OracleRef) ref :=
                        Option.some.inj (hO''.symm.trans hO)
                      injection hNodeEq3 with href
                      subst ref

                      have htSteps :
                          Comb.Steps (Comb.app (Comb.app (oracle refId) tThen) tElse)
                            (if oracleEval refId then tThen else tElse) :=
                        horacle refId tThen tElse

                      refine ⟨if oracleEval refId then tThen else tElse, htSteps, ?_⟩
                      cases hEv : oracleEval refId with
                      | true =>
                          have hp :
                              SKYGraph.Graph.NodesPrefix (OracleRef := OracleRef) g.nodes
                                ({ g with root := leftRId }.nodes) := by
                            simpa using SKYGraph.Graph.NodesPrefix.refl (OracleRef := OracleRef) g.nodes
                          have hThen' :
                              SKYGraph.Realizes (OracleRef := OracleRef) oracle { g with root := leftRId } leftRId tThen :=
                            SKYGraph.Realizes.weaken (OracleRef := OracleRef) (oracle := oracle) (g := g)
                              (g' := { g with root := leftRId }) hp hLeftR
                          simpa [hEv] using hThen'
                      | false =>
                          have hp :
                              SKYGraph.Graph.NodesPrefix (OracleRef := OracleRef) g.nodes
                                ({ g with root := rootRId }.nodes) := by
                            simpa using SKYGraph.Graph.NodesPrefix.refl (OracleRef := OracleRef) g.nodes
                          have hElse' :
                              SKYGraph.Realizes (OracleRef := OracleRef) oracle { g with root := rootRId } rootRId tElse :=
                            SKYGraph.Realizes.weaken (OracleRef := OracleRef) (oracle := oracle) (g := g)
                              (g' := { g with root := rootRId }) hp hRootR
                          simpa [hEv] using hElse'

                  | K h =>
                      cases (Option.some.inj (h.symm.trans hO))
                  | S h =>
                      cases (Option.some.inj (h.symm.trans hO))
                  | Y h =>
                      cases (Option.some.inj (h.symm.trans hO))
                  | app h _ _ =>
                      cases (Option.some.inj (h.symm.trans hO))

              | K h =>
                  cases (Option.some.inj (h.symm.trans hL))
              | S h =>
                  cases (Option.some.inj (h.symm.trans hL))
              | Y h =>
                  cases (Option.some.inj (h.symm.trans hL))
              | oracle _ h =>
                  cases (Option.some.inj (h.symm.trans hL))

          | K h =>
              cases (Option.some.inj (h.symm.trans hRoot))
          | S h =>
              cases (Option.some.inj (h.symm.trans hRoot))
          | Y h =>
              cases (Option.some.inj (h.symm.trans hRoot))
          | oracle _ h =>
              cases (Option.some.inj (h.symm.trans hRoot))

end GraphReductionOracleSoundness

end Correspondence
end LoF
end HeytingLean
