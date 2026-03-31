import HeytingLean.LoF.Combinators.Topos.StepsSite
import HeytingLean.LoF.MRSystems.ConfigSite
import HeytingLean.LoF.MRSystems.SKYBoolSimulation

/-!
# Bool configuration site → SKY reachability site (scoped work)

This module implements the **Bool-level** site/category bridge sketched in
`WIP/sky_heyting_infty_groupoid_unification_optional_future_research_mr_to_sky_site_bridge_2026-01-03.md`:

- MR-side: the reachability preorder on Boolean configurations `(state, remainingWord)` from
  `MRSystems/ConfigSite.lean`.
- SKY-side: the reachability preorder on terms (`Comb.Steps`) packaged as `Combinators.Topos.StepsCat`.

We construct a functor sending an MR configuration to the corresponding SKY term obtained by
applying the compiled step function along the remaining word, and prove that reachability implies
reduction in the SKY preorder.

Objectivity boundary:
- This is a Bool-level bridge, powered by the verified reduction theorem
  `BoolSim.steps_applyWordTerm_correct`.
- We do not claim this is a continuous functor between the dense Grothendieck topologies; this would
  require additional cover-density hypotheses that are not intrinsic to this encoding.
-/

namespace HeytingLean
namespace LoF
namespace MRSystems

open scoped Classical

open CategoryTheory
open HeytingLean.LoF
open HeytingLean.LoF.Comb

open HeytingLean.LoF.Correspondence
open HeytingLean.LoF.Correspondence.SKYBool
open HeytingLean.LoF.Correspondence.StepsLemmas

namespace BoolConfig

/-! ## Aligning `run` with the SKYBoolSimulation version -/

theorem run_eq_boolSim_run (R : Bool → Bool → Bool) (b : Bool) (w : List Bool) :
    BoolConfig.run R b w = BoolSim.run R b w := by
  induction w generalizing b with
  | nil =>
      simp [BoolConfig.run, BoolSim.run]
  | cons a w ih =>
      simp [BoolConfig.run, BoolSim.run, ih]

/-! ## Rewriting on words inside SKY terms -/

theorem applyWordTerm_append (step : Comb) (b : Comb) (w₁ w₂ : List Comb) :
    BoolSim.applyWordTerm step b (w₁ ++ w₂) =
      BoolSim.applyWordTerm step (BoolSim.applyWordTerm step b w₁) w₂ := by
  induction w₁ generalizing b with
  | nil =>
      simp [BoolSim.applyWordTerm]
  | cons a w₁ ih =>
      simp [BoolSim.applyWordTerm, ih]

/-! ## The configuration-to-term translation -/

/-- Translate an MR Boolean configuration to a SKY term representing “run the compiled step along the remaining word”. -/
def toSKYTerm (R : Bool → Bool → Bool) (c : Config R) : Comb :=
  BoolSim.applyWordTerm (BoolSim.toSKYFun2 R) (SKYBool.ofBool c.state) (c.word.map SKYBool.ofBool)

theorem steps_toSKYTerm_of_reachable {R : Bool → Bool → Bool} {c₁ c₂ : Config R}
    (h : Config.Reachable (R := R) c₁ c₂) :
    Comb.Steps (toSKYTerm R c₁) (toSKYTerm R c₂) := by
  rcases h with ⟨w, hw, hs⟩
  -- Abbreviations for readability.
  let step : Comb := BoolSim.toSKYFun2 R
  let enc : Bool → Comb := SKYBool.ofBool
  have hword : c₁.word.map enc = w.map enc ++ c₂.word.map enc := by
    simp [hw, List.map_append]
  -- Split the source term into prefix and suffix, reduce the prefix, then lift under the suffix context.
  have hsplit :
      BoolSim.applyWordTerm step (enc c₁.state) (c₁.word.map enc) =
        BoolSim.applyWordTerm step (BoolSim.applyWordTerm step (enc c₁.state) (w.map enc)) (c₂.word.map enc) := by
    simp [hword, applyWordTerm_append]
  -- Reduce the prefix fold to the encoded reached state.
  have hprefix :
      Comb.Steps
          (BoolSim.applyWordTerm step (enc c₁.state) (w.map enc))
          (enc (BoolConfig.run R c₁.state w)) := by
    -- Use the already-proved SKY reduction theorem (with `BoolSim.run`), then rewrite the `run`.
    have h0 :
        Comb.Steps
            (BoolSim.applyWordTerm step (enc c₁.state) (w.map enc))
            (enc (BoolSim.run R c₁.state w)) := by
      simpa [step, enc] using
        (BoolSim.steps_applyWordTerm_correct (R := R) (b := c₁.state) (w := w))
    simpa [run_eq_boolSim_run (R := R) (b := c₁.state) (w := w)] using h0
  -- Lift the prefix reduction under the remaining word.
  have hlift :
      Comb.Steps
          (BoolSim.applyWordTerm step
            (BoolSim.applyWordTerm step (enc c₁.state) (w.map enc))
            (c₂.word.map enc))
          (BoolSim.applyWordTerm step (enc (BoolConfig.run R c₁.state w)) (c₂.word.map enc)) :=
    BoolSim.steps_applyWordTerm_state (step := step) (b := _)
      (b' := enc (BoolConfig.run R c₁.state w)) hprefix (w := c₂.word.map enc)
  -- Rewrite the target state using `hs` and conclude.
  have hstate : enc (BoolConfig.run R c₁.state w) = enc c₂.state := by
    exact congrArg enc hs.symm
  -- Assemble: rewrite source by `hsplit`, apply `hlift`, then rewrite the final state.
  have hsplit' :
      toSKYTerm R c₁ =
        BoolSim.applyWordTerm step
          (BoolSim.applyWordTerm step (enc c₁.state) (w.map enc))
          (c₂.word.map enc) := by
    simpa [toSKYTerm, step, enc] using hsplit
  have hfinal :
      BoolSim.applyWordTerm step (enc (BoolConfig.run R c₁.state w)) (c₂.word.map enc) =
        toSKYTerm R c₂ := by
    simp [toSKYTerm, step, enc, hstate]
  -- Convert equalities to `Steps` via reflexivity, then compose.
  exact
    steps_transitive
      (by simpa [hsplit'] using Comb.Steps.refl (toSKYTerm R c₁))
      (steps_transitive hlift (by simpa [hfinal] using Comb.Steps.refl _))

/-! ## Functor to the SKY reachability category -/

/-- A preorder functor from configurations to terms: reachability implies reducibility. -/
noncomputable def toStepsCatFunctor (R : Bool → Bool → Bool) : BoolConfig.Config R ⥤ Combinators.Topos.StepsCat where
  obj c := toSKYTerm R c
  map {c₁ c₂} f :=
    CategoryTheory.homOfLE <| steps_toSKYTerm_of_reachable (R := R) (c₁ := c₁) (c₂ := c₂) (CategoryTheory.leOfHom f)
  map_id := by
    intro c
    apply Subsingleton.elim
  map_comp := by
    intro a b c f g
    apply Subsingleton.elim

end BoolConfig

end MRSystems
end LoF
end HeytingLean
