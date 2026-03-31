import HeytingLean.Computation.YWitness.ProductiveSequence
import HeytingLean.LoF.HoTT.SKYMultiway
import HeytingLean.LoF.Combinators.Category.Groupoid
import HeytingLean.LoF.Combinators.InfinityGroupoid.SSet
import HeytingLean.WPP.Wolfram.MultiwayBridge

namespace HeytingLean.Computation.YWitness

open CategoryTheory
open HeytingLean.LoF

/-- Each productive unfold contributes a concrete finite successor in the SKY multiway frontier. -/
theorem finite_multiway_crystallization (seed : Comb) (n : Nat) :
    ∃ ed : Comb.EventData,
      (ed, Comb.app (yProductiveSequence seed n) (yProductiveSequence seed (n + 1))) ∈
        Comb.stepEdges (yProductiveSequence seed (n + 1)) := by
  exact Comb.stepEdges_complete (yProductiveSequence_step seed n)

/-- The productive frontier step lifts to a morphism in the free groupoid completion. -/
noncomputable def productiveGroupoidArrow (seed : Comb) (n : Nat) :
    HeytingLean.LoF.Combinators.Category.GObj (yProductiveSequence seed (n + 1)) ⟶
      HeytingLean.LoF.Combinators.Category.GObj
        (Comb.app (yProductiveSequence seed n) (yProductiveSequence seed (n + 1))) := by
  classical
  let h := finite_multiway_crystallization seed n
  exact HeytingLean.LoF.Combinators.Category.LStep.toGroupoid
    ⟨Classical.choose h, Classical.choose_spec h⟩

theorem groupoid_completion_respects_productive_paths (seed : Comb) (n : Nat) :
    Nonempty
      (HeytingLean.LoF.Combinators.Category.GObj (yProductiveSequence seed (n + 1)) ⟶
        HeytingLean.LoF.Combinators.Category.GObj
          (Comb.app (yProductiveSequence seed n) (yProductiveSequence seed (n + 1)))) := by
  exact ⟨productiveGroupoidArrow seed n⟩

end HeytingLean.Computation.YWitness
