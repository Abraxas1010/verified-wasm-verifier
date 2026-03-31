import HeytingLean.Genesis.YWitness.WitnessDuality
import HeytingLean.Numbers.Surreal.YWitness
import HeytingLean.Bridge.YWitness.ClassicalConstructive
import HeytingLean.Computation.YWitness.ProbabilityLane

namespace HeytingLean.Genesis.YWitness

open Order

/-- Phase-5 milestone packaging: every lane records the proposition it now supports. -/
structure YWitnessMilestone where
  foundations : Prop
  surreal : Prop
  booleanCore : Prop
  computation : Prop

/-- The assembled phase-5 milestone keeps the honest per-lane theorem strengths visible. -/
def phase5Milestone {L : Type _} [CompleteLattice L] (R : Nucleus L)
    (cw : ContinuousWitness L) (seed : ReentrySeed L)
    (g : HeytingLean.Numbers.SurrealCore.PreGame)
    {α : Type _} [HeytingAlgebra α] (a : α)
    (c : HeytingLean.LoF.Comb) : YWitnessMilestone where
  foundations :=
    CrystallizesTo R cw (crystallizationPoint R) /\
      Regenerates (crystallizationPoint R) seed
  surreal :=
    (HeytingLean.Numbers.Surreal.YWitness.ofPreGame g).raw = g /\
      HeytingLean.Numbers.SurrealCore.canonicalize g ∈
        (HeytingLean.Numbers.Surreal.YWitness.ofPreGame g).closureCarrier
  booleanCore :=
    HeytingLean.Bridge.YWitness.isDiscrete
        (HeytingLean.LoF.Bauer.doubleNegNucleus α a) /\
      Function.IsFixedPt (HeytingLean.LoF.Bauer.doubleNegNucleus α)
        (HeytingLean.LoF.Bauer.doubleNegNucleus α a)
  computation :=
    HeytingLean.LoF.Comb.Step
        (HeytingLean.Computation.YWitness.yProductiveSequence c 1)
        (HeytingLean.LoF.Comb.app
          (HeytingLean.Computation.YWitness.yProductiveSequence c 0)
          (HeytingLean.Computation.YWitness.yProductiveSequence c 1)) /\
      0 < HeytingLean.Computation.YWitness.normalizedWeightAtDepth 1 c

theorem y_witness_chain_phase5 {L : Type _} [CompleteLattice L] (R : Nucleus L)
    (cw : ContinuousWitness L) (hcw : FollowsApprox R cw)
    (seed : ReentrySeed L) (hseed : StartsAt seed.seq (crystallizationPoint R))
    (g : HeytingLean.Numbers.SurrealCore.PreGame)
    {α : Type _} [HeytingAlgebra α] (a : α)
    (c : HeytingLean.LoF.Comb) :
    let milestone := phase5Milestone R cw seed g a c
    milestone.foundations ∧ milestone.surreal ∧ milestone.booleanCore ∧ milestone.computation := by
  dsimp [phase5Milestone]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨⟨hcw, rfl⟩, ⟨hseed, seed.nonconstant⟩⟩
  · exact ⟨HeytingLean.Numbers.Surreal.YWitness.ofPreGame_raw g,
      HeytingLean.Numbers.Surreal.YWitness.canonicalized_mem_closureCarrier g⟩
  · exact ⟨HeytingLean.Bridge.YWitness.bounded_classical_constructive_bridge_on_dn_core
        (α := α) a,
      HeytingLean.Bridge.YWitness.y_fixed_point_shape_on_dn_core (α := α) a⟩
  · exact ⟨by
        simpa using HeytingLean.Computation.YWitness.yProductiveSequence_step c 0,
      HeytingLean.Computation.YWitness.finite_productive_paths_have_positive_weight 1 c⟩

end HeytingLean.Genesis.YWitness
