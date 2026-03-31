import HeytingLean.Genesis.NothingComputes.WitnessSeed
import HeytingLean.LoF.Combinators.SKYUniversality
import HeytingLean.Genesis.YWitness.FullChain

namespace HeytingLean.Genesis.NothingComputes

open Order

/-- Named noneist face of the strengthened theorem family. -/
def NonSingularFace (w : HeytingLean.Numbers.Surreal.NoneistKripke.World) : Prop :=
  ¬ HeytingLean.Noneism.NothingComputes.SingularNothingAt .varying w

/-- Named witness face of the strengthened theorem family. -/
def WitnessFace (w : HeytingLean.Numbers.Surreal.NoneistKripke.World) : Prop :=
  Nonempty (DistinctionWitness .varying w)

/-- Named self-reference face: the explicit SKY program fragment is encoded and unfolds exactly. -/
def SelfReferenceFace
    (program : HeytingLean.LoF.Combinators.SKYUniversality.SelfProgram) : Prop :=
  HeytingLean.LoF.Combinators.SKYUniversality.encode
      (HeytingLean.LoF.Combinators.SKYUniversality.decode
        (HeytingLean.LoF.Combinators.SKYUniversality.encode program)) =
    HeytingLean.LoF.Combinators.SKYUniversality.encode program ∧
      HeytingLean.LoF.Comb.Step
        (HeytingLean.LoF.Combinators.SKYUniversality.encode (.unfold program))
        (HeytingLean.LoF.Comb.app
          (HeytingLean.LoF.Combinators.SKYUniversality.encode program)
          (HeytingLean.LoF.Combinators.SKYUniversality.encode (.unfold program)))

/-- Honest strengthened milestone: keep the existing phase-5 package, but add the exact noneist,
plurality, and explicit SKY self-reference lanes as separate visible fields.
-/
structure StrengthenedMilestone where
  noneism : Prop
  witness : Prop
  selfReference : Prop
  foundations : Prop
  surreal : Prop
  booleanCore : Prop
  computation : Prop

/-- The strengthened package specializes the phase-5 milestone to the explicit SKY program lane. -/
def strengthenedPhase {L : Type _} [CompleteLattice L] (R : Nucleus L)
    (cw : HeytingLean.Genesis.YWitness.ContinuousWitness L)
    (seed : HeytingLean.Genesis.YWitness.ReentrySeed L)
    (w : HeytingLean.Numbers.Surreal.NoneistKripke.World)
    (g : HeytingLean.Numbers.SurrealCore.PreGame)
    {α : Type _} [HeytingAlgebra α] (a : α)
    (program : HeytingLean.LoF.Combinators.SKYUniversality.SelfProgram) :
    StrengthenedMilestone :=
  let milestone :=
    HeytingLean.Genesis.YWitness.phase5Milestone R cw seed g a
      (HeytingLean.LoF.Combinators.SKYUniversality.encode program)
  { noneism := NonSingularFace w
    witness := WitnessFace w
    selfReference := SelfReferenceFace program
    foundations := milestone.foundations
    surreal := milestone.surreal
    booleanCore := milestone.booleanCore
    computation := milestone.computation }

theorem strengthened_y_witness {L : Type _} [CompleteLattice L] (R : Nucleus L)
    (cw : HeytingLean.Genesis.YWitness.ContinuousWitness L)
    (hcw : HeytingLean.Genesis.YWitness.FollowsApprox R cw)
    (seed : HeytingLean.Genesis.YWitness.ReentrySeed L)
    (hseed : HeytingLean.Genesis.YWitness.StartsAt seed.seq
      (HeytingLean.Genesis.YWitness.crystallizationPoint R))
    (w : HeytingLean.Numbers.Surreal.NoneistKripke.World) (hw : 1 ≤ w.stage)
    (g : HeytingLean.Numbers.SurrealCore.PreGame)
    {α : Type _} [HeytingAlgebra α] (a : α)
    (program : HeytingLean.LoF.Combinators.SKYUniversality.SelfProgram) :
    let strengthened := strengthenedPhase R cw seed w g a program
    strengthened.noneism ∧ strengthened.witness ∧ strengthened.selfReference ∧
      strengthened.foundations ∧ strengthened.surreal ∧
      strengthened.booleanCore ∧ strengthened.computation := by
  have hPhase :=
    HeytingLean.Genesis.YWitness.y_witness_chain_phase5
      R cw hcw seed hseed g a
        (HeytingLean.LoF.Combinators.SKYUniversality.encode program)
  dsimp [strengthenedPhase, NonSingularFace, WitnessFace, SelfReferenceFace]
  dsimp [HeytingLean.Genesis.YWitness.phase5Milestone] at hPhase
  rcases hPhase with ⟨hFound, hSur, hBool, hComp⟩
  refine ⟨?_, ?_, ?_, hFound, hSur, hBool, hComp⟩
  · exact HeytingLean.Noneism.NothingComputes.nothing_not_singular_exact w hw
  · exact witness_from_plurality w hw
  · exact ⟨HeytingLean.LoF.Combinators.SKYUniversality.decode_encode program,
      HeytingLean.LoF.Combinators.SKYUniversality.encode_unfold_step program⟩

end HeytingLean.Genesis.NothingComputes
