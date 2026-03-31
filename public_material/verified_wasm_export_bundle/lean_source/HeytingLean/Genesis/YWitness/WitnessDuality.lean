import HeytingLean.Genesis.YWitness.Foundations
import HeytingLean.Genesis.ReentryTransport

namespace HeytingLean.Genesis.YWitness

/-- Any continuous witness that follows the canonical approximation chain crystallizes to the
canonical discrete witness. -/
theorem crystallization_has_discrete_witness {L : Type _} [CompleteLattice L]
    (R : Nucleus L) (cw : ContinuousWitness L) (hfollow : FollowsApprox R cw) :
    Exists fun dw : DiscreteWitness L R => CrystallizesTo R cw dw.point := by
  refine ⟨crystallizedWitness R, ?_⟩
  exact ⟨hfollow, rfl⟩

/-- Regeneration is only accepted when the seed exhibits a genuine adjacent change. -/
theorem regeneration_requires_nontrivial_seed {L : Type _} {x : L} {seed : ReentrySeed L}
    (hregen : Regenerates x seed) :
    AdjacentNonconstant seed.seq := by
  exact hregen.2

/-- A bounded roundtrip packages the crystallization point together with the regeneration witness. -/
theorem bounded_duality_roundtrip {L : Type _} [CompleteLattice L]
    (R : Nucleus L) (cw : ContinuousWitness L) {x : L} {seed : ReentrySeed L}
    (hcrys : CrystallizesTo R cw x) (hregen : Regenerates x seed) :
    x = crystallizationPoint R /\ AdjacentNonconstant seed.seq := by
  exact ⟨hcrys.2, hregen.2⟩

end HeytingLean.Genesis.YWitness
