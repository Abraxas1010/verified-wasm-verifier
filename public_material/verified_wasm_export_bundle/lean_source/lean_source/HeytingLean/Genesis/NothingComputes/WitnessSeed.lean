import HeytingLean.Noneism.NothingComputes.NonSingularity
import HeytingLean.Genesis.MinimalDistinction

namespace HeytingLean.Genesis.NothingComputes

open HeytingLean.Noneism
open HeytingLean.Noneism.NothingComputes

abbrev NKWorld := HeytingLean.Numbers.Surreal.NoneistKripke.World
abbrev NKDomainPolicy := HeytingLean.Numbers.Surreal.NoneistKripke.DomainPolicy

/-- A concrete distinction witness extracted from plurality in the noneist lane. -/
structure DistinctionWitness (policy : NKDomainPolicy) (w : NKWorld) where
  left : Term
  right : Term
  left_exists : ExistingNothing policy w left
  right_exists : ExistingNothing policy w right
  same_profile : IndiscernibleTerms policy w left right
  distinct : left ≠ right

namespace DistinctionWitness

/-- The canonical region-level image of a distinction witness lands in the existing Genesis atom. -/
def seedRegion {policy : NKDomainPolicy} {w : NKWorld}
    (_seed : DistinctionWitness policy w) : HeytingLean.Genesis.EmergentRegion :=
  HeytingLean.Genesis.minimalDistinction

theorem seedRegion_atom {policy : NKDomainPolicy} {w : NKWorld}
    (seed : DistinctionWitness policy w) :
    IsAtom seed.seedRegion := by
  simpa [seedRegion] using HeytingLean.Genesis.minimalDistinction_atom

end DistinctionWitness

/-- The canonical distinction witness at stage `≥ 1` is the irreducible pair `0` and `1`. -/
def canonicalWitnessSeed (w : NKWorld) (hStage : 1 ≤ w.stage) :
    DistinctionWitness .varying w where
  left := .var 0
  right := .var 1
  left_exists := existing_var_zero_varying w
  right_exists := existing_var_one_varying w hStage
  same_profile := all_existing_terms_indiscernible .varying w _ _
  distinct := var_zero_ne_var_one

/-- Plurality in the exact noneist lane produces an explicit minimal distinction witness. -/
theorem witness_from_plurality (w : NKWorld) (hStage : 1 ≤ w.stage) :
    Nonempty (DistinctionWitness .varying w) := by
  exact ⟨canonicalWitnessSeed w hStage⟩

/-- The stage assumption that forces exact non-singularity also forces a witness object. -/
theorem non_singular_nothing_yields_witness (w : NKWorld) (hStage : 1 ≤ w.stage) :
    ¬ SingularNothingAt .varying w ∧ Nonempty (DistinctionWitness .varying w) := by
  exact ⟨nothing_not_singular_exact w hStage, witness_from_plurality w hStage⟩

end HeytingLean.Genesis.NothingComputes
