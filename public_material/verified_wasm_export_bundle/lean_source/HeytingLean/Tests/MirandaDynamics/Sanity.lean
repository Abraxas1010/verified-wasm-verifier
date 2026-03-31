import HeytingLean.MirandaDynamics

/-!
# Tests: MirandaDynamics sanity

These are small “no proof-gap” regression tests for the MirandaDynamics spine:

- reaching relation category laws,
- union-nucleus fixed-point characterization.
-/

namespace HeytingLean.Tests.MirandaDynamics

open HeytingLean.MirandaDynamics

namespace TKFT

open HeytingLean.MirandaDynamics.TKFT

universe u v w z

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type z}

theorem reaching_id_left (R : ReachingRel α β) :
    ReachingRel.comp (ReachingRel.id α) R = R :=
  ReachingRel.id_left R

theorem reaching_id_right (R : ReachingRel α β) :
    ReachingRel.comp R (ReachingRel.id β) = R :=
  ReachingRel.id_right R

theorem reaching_assoc (R : ReachingRel α β) (S : ReachingRel β γ) (T : ReachingRel γ δ) :
    ReachingRel.comp (ReachingRel.comp R S) T = ReachingRel.comp R (ReachingRel.comp S T) :=
  ReachingRel.assoc R S T

end TKFT

namespace FixedPoint

open HeytingLean.MirandaDynamics.FixedPoint

theorem union_fixedPoint_iff_superset {α : Type} (U S : Set α) :
    unionNucleus (α := α) U S = S ↔ U ⊆ S :=
  isFixedPoint_unionNucleus_iff (α := α) U S

end FixedPoint

end HeytingLean.Tests.MirandaDynamics
