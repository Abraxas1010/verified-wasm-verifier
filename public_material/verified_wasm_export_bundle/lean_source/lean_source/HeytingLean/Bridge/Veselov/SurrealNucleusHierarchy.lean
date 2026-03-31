import HeytingLean.Bridge.Veselov.TimeReduction

/-!
# Bridge.Veselov.SurrealNucleusHierarchy

Scoped OP02 bridge surface:
finite-stage hierarchy approximation built from reduction-trace stages, with
successor monotonicity and bounded-limit stability.
-/

namespace HeytingLean.Bridge.Veselov

universe u

/-- Stage-indexed state in the bounded hierarchy approximation. -/
def StageState (S : Type u) (R : DiscreteReduction S) (s : S) (n : Nat) : S :=
  reductionTrace (S := S) R s n

/-- Stage-indexed potential in the bounded hierarchy approximation. -/
def StagePotential (S : Type u) (R : DiscreteReduction S) (s : S) (n : Nat) : Nat :=
  R.potential (StageState S R s n)

/-- Successor-stage monotonicity contract. -/
def SuccessorHierarchyMonotone (S : Type u) (R : DiscreteReduction S) (s : S) : Prop :=
  ∀ n, StagePotential S R s (n + 1) ≤ StagePotential S R s n

/-- Bounded-limit stability contract for stage-indexed traces. -/
def BoundedLimitStable (S : Type u) (R : DiscreteReduction S) (s : S) (N : Nat) : Prop :=
  ∀ m, N ≤ m → StageState S R s m = StageState S R s N

/-- Successor-stage potentials are non-increasing. -/
theorem successor_hierarchy_monotone
    (S : Type u) (R : DiscreteReduction S) (s : S) :
    SuccessorHierarchyMonotone S R s := by
  intro n
  simpa [SuccessorHierarchyMonotone, StagePotential, StageState] using
    trace_potential_nonincreasing (S := S) (R := R) s n

/-- Zero-reachability implies bounded-limit stability in the stage hierarchy. -/
theorem bounded_limit_stability_of_zeroReachable
    (S : Type u) (R : DiscreteReduction S) (s : S)
    (H : ZeroReachable (S := S) R) :
    ∃ N, BoundedLimitStable S R s N := by
  rcases reductionTrace_eventual_stability (S := S) (R := R) s H with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro m hm
  simpa [BoundedLimitStable, StageState] using hN m hm

/--
Packaged OP02 scoped theorem:
- successor-stage monotonicity over the bounded hierarchy,
- bounded-limit stability under explicit zero-reachability assumptions.
-/
theorem op02_scoped_bridge_theorem
    (S : Type u) (R : DiscreteReduction S) (s : S)
    (H : ZeroReachable (S := S) R) :
    SuccessorHierarchyMonotone S R s ∧
      ∃ N, BoundedLimitStable S R s N := by
  exact ⟨successor_hierarchy_monotone S R s,
    bounded_limit_stability_of_zeroReachable S R s H⟩

end HeytingLean.Bridge.Veselov
