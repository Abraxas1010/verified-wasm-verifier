import Mathlib
import HeytingLean.Bridge.Veselov.GaloisNucleus

/-!
# Bridge.Veselov.TimeReduction

A complete, assumption-first formalization of iterative reduction dynamics:
- finite-valued potential,
- strictly decreasing nonzero update step,
- induced well-founded descent relation, and
- zero-state stabilization.
-/

namespace HeytingLean.Bridge.Veselov

universe u

/-- Measure-valued reduction contract. -/
structure DiscreteReduction (S : Type u) where
  potential : S → ℕ
  step : S → S
  strictDescent : ∀ s, potential s ≠ 0 → potential (step s) < potential s
  terminalAtZero : ∀ s, potential s = 0 → step s = s

/-- Potential-descent relation on states. -/
def reductionRelation (S : Type u) (R : DiscreteReduction S) : S → S → Prop :=
  InvImage (· < ·) R.potential

/-- The relation is well-founded because it is measured by natural-number potential. -/
theorem reductionRelation_wf (S : Type u) (R : DiscreteReduction S) :
    WellFounded (reductionRelation S R) := by
  simpa [reductionRelation] using
    (inferInstance : IsWellFounded S (InvImage (· < ·) R.potential)).wf

/-- `step` strictly lowers potential whenever the system is not at zero energy. -/
theorem step_decreases (S : Type u) (R : DiscreteReduction S) {s : S}
    (hs : R.potential s ≠ 0) :
    R.potential (R.step s) < R.potential s :=
  R.strictDescent s hs

/-- The zero-level is invariant under the update. -/
theorem terminal_state (S : Type u) (R : DiscreteReduction S) {s : S}
    (hz : R.potential s = 0) :
    R.step s = s :=
  R.terminalAtZero s hz

/-- Iterated reduction trace (0-based). -/
def reductionTrace (S : Type u) (R : DiscreteReduction S) (s : S) : ℕ → S
  | 0 => s
  | n + 1 => R.step (reductionTrace (S := S) R s n)

/-- Trace remains stable once the initial state is zero. -/
theorem zeroTrace_stable (S : Type u) (R : DiscreteReduction S) (s : S)
    (hz : R.potential s = 0) :
    ∀ n, reductionTrace (S := S) R s n = s := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [reductionTrace, ih, terminal_state (S := S) R hz]

/-- Any nonzero state is either terminal-incompatible (hence descending), or
already stable at zero. -/
theorem one_step_description (S : Type u) (R : DiscreteReduction S) (s : S) :
    (R.potential s = 0 ∧ R.step s = s) ∨
      (R.potential s ≠ 0 ∧ R.potential (R.step s) < R.potential s) := by
  by_cases hs : R.potential s = 0
  · exact Or.inl ⟨hs, terminal_state (S := S) R hs⟩
  · exact Or.inr ⟨hs, step_decreases (S := S) R hs⟩

/-- Assumption wrapper used by high-level reduction strategies: a finite index after which
potential is at zero for each initial state. -/
structure ZeroReachable (S : Type u) (R : DiscreteReduction S) where
  stabilizationTime : S → ℕ
  reachesZero : ∀ s, R.potential (reductionTrace (S := S) R s (stabilizationTime s)) = 0

/-- Trace additivity: `n + m` steps from `s` equal `m` steps from the `n`-reduced state. -/
theorem reductionTrace_add (S : Type u) (R : DiscreteReduction S) (s : S) (n m : ℕ) :
    reductionTrace (S := S) R s (n + m) =
      reductionTrace (S := S) R (reductionTrace (S := S) R s n) m := by
  induction m with
  | zero =>
      simp [reductionTrace]
  | succ m ih =>
      calc
        reductionTrace (S := S) R s (n + m.succ)
            = R.step (reductionTrace (S := S) R s (n + m)) := by
                simp [reductionTrace]
        _ = R.step (reductionTrace (S := S) R (reductionTrace (S := S) R s n) m) := by
                simpa using congrArg R.step (ih)
        _ = reductionTrace (S := S) R (reductionTrace (S := S) R s n) (m.succ) := by
                simp [reductionTrace]

/-- Potential along the trace is non-increasing. -/
theorem trace_potential_nonincreasing (S : Type u) (R : DiscreteReduction S) (s : S) :
    ∀ n, R.potential (reductionTrace (S := S) R s (n + 1))
      ≤ R.potential (reductionTrace (S := S) R s n) := by
  intro n
  by_cases hzero : R.potential (reductionTrace (S := S) R s n) = 0
  · simp [reductionTrace, terminal_state (S := S) R hzero]
  · exact le_of_lt (R.strictDescent _ hzero)

/-- Once a zero potential state is reached, later steps are stable by definition. -/
theorem reductionTrace_stable_after (S : Type u) (R : DiscreteReduction S)
    (s : S) (H : ZeroReachable (S := S) R) :
    ∀ m : ℕ, reductionTrace (S := S) R s (H.stabilizationTime s + m) =
      reductionTrace (S := S) R s (H.stabilizationTime s) := by
  intro m
  have hz : R.potential (reductionTrace (S := S) R s (H.stabilizationTime s)) = 0 :=
    H.reachesZero s
  calc
    reductionTrace (S := S) R s (H.stabilizationTime s + m)
        = reductionTrace (S := S) R (reductionTrace (S := S) R s (H.stabilizationTime s)) m := by
          simpa using (reductionTrace_add (S := S) (R := R) (s := s)
            (n := H.stabilizationTime s) (m := m))
    _ = reductionTrace (S := S) R s (H.stabilizationTime s) := by
          exact zeroTrace_stable (S := S) (R := R)
            (s := reductionTrace (S := S) R s (H.stabilizationTime s)) hz m

/-- Assumption-first eventual stability theorem. -/
theorem reductionTrace_eventual_stability (S : Type u) (R : DiscreteReduction S)
    (s : S) (H : ZeroReachable (S := S) R) :
    ∃ n, ∀ m, n ≤ m → reductionTrace (S := S) R s m = reductionTrace (S := S) R s n := by
  refine ⟨H.stabilizationTime s, ?_⟩
  intro m hm
  rcases Nat.le.dest hm with ⟨k, rfl⟩
  simpa [Nat.add_comm] using (reductionTrace_stable_after (S := S) (R := R) (s := s) H k)

/-- Assumption-first reduction contract that exposes a lifted Novikov-style cover.
Keeps only hypotheses that are explicit and auditable. -/
structure NeuralReductionContract (S C : Type u) where
  lift : DiscreteReduction C
  cover : S → C
  project : C → S
  coverSection : ∀ s : S, project (cover s) = s
  coverAtZero : ∀ s : S, lift.potential (cover s) = 0
  terminalUnique :
    ∀ c c' : C, lift.potential c = 0 → lift.potential c' = 0 →
      project c = project c' → c = c'

/-- Lifted cover points are terminal for the explicit reduction relation. -/
theorem NeuralReductionContract.cover_fixed_point (S C : Type u)
    (R : NeuralReductionContract S C) (s : S) :
    R.lift.step (R.cover s) = R.cover s := by
  exact R.lift.terminalAtZero (R.cover s) (R.coverAtZero s)

/-- Projected zero-potential lifts identify by explicit contract witness. -/
theorem NeuralReductionContract.lift_zero_unique (S C : Type u)
    (R : NeuralReductionContract S C) {c c' : C}
    (hc : R.lift.potential c = 0) (hc' : R.lift.potential c' = 0)
    (hproj : R.project c = R.project c') : c = c' :=
  R.terminalUnique c c' hc hc' hproj

end HeytingLean.Bridge.Veselov
