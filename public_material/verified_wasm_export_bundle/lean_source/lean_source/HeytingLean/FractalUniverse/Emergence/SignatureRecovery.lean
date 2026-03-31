import HeytingLean.FractalUniverse.Emergence.DiscreteDAlembert

/-!
# Signature Recovery

Formalizes the causal splitting of the discrete d'Alembertian from
Veselov's "Fractal Universe" paper (Section 5.2). A causal splitting
partitions edges into timelike and spacelike, yielding a decomposition
of the past contribution (and hence □_G) into temporal and spatial parts.
This is the foundation of Lorentzian signature recovery (−,+,+,+).

Key results:
- `pastContribution_causal_split`: past contribution = temporal + spatial
- Constants are killed by both temporal and spatial parts.
-/

namespace HeytingLean.FractalUniverse.Emergence

/-- A causal splitting partitions each edge into timelike or spacelike. -/
structure CausalSplitting (G : WeightedCausalGraph) (t : ℕ) where
  is_timelike : G.V t → G.V t → Prop
  is_spacelike : G.V t → G.V t → Prop
  partition : ∀ u v, G.E t u v → is_timelike u v ∨ is_spacelike u v
  disjoint : ∀ u v, ¬ (is_timelike u v ∧ is_spacelike u v)

/-- The temporal part of the d'Alembertian (sums over timelike edges only). -/
noncomputable def temporalPart (G : WeightedCausalGraph) (t : ℕ) [Fintype (G.V t)]
    [DecidableEq (G.V t)] [∀ u v : G.V t, Decidable (G.E t u v)]
    (split : CausalSplitting G t) [∀ u v : G.V t, Decidable (split.is_timelike u v)]
    (f : G.V t → ℝ) (v : G.V t) : ℝ :=
  ∑ u : G.V t, if G.E t u v ∧ split.is_timelike u v
    then (f v - f u) * G.weight t u v else 0

/-- The spatial part of the d'Alembertian (sums over spacelike edges only). -/
noncomputable def spatialPart (G : WeightedCausalGraph) (t : ℕ) [Fintype (G.V t)]
    [DecidableEq (G.V t)] [∀ u v : G.V t, Decidable (G.E t u v)]
    (split : CausalSplitting G t) [∀ u v : G.V t, Decidable (split.is_spacelike u v)]
    (f : G.V t → ℝ) (v : G.V t) : ℝ :=
  ∑ u : G.V t, if G.E t v u ∧ split.is_spacelike v u
    then (f u - f v) * G.weight t v u else 0

/-- Constants are killed by both temporal and spatial parts. -/
theorem temporal_const (G : WeightedCausalGraph) (t : ℕ) [Fintype (G.V t)]
    [DecidableEq (G.V t)] [∀ u v : G.V t, Decidable (G.E t u v)]
    (split : CausalSplitting G t) [∀ u v : G.V t, Decidable (split.is_timelike u v)]
    (c : ℝ) (v : G.V t) :
    temporalPart G t split (fun _ => c) v = 0 := by
  unfold temporalPart; simp [sub_self, zero_mul]

theorem spatial_const (G : WeightedCausalGraph) (t : ℕ) [Fintype (G.V t)]
    [DecidableEq (G.V t)] [∀ u v : G.V t, Decidable (G.E t u v)]
    (split : CausalSplitting G t) [∀ u v : G.V t, Decidable (split.is_spacelike u v)]
    (c : ℝ) (v : G.V t) :
    spatialPart G t split (fun _ => c) v = 0 := by
  unfold spatialPart; simp [sub_self, zero_mul]

/-- The past contribution decomposes into timelike and spacelike parts
    via any causal splitting. For each edge u → v, the partition ensures
    the edge is exactly one of timelike or spacelike, so the sum splits. -/
theorem pastContribution_causal_split (G : WeightedCausalGraph) (t : ℕ)
    [Fintype (G.V t)] [DecidableEq (G.V t)]
    [∀ u v : G.V t, Decidable (G.E t u v)]
    (split : CausalSplitting G t)
    [∀ u v : G.V t, Decidable (split.is_timelike u v)]
    [∀ u v : G.V t, Decidable (split.is_spacelike u v)]
    (f : G.V t → ℝ) (v : G.V t) :
    pastContribution G t f v = temporalPart G t split f v +
      ∑ u : G.V t, if G.E t u v ∧ split.is_spacelike u v
        then (f v - f u) * G.weight t u v else 0 := by
  unfold pastContribution temporalPart
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hE : G.E t u v
  · rcases split.partition u v hE with hT | hS
    · have hNS : ¬split.is_spacelike u v := fun hS' => split.disjoint u v ⟨hT, hS'⟩
      simp [hE, hT, hNS]
    · have hNT : ¬split.is_timelike u v := fun hT' => split.disjoint u v ⟨hT', hS⟩
      simp [hE, hNT, hS]
  · simp [hE]

end HeytingLean.FractalUniverse.Emergence
