import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# AETHER Block Pruning Correctness

Cauchy-Schwarz + triangle-inequality safety proof for geometric block pruning.
-/

namespace HeytingLean.Bridge.Sharma.AetherPruning

variable {D : ℕ}

/-- Block metadata: centroid and radius. -/
structure BlockMeta (D : ℕ) where
  centroid : EuclideanSpace Real (Fin D)
  radius : Real
  radius_nonneg : 0 ≤ radius

/-- Key `k` belongs to block `B` when within radius of centroid. -/
def BlockMeta.contains (B : BlockMeta D) (k : EuclideanSpace Real (Fin D)) : Prop :=
  ‖k - B.centroid‖ ≤ B.radius

/-- Cauchy-Schwarz upper bound used by pruning. -/
noncomputable def upperBoundScore (q : EuclideanSpace Real (Fin D)) (B : BlockMeta D) : Real :=
  ‖q‖ * (‖B.centroid‖ + B.radius)

lemma norm_key_le_centroid_plus_radius
    (B : BlockMeta D) (k : EuclideanSpace Real (Fin D)) (hk : B.contains k) :
    ‖k‖ ≤ ‖B.centroid‖ + B.radius := by
  have htri : ‖k‖ ≤ ‖k - B.centroid‖ + ‖B.centroid‖ := by
    simpa [sub_add_cancel] using (norm_add_le (k - B.centroid) B.centroid)
  have hrad : ‖k - B.centroid‖ + ‖B.centroid‖ ≤ B.radius + ‖B.centroid‖ := by
    exact add_le_add_right hk _
  calc
    ‖k‖ ≤ ‖k - B.centroid‖ + ‖B.centroid‖ := htri
    _ ≤ B.radius + ‖B.centroid‖ := hrad
    _ = ‖B.centroid‖ + B.radius := by ring

lemma inner_le_upperBound (q k : EuclideanSpace Real (Fin D)) (B : BlockMeta D)
    (hk : B.contains k) :
    inner Real q k ≤ upperBoundScore q B := by
  have h1 : inner Real q k ≤ ‖q‖ * ‖k‖ := real_inner_le_norm _ _
  have h2 : ‖k‖ ≤ ‖B.centroid‖ + B.radius :=
    norm_key_le_centroid_plus_radius B k hk
  have hmul : ‖q‖ * ‖k‖ ≤ ‖q‖ * (‖B.centroid‖ + B.radius) := by
    exact mul_le_mul_of_nonneg_left h2 (norm_nonneg q)
  calc
    inner Real q k ≤ ‖q‖ * ‖k‖ := h1
    _ ≤ ‖q‖ * (‖B.centroid‖ + B.radius) := hmul

/-- Main pruning safety theorem. -/
theorem prune_safe (q k : EuclideanSpace Real (Fin D))
    (B : BlockMeta D)
    (hk : B.contains k)
    (theta : Real)
    (h_prune : upperBoundScore q B < theta) :
    inner Real q k < theta := by
  have hbound : inner Real q k ≤ upperBoundScore q B :=
    inner_le_upperBound q k B hk
  exact lt_of_le_of_lt hbound h_prune

/-- `can_prune` soundness. -/
theorem can_prune_sound (q : EuclideanSpace Real (Fin D))
    (B : BlockMeta D) (theta : Real)
    (h : upperBoundScore q B < theta) :
    ∀ k, B.contains k → inner Real q k < theta :=
  fun k hk => prune_safe q k B hk theta h

/-- Upper bound is attained in a nontrivial radius-zero block when `D > 0`. -/
theorem upper_bound_tight (hD : 0 < D) :
    ∃ (q : EuclideanSpace Real (Fin D)) (B : BlockMeta D) (k : EuclideanSpace Real (Fin D)),
      q ≠ 0 ∧ B.contains k ∧ inner Real q k = upperBoundScore q B := by
  let i0 : Fin D := ⟨0, hD⟩
  let q : EuclideanSpace Real (Fin D) := Pi.single i0 1
  let B : BlockMeta D := ⟨q, 0, le_rfl⟩
  refine ⟨q, B, q, ?_, ?_, ?_⟩
  · intro hq
    have hAt : q i0 = 0 := by simp [hq]
    simp [q, i0] at hAt
  · simp [BlockMeta.contains, B, q]
  · change inner Real q q = ‖q‖ * (‖B.centroid‖ + B.radius)
    calc
      inner Real q q = ‖q‖ ^ 2 := by simp [real_inner_self_eq_norm_sq]
      _ = ‖q‖ * ‖q‖ := by ring
      _ = ‖q‖ * (‖B.centroid‖ + B.radius) := by simp [B]

/-- If child keys are included in parent keys, parent pruning implies child pruning. -/
theorem hierarchical_prune_safe
    (q : EuclideanSpace Real (Fin D))
    (parent child : BlockMeta D)
    (h_sub : ∀ k, child.contains k → parent.contains k)
    (theta : Real)
    (h_prune : upperBoundScore q parent < theta) :
    ∀ k, child.contains k → inner Real q k < theta :=
  fun k hk => prune_safe q k parent (h_sub k hk) theta h_prune

end HeytingLean.Bridge.Sharma.AetherPruning
