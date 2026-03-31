import HeytingLean.Quantum.Measurement.Basis

/-!
Diagonal (computational-basis) POVMs.

This is a “thin layer” that is strong enough for physically meaningful IO/executable demos:

- effects are diagonal matrices with nonnegative real entries,
- effects sum to identity (pointwise on the diagonal),
- Born probabilities are computed as `Re (Tr(E_x * ρ))`,
- probabilities are nonnegative and sum to `1`.

It deliberately avoids general POVM positivity (which typically wants functional calculus / square roots).
-/

noncomputable section

namespace HeytingLean
namespace Quantum

open Matrix Complex
open scoped BigOperators

variable {n : ℕ}

private def diagEffect (w : Fin n → ℝ) : Mat n :=
  Matrix.diagonal fun i => (w i : ℂ)

private lemma diagEffect_apply (w : Fin n → ℝ) (i j : Fin n) :
    diagEffect (n := n) w i j = (if i = j then (w i : ℂ) else 0) := by
  rfl

private lemma trace_diagEffect_mul (w : Fin n → ℝ) (ρ : Density n) :
    (Matrix.trace (diagEffect (n := n) w * ρ.mat)).re = ∑ i : Fin n, w i * basisProb ρ i := by
  classical
  -- Expand the trace and use that multiplying by a diagonal matrix scales each diagonal entry.
  unfold Matrix.trace
  -- `trace (E*ρ) = ∑ i (E*ρ) i i` and `(E*ρ) i i = w i * ρ i i`.
  have hentry : ∀ i : Fin n, (diagEffect (n := n) w * ρ.mat) i i = (w i : ℂ) * ρ.mat i i := by
    intro i
    -- Expand matrix multiplication and use diagonal sparsity.
    simp [Matrix.mul_apply, diagEffect, Matrix.diagonal]
  -- Now take real parts termwise, using that `ρ` is Hermitian so diagonal entries are real.
  have hdiagReal : ∀ i : Fin n, (ρ.mat i i).im = 0 := by
    intro i
    exact Density.Matrix.IsHermitian.diag_im_zero ρ.hermitian i
  -- Convert the real part of the trace into a sum of real parts.
  calc
    (∑ i : Fin n, (diagEffect (n := n) w * ρ.mat) i i).re
        = ∑ i : Fin n, ((diagEffect (n := n) w * ρ.mat) i i).re := by
            -- `Complex.reAddGroupHom` is additive, so it commutes with finite sums.
            exact map_sum Complex.reAddGroupHom (fun i : Fin n => (diagEffect (n := n) w * ρ.mat) i i) Finset.univ
    _ = ∑ i : Fin n, (((w i : ℂ) * ρ.mat i i)).re := by
          simp [hentry]
    _ = ∑ i : Fin n, w i * (ρ.mat i i).re := by
          refine Finset.sum_congr rfl ?_
          intro i _
          -- `w i` is real, and the diagonal entry is real (im = 0), so `Re((w:ℂ)*z) = w*Re(z)`.
          simp [Complex.mul_re, hdiagReal i]
    _ = ∑ i : Fin n, w i * basisProb ρ i := by
          simp [basisProb]

/-- A diagonal POVM: effects are diagonal matrices (computational basis),
with nonnegative real weights summing to `1` on each diagonal coordinate. -/
structure DiagonalPOVM (X : Type*) [Fintype X] where
  weight : X → Fin n → ℝ
  weight_nonneg : ∀ x i, 0 ≤ weight x i
  weight_sum_one : ∀ i, (∑ x : X, weight x i) = 1

namespace DiagonalPOVM

variable {X : Type*} [Fintype X] (Λ : DiagonalPOVM (n := n) X)

/-- The effect matrix for outcome `x`. -/
def effect (x : X) : Mat n :=
  diagEffect (n := n) (Λ.weight x)

/-- Born probability for outcome `x`. -/
def prob (ρ : Density n) (x : X) : ℝ :=
  (Matrix.trace (Λ.effect x * ρ.mat)).re

lemma prob_eq_sum (ρ : Density n) (x : X) :
    Λ.prob ρ x = ∑ i : Fin n, Λ.weight x i * basisProb ρ i := by
  classical
  unfold DiagonalPOVM.prob DiagonalPOVM.effect
  exact trace_diagEffect_mul (n := n) (w := Λ.weight x) ρ

lemma prob_nonneg (ρ : Density n) (x : X) : 0 ≤ Λ.prob ρ x := by
  classical
  -- Reduce to a weighted sum of basis probabilities and apply `Finset.sum_nonneg`.
  rw [Λ.prob_eq_sum (ρ := ρ) x]
  refine Finset.sum_nonneg ?_
  intro i _
  exact mul_nonneg (Λ.weight_nonneg x i) (basisProb_nonneg (ρ := ρ) i)

lemma prob_sum (ρ : Density n) : (∑ x : X, Λ.prob ρ x) = 1 := by
  classical
  -- Write everything as a double `Fintype` sum and swap it via an equivalence on product types.
  let f : X → Fin n → ℝ := fun x i => Λ.weight x i * basisProb ρ i
  have hprob : (∑ x : X, Λ.prob ρ x) = ∑ x : X, ∑ i : Fin n, f x i := by
    simp [DiagonalPOVM.prob_eq_sum, f]
  have hswap :
      (∑ x : X, ∑ i : Fin n, f x i) = ∑ i : Fin n, ∑ x : X, f x i := by
    -- Turn nested sums into a sum over `X × Fin n`, swap components, then turn back into nested sums.
    have h₁ : (∑ x : X, ∑ i : Fin n, f x i) = ∑ p : X × Fin n, f p.1 p.2 := by
      simpa using (Fintype.sum_prod_type' (f := f)).symm
    have h₂ : (∑ p : X × Fin n, f p.1 p.2) = ∑ q : Fin n × X, f q.2 q.1 := by
      simpa using
        (Fintype.sum_equiv (Equiv.prodComm X (Fin n))
          (fun p : X × Fin n => f p.1 p.2)
          (fun q : Fin n × X => f q.2 q.1)
          (by intro p; simp))
    let g : Fin n → X → ℝ := fun i x => f x i
    have h₃ : (∑ q : Fin n × X, f q.2 q.1) = ∑ i : Fin n, ∑ x : X, f x i := by
      simpa [g] using (Fintype.sum_prod_type' (f := g))
    exact h₁.trans (h₂.trans h₃)
  have hfactor :
      (∑ i : Fin n, ∑ x : X, f x i) = ∑ i : Fin n, (∑ x : X, Λ.weight x i) * basisProb ρ i := by
    -- Factor out `basisProb ρ i` from the inner sum.
    refine Fintype.sum_congr
      (f := fun i : Fin n => ∑ x : X, f x i)
      (g := fun i : Fin n => (∑ x : X, Λ.weight x i) * basisProb ρ i) ?_
    intro i
    -- Use distributivity of multiplication over a finite sum.
    -- `Finset.sum_mul` gives `(∑ w) * p = ∑ (w*p)`; we use it in the reverse direction.
    have hs :
        (∑ x : X, Λ.weight x i * basisProb ρ i) = (∑ x : X, Λ.weight x i) * basisProb ρ i := by
      simpa using
        (Finset.sum_mul (s := (Finset.univ : Finset X))
          (f := fun x : X => Λ.weight x i) (a := basisProb ρ i)).symm
    simpa [f, hs]
  calc
    (∑ x : X, Λ.prob ρ x)
        = ∑ x : X, ∑ i : Fin n, f x i := hprob
    _ = ∑ i : Fin n, ∑ x : X, f x i := hswap
    _ = ∑ i : Fin n, (∑ x : X, Λ.weight x i) * basisProb ρ i := hfactor
    _ = ∑ i : Fin n, basisProb ρ i := by
          refine Fintype.sum_congr
            (f := fun i : Fin n => (∑ x : X, Λ.weight x i) * basisProb ρ i)
            (g := fun i : Fin n => basisProb ρ i) ?_
          intro i
          simp [Λ.weight_sum_one i]
    _ = 1 := by
          simpa using basisProb_sum (ρ := ρ)

end DiagonalPOVM

end Quantum
end HeytingLean
