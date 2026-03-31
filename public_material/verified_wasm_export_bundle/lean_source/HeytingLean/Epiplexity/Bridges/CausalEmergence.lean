import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ENNReal.Basic
import HeytingLean.Bridges.Emergence
import HeytingLean.Epiplexity.Emergence
import HeytingLean.Epiplexity.Prelude

namespace HeytingLean
namespace Epiplexity
namespace Bridges
namespace CausalEmergence

open scoped BigOperators

open HeytingLean.Probability.InfoTheory
open HeytingLean.Bridges.Emergence

noncomputable section

namespace TPM

variable {n : Nat}

/-- Row weights of a TPM converted to real numbers. -/
noncomputable def rowWeights (P : TPM n) (i : Fin n) : Fin n → ℝ :=
  fun j => (P.prob i j).toReal

/-- Real-valued sum of the row weights. -/
noncomputable def rowSum (P : TPM n) (i : Fin n) : ℝ :=
  ∑ j : Fin n, rowWeights P i j

/--
Normalize a TPM row into a `FinDist (Fin n)`.

We require `0 < n` so a fallback distribution exists. If the row sum is zero (degenerate TPM),
we fall back to the uniform distribution on `Fin n`.
-/
noncomputable def rowDist (P : TPM n) (hn : 0 < n) (i : Fin n) : FinDist (Fin n) := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let w : Fin n → ℝ := rowWeights (n := n) P i
  let Z : ℝ := ∑ j : Fin n, w j
  have hZnonneg : 0 ≤ Z := by
    refine Finset.sum_nonneg ?_
    intro j _
    dsimp [w, rowWeights]
    exact ENNReal.toReal_nonneg
  by_cases hZ : Z = 0
  · exact Epiplexity.FinDist.uniform (α := Fin n)
  · have h0ne : (0 : ℝ) ≠ Z := (ne_comm).1 hZ
    have hZpos : 0 < Z := lt_of_le_of_ne hZnonneg h0ne
    refine
      { pmf := fun j => w j / Z
        nonneg := ?_
        sum_one := ?_ }
    · intro j
      have hw : 0 ≤ w j := by
        dsimp [w, rowWeights]
        exact ENNReal.toReal_nonneg
      exact div_nonneg hw (le_of_lt hZpos)
    · have hZ0 : Z ≠ 0 := hZ
      calc
        (∑ j : Fin n, w j / Z) = (∑ j : Fin n, w j) / Z := by
          simp [div_eq_mul_inv, Finset.sum_mul]
        _ = Z / Z := by simp [Z]
        _ = 1 := by simp [hZ0]

/--
Joint distribution on `(cause, effect)` induced by a TPM, under a uniform prior on causes.

This is the probability model needed to feed a TPM into Epiplexity’s conditional layer.
-/
noncomputable def jointDist (P : TPM n) (hn : 0 < n) : FinDist (Fin n × Fin n) := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let U : FinDist (Fin n) := Epiplexity.FinDist.uniform (α := Fin n)
  refine
    { pmf := fun ij => U.pmf ij.1 * (rowDist (n := n) P hn ij.1).pmf ij.2
      nonneg := ?_
      sum_one := ?_ }
  · intro ij
    exact mul_nonneg (U.nonneg ij.1) ((rowDist (n := n) P hn ij.1).nonneg ij.2)
  · have hswap :
        (∑ ij : Fin n × Fin n, U.pmf ij.1 * (rowDist (n := n) P hn ij.1).pmf ij.2)
          = ∑ i : Fin n, ∑ j : Fin n, U.pmf i * (rowDist (n := n) P hn i).pmf j := by
      simpa using (Fintype.sum_prod_type
        (fun ij : Fin n × Fin n => U.pmf ij.1 * (rowDist (n := n) P hn ij.1).pmf ij.2))
    calc
      (∑ ij : Fin n × Fin n, U.pmf ij.1 * (rowDist (n := n) P hn ij.1).pmf ij.2)
          = ∑ i : Fin n, ∑ j : Fin n, U.pmf i * (rowDist (n := n) P hn i).pmf j := hswap
      _ = ∑ i : Fin n, U.pmf i * (∑ j : Fin n, (rowDist (n := n) P hn i).pmf j) := by
            refine Fintype.sum_congr _ _ (fun i => ?_)
            change
              (Finset.univ.sum fun j : Fin n => U.pmf i * (rowDist (n := n) P hn i).pmf j)
                =
              U.pmf i * (Finset.univ.sum fun j : Fin n => (rowDist (n := n) P hn i).pmf j)
            simp [Finset.mul_sum]
      _ = ∑ i : Fin n, U.pmf i * 1 := by
            refine Fintype.sum_congr _ _ (fun i => ?_)
            simp [(rowDist (n := n) P hn i).sum_one]
      _ = ∑ i : Fin n, U.pmf i := by simp
      _ = 1 := U.sum_one

end TPM

namespace Emergence

open HeytingLean.Epiplexity.Emergence

/--
A finite (non-asymptotic) epiplexity-gap predicate: there exist optimizers at two time bounds whose
`ST` values differ by at least `g`.
-/
def HasSTGapAtLeast {α β : Type u} [Fintype α] [Fintype β]
    (T₁ T₂ : Nat) (PXY : FinDist (α × β)) (g : Nat) : Prop :=
  ∃ opt₁ : OptimalCondProg (α := α) (β := β) (T := T₁) (PXY := PXY),
    ∃ opt₂ : OptimalCondProg (α := α) (β := β) (T := T₂) (PXY := PXY),
      g ≤ STGap (opt₁ := opt₁) (opt₂ := opt₂)

end Emergence

end

end CausalEmergence
end Bridges
end Epiplexity
end HeytingLean
