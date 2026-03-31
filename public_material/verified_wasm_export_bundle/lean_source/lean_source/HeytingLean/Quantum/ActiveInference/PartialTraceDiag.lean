import HeytingLean.Quantum.ActiveInference.PartialTrace
import HeytingLean.Quantum.QState
import HeytingLean.Quantum.QFreeEnergy

/-
Diagonal density helpers for partial-trace manipulations.  These lemmas keep
the cumbersome reindexing localized so the data-processing proof can treat
classical (diagonal) states as probability tables.
-/

namespace HeytingLean
namespace Quantum
namespace ActiveInference

open scoped Matrix BigOperators
open Matrix

noncomputable section

def diagDensityProd {m k : ℕ} (d : Fin m × Fin k → ℝ)
    (hd_nonneg : ∀ p, 0 ≤ d p) (hd_sum : ∑ p, d p = 1) :
    Density (m * k) := by
  classical
  refine Density.diagDensity
    (fun idx : Fin (m * k) => d (finProdFinEquiv.symm idx)) ?_ ?_
  · intro idx; simpa using hd_nonneg (finProdFinEquiv.symm idx)
  ·
    have hsum :
        (∑ idx : Fin (m * k), d (finProdFinEquiv.symm idx)) =
          ∑ p : Fin m × Fin k, d p := by
      simpa using
        (Fintype.sum_equiv (finProdFinEquiv (m:=m) (n:=k)).symm
          (fun idx : Fin (m * k) => d (finProdFinEquiv.symm idx))
          (fun p : Fin m × Fin k => d p)
          (by intro idx; simp))
    simpa [hsum.symm] using hd_sum

lemma diagDensityProd_mat {m k : ℕ} (d : Fin m × Fin k → ℝ)
    (hd_nonneg : ∀ p, 0 ≤ d p) (hd_sum : ∑ p, d p = 1) :
    (diagDensityProd d hd_nonneg hd_sum).mat =
      Matrix.diagonal fun idx : Fin (m * k) =>
        (d (finProdFinEquiv.symm idx) : ℂ) := rfl

lemma partialTraceDensity_diagDensityProd_mat {m k : ℕ}
    (d : Fin m × Fin k → ℝ)
    (hd_nonneg : ∀ p, 0 ≤ d p) (hd_sum : ∑ p, d p = 1) :
    (partialTraceDensity (diagDensityProd d hd_nonneg hd_sum)).mat =
      Matrix.diagonal fun i : Fin m =>
        (∑ l : Fin k, d (i, l) : ℂ) := by
  classical
  let e : Fin m × Fin k ≃ Fin (m * k) := finProdFinEquiv (m:=m) (n:=k)
  have hSub :
      ((diagDensityProd d hd_nonneg hd_sum).mat).submatrix
          (fun ik => e ik) (fun ik => e ik) =
        Matrix.diagonal fun p : Fin m × Fin k => (d p : ℂ) := by
    classical
    ext p q
    by_cases h : p = q
    · subst q
      have heq : e.symm (e p) = p := by
        simpa using e.left_inv p
      have hpair :
          ((e p).divNat, (e p).modNat) = e.symm (e p) := rfl
      simp [Matrix.submatrix, diagDensityProd_mat, Matrix.diagonal,
        heq, hpair, Function.comp]
    · have hneq : e p ≠ e q := by
        intro heq
        exact h (by simpa using e.injective heq)
      simp [Matrix.submatrix, diagDensityProd_mat, Matrix.diagonal,
        h, hneq, Function.comp]
  have hSub' :
      ((diagDensityProd d hd_nonneg hd_sum).mat).submatrix
          (fun ik => finProdFinEquiv (m:=m) (n:=k) ik)
          (fun ik => finProdFinEquiv (m:=m) (n:=k) ik) =
        Matrix.diagonal fun p : Fin m × Fin k => (d p : ℂ) := by
    simpa [e]
      using hSub
  have htrace :
      partialTrace (Matrix.diagonal fun p : Fin m × Fin k => (d p : ℂ)) =
        Matrix.diagonal fun i : Fin m =>
          (∑ l : Fin k, d (i, l) : ℂ) := by
    simpa using partialTrace_diagonal_real (m:=m) (k:=k) d
  have hPartial :
      (partialTraceDensity (diagDensityProd d hd_nonneg hd_sum)).mat =
        partialTrace
          (((diagDensityProd d hd_nonneg hd_sum).mat).submatrix
            (fun ik => e ik) (fun ik => e ik)) := by
    rfl
  have hPartial' :
      (partialTraceDensity (diagDensityProd d hd_nonneg hd_sum)).mat =
        partialTrace
          (((diagDensityProd d hd_nonneg hd_sum).mat).submatrix
            (fun ik => finProdFinEquiv (m:=m) (n:=k) ik)
            (fun ik => finProdFinEquiv (m:=m) (n:=k) ik)) := by
    simpa [e] using hPartial
  simpa [partialTraceDensity, hPartial', hSub', htrace]

lemma partialTraceDensity_diagDensityProd {m k : ℕ}
    (d : Fin m × Fin k → ℝ)
    (hd_nonneg : ∀ p, 0 ≤ d p) (hd_sum : ∑ p, d p = 1) :
    partialTraceDensity (diagDensityProd d hd_nonneg hd_sum) =
      Density.diagDensity
        (fun i : Fin m => ∑ l : Fin k, d (i, l))
        (fun i =>
          Finset.sum_nonneg fun l _ => hd_nonneg (i, l))
        (by
          classical
          have hpair :
              (∑ p : Fin m × Fin k, d p) =
                ∑ i : Fin m, ∑ l : Fin k, d (i, l) := by
            simpa using
              (Fintype.sum_prod_type
                (f := fun p : Fin m × Fin k => d p))
          simpa [hpair] using hd_sum) := by
  classical
  refine Density.ext ?_
  simpa [partialTraceDensity_diagDensityProd_mat, Density.diagDensity]

lemma qRelEnt_partialTrace_diagDensityProd_le {m k : ℕ} [NeZero k]
    (r s : Fin m × Fin k → ℝ)
    (hr_pos : ∀ p, 0 < r p) (hs_pos : ∀ p, 0 < s p)
    (hr_sum : ∑ p, r p = 1) (hs_sum : ∑ p, s p = 1) :
    qRelEnt
        (partialTraceDensity
          (diagDensityProd r (fun p => (hr_pos p).le) hr_sum))
        (partialTraceDensity
          (diagDensityProd s (fun p => (hs_pos p).le) hs_sum))
      ≤ qRelEnt
          (diagDensityProd r (fun p => (hr_pos p).le) hr_sum)
          (diagDensityProd s (fun p => (hs_pos p).le) hs_sum) := by
  classical
  have hk_pos : 0 < k := Nat.pos_of_ne_zero (NeZero.ne (n := k))
  have hrow_nonneg_r :
      ∀ i : Fin m, 0 ≤ ∑ l : Fin k, r (i, l) :=
    fun i => Finset.sum_nonneg fun l _ => (hr_pos (i, l)).le
  have hrow_nonneg_s :
      ∀ i : Fin m, 0 ≤ ∑ l : Fin k, s (i, l) :=
    fun i => Finset.sum_nonneg fun l _ => (hs_pos (i, l)).le
  have hrow_pos_r :
      ∀ i : Fin m, 0 < ∑ l : Fin k, r (i, l) := by
    intro i
    classical
    let l₀ : Fin k := ⟨0, hk_pos⟩
    have hmem : l₀ ∈ (Finset.univ : Finset (Fin k)) := by simp
    have hle :
        r (i, l₀) ≤ ∑ l : Fin k, r (i, l) :=
      Finset.single_le_sum
        (fun l _ => (hr_pos (i, l)).le)
        hmem
    exact lt_of_lt_of_le (hr_pos (i, l₀)) hle
  have hrow_pos_s :
      ∀ i : Fin m, 0 < ∑ l : Fin k, s (i, l) := by
    intro i
    classical
    let l₀ : Fin k := ⟨0, hk_pos⟩
    have hmem : l₀ ∈ (Finset.univ : Finset (Fin k)) := by simp
    have hle :
        s (i, l₀) ≤ ∑ l : Fin k, s (i, l) :=
      Finset.single_le_sum
        (fun l _ => (hs_pos (i, l)).le)
        hmem
    exact lt_of_lt_of_le (hs_pos (i, l₀)) hle
  have hrow_sum_r :
      ∑ i : Fin m, ∑ l : Fin k, r (i, l) = 1 := by
    have hpair :
        (∑ p : Fin m × Fin k, r p) =
          ∑ i : Fin m, ∑ l : Fin k, r (i, l) := by
      simpa using
        (Fintype.sum_prod_type
          (f := fun p : Fin m × Fin k => r p))
    simpa [hpair.symm, hr_sum]
  have hrow_sum_s :
      ∑ i : Fin m, ∑ l : Fin k, s (i, l) = 1 := by
    have hpair :
        (∑ p : Fin m × Fin k, s p) =
          ∑ i : Fin m, ∑ l : Fin k, s (i, l) := by
      simpa using
        (Fintype.sum_prod_type
          (f := fun p : Fin m × Fin k => s p))
    simpa [hpair.symm, hs_sum]
  have hpartial_r :
      partialTraceDensity
          (diagDensityProd r (fun p => (hr_pos p).le) hr_sum) =
        Density.diagDensity
          (fun i : Fin m => ∑ l : Fin k, r (i, l))
          (fun i => hrow_nonneg_r i)
          hrow_sum_r :=
    partialTraceDensity_diagDensityProd r (fun p => (hr_pos p).le) hr_sum
  have hpartial_s :
      partialTraceDensity
          (diagDensityProd s (fun p => (hs_pos p).le) hs_sum) =
        Density.diagDensity
          (fun i : Fin m => ∑ l : Fin k, s (i, l))
          (fun i => hrow_nonneg_s i)
          hrow_sum_s :=
    partialTraceDensity_diagDensityProd s (fun p => (hs_pos p).le) hs_sum
  have hpartial_q :
      qRelEnt
          (partialTraceDensity
            (diagDensityProd r (fun p => (hr_pos p).le) hr_sum))
          (partialTraceDensity
            (diagDensityProd s (fun p => (hs_pos p).le) hs_sum)) =
        ∑ i : Fin m,
          (∑ l : Fin k, r (i, l)) *
            (Real.log (∑ l : Fin k, r (i, l)) -
              Real.log (∑ l : Fin k, s (i, l))) := by
    simpa [hpartial_r, hpartial_s] using
      qRelEnt_diagDensity_eq_sum
        (d := fun i : Fin m => ∑ l : Fin k, r (i, l))
        (s := fun i : Fin m => ∑ l : Fin k, s (i, l))
        (hd_nonneg := fun i => hrow_nonneg_r i)
        (hd_sum := hrow_sum_r)
        (hs_nonneg := fun i => hrow_nonneg_s i)
        (hs_sum := hrow_sum_s)
  let e : Fin m × Fin k ≃ Fin (m * k) := finProdFinEquiv (m:=m) (n:=k)
  have hjoint :
      qRelEnt
          (diagDensityProd r (fun p => (hr_pos p).le) hr_sum)
          (diagDensityProd s (fun p => (hs_pos p).le) hs_sum) =
        ∑ p : Fin m × Fin k,
          r p * (Real.log (r p) - Real.log (s p)) := by
    have hsum_r :
        ∑ idx : Fin (m * k), r (e.symm idx) = 1 := by
      have h :=
        Fintype.sum_equiv e.symm
          (fun idx => r (e.symm idx))
          (fun p : Fin m × Fin k => r p)
          (by intro idx; simp)
      exact h.trans hr_sum
    have hsum_s :
        ∑ idx : Fin (m * k), s (e.symm idx) = 1 := by
      have h :=
        Fintype.sum_equiv e.symm
          (fun idx => s (e.symm idx))
          (fun p : Fin m × Fin k => s p)
          (by intro idx; simp)
      exact h.trans hs_sum
    have hq :
        qRelEnt
            (diagDensityProd r (fun p => (hr_pos p).le) hr_sum)
            (diagDensityProd s (fun p => (hs_pos p).le) hs_sum) =
          ∑ idx : Fin (m * k),
            r (e.symm idx) *
              (Real.log (r (e.symm idx)) - Real.log (s (e.symm idx))) := by
      simpa using
        qRelEnt_diagDensity_eq_sum
          (n := m * k)
          (d := fun idx : Fin (m * k) => r (e.symm idx))
          (s := fun idx : Fin (m * k) => s (e.symm idx))
          (hd_nonneg := fun idx => (hr_pos (e.symm idx)).le)
          (hd_sum := hsum_r)
          (hs_nonneg := fun idx => (hs_pos (e.symm idx)).le)
          (hs_sum := hsum_s)
    have hsum_reindex :
        (∑ idx : Fin (m * k),
            r (e.symm idx) *
              (Real.log (r (e.symm idx)) - Real.log (s (e.symm idx)))) =
          ∑ p : Fin m × Fin k,
            r p * (Real.log (r p) - Real.log (s p)) := by
      simpa using
        (Fintype.sum_equiv e.symm
          (fun idx =>
            r (e.symm idx) *
              (Real.log (r (e.symm idx)) - Real.log (s (e.symm idx))))
          (fun p =>
            r p * (Real.log (r p) - Real.log (s p)))
          (by intro idx; simp))
    exact hq.trans hsum_reindex
  have hineq' :
      ∑ i : Fin m,
          (∑ l : Fin k, r (i, l)) *
            (Real.log (∑ l : Fin k, r (i, l)) -
              Real.log (∑ l : Fin k, s (i, l))) ≤
        ∑ p : Fin m × Fin k,
          r p * (Real.log (r p) - Real.log (s p)) := by
    simpa [sub_eq_add_neg] using
      (sum_logRatio_partialTrace (m:=m) (k:=k) r s hr_pos hs_pos)
  simpa [hpartial_q, hjoint] using hineq'

end

end ActiveInference
end Quantum
end HeytingLean
