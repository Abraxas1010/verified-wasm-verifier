import Mathlib.Data.Matrix.Block
import HeytingLean.Quantum.ActiveInference.PartialTrace

/-
Ancilla pinching operators.

The `pinchAncilla` map zeros all off-diagonal blocks along the ancilla index in a
bipartite matrix.  It preserves Hermitian / positive-semidefinite structure and
leaves the partial trace untouched, so it can be used to reduce to diagonal
ancilla blocks before invoking classical inequalities.
-/

namespace HeytingLean
namespace Quantum
namespace ActiveInference

open scoped Matrix BigOperators ComplexConjugate
open Matrix

noncomputable section

variable {m k : ℕ}

/-- Zero the off-diagonal ancilla blocks in a bipartite matrix. -/
def pinchAncilla
    (A : Matrix (Fin m × Fin k) (Fin m × Fin k) ℂ) :
    Matrix (Fin m × Fin k) (Fin m × Fin k) ℂ :=
  fun p q => if p.2 = q.2 then A p q else 0

@[simp] lemma pinchAncilla_apply
    (A : Matrix (Fin m × Fin k) (Fin m × Fin k) ℂ)
    (p q : Fin m × Fin k) :
    pinchAncilla A p q = if p.2 = q.2 then A p q else 0 := rfl

lemma pinchAncilla_isHermitian
    (A : Matrix (Fin m × Fin k) (Fin m × Fin k) ℂ)
    (hA : A.IsHermitian) :
    (pinchAncilla A).IsHermitian := by
  classical
  unfold Matrix.IsHermitian at hA ⊢
  ext p q
  by_cases h : p.2 = q.2
  ·
    have hEntry : star (A q p) = A p q := by
      simpa [Matrix.conjTranspose_apply] using congrArg (fun M => M p q) hA
    simp [Matrix.conjTranspose_apply, pinchAncilla]
    rw [if_pos h.symm, if_pos h]
    simpa using hEntry
  ·
    have hqp : q.2 ≠ p.2 := by
      intro hqp
      exact h hqp.symm
    simp [Matrix.conjTranspose_apply, pinchAncilla]
    rw [if_neg hqp, if_neg h]
    simp

lemma trace_pinchAncilla
    (A : Matrix (Fin m × Fin k) (Fin m × Fin k) ℂ) :
    Matrix.trace (pinchAncilla A) = Matrix.trace A := by
  classical
  unfold Matrix.trace
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [pinchAncilla]

/-- Diagonal mask selecting the ancilla block indexed by `l`. -/
def ancillaMask (l : Fin k) :
    Matrix (Fin m × Fin k) (Fin m × Fin k) ℂ :=
  Matrix.diagonal fun p => if p.2 = l then (1 : ℂ) else 0

/-- Extract the `(m × m)` block along the ancilla index `l`. -/
def ancillaBlock
    (A : Matrix (Fin m × Fin k) (Fin m × Fin k) ℂ) (l : Fin k) :
    Matrix (Fin m) (Fin m) ℂ :=
  A.submatrix (fun i => (i, l)) (fun j => (j, l))

@[simp] lemma ancillaBlock_apply
    (A : Matrix (Fin m × Fin k) (Fin m × Fin k) ℂ)
    (l : Fin k) (i j : Fin m) :
    ancillaBlock (m:=m) (k:=k) A l i j = A (i, l) (j, l) := rfl

lemma ancillaBlock_isHermitian
    (A : Matrix (Fin m × Fin k) (Fin m × Fin k) ℂ)
    (hA : A.IsHermitian) (l : Fin k) :
    (ancillaBlock (m:=m) (k:=k) A l).IsHermitian := by
  classical
  simpa [ancillaBlock] using
    (Matrix.IsHermitian.submatrix
      (A := A) hA (fun i : Fin m => (i, l)))

lemma ancillaBlock_posSemidef
    (A : Matrix (Fin m × Fin k) (Fin m × Fin k) ℂ)
    (hA : PosSemidef A) (l : Fin k) :
    PosSemidef (ancillaBlock (m:=m) (k:=k) A l) := by
  classical
  simpa [ancillaBlock] using
    (PosSemidef.submatrix (f := fun i : Fin m => (i, l)) (A := A) hA)

lemma ancillaBlock_trace
    (A : Matrix (Fin m × Fin k) (Fin m × Fin k) ℂ) (l : Fin k) :
    Matrix.trace (ancillaBlock (m:=m) (k:=k) A l) =
      ∑ i : Fin m, A (i, l) (i, l) := by
  classical
  simp [ancillaBlock, Matrix.trace, Matrix.submatrix]

lemma ancillaBlock_trace_sum
    (A : Matrix (Fin m × Fin k) (Fin m × Fin k) ℂ) :
    (∑ l : Fin k, Matrix.trace (ancillaBlock (m:=m) (k:=k) A l)) =
      Matrix.trace A := by
  classical
  have hleft :
      (∑ l : Fin k, Matrix.trace (ancillaBlock (m:=m) (k:=k) A l)) =
        ∑ l : Fin k, ∑ i : Fin m, A (i, l) (i, l) := by
    simp [ancillaBlock_trace]
  have hswap :
      (∑ l : Fin k, ∑ i : Fin m, A (i, l) (i, l)) =
        ∑ pair : Fin k × Fin m, A (pair.2, pair.1) (pair.2, pair.1) := by
    simpa [Finset.univ_product_univ] using
      (Finset.sum_product
        (s := (Finset.univ : Finset (Fin k)))
        (t := (Finset.univ : Finset (Fin m)))
        (f := fun p : Fin k × Fin m =>
          A (p.2, p.1) (p.2, p.1))).symm
  have hswap' :
      (∑ pair : Fin k × Fin m, A (pair.2, pair.1) (pair.2, pair.1)) =
        ∑ pair : Fin m × Fin k, A (pair.1, pair.2) (pair.1, pair.2) := by
    have :=
      Fintype.sum_equiv (Equiv.prodComm (Fin k) (Fin m))
        (fun pair : Fin k × Fin m =>
          A (pair.2, pair.1) (pair.2, pair.1))
        (fun pair : Fin m × Fin k =>
          A (pair.1, pair.2) (pair.1, pair.2))
        (by intro pair; simp)
    simpa using this
  have htrace :
      (∑ pair : Fin m × Fin k, A (pair.1, pair.2) (pair.1, pair.2)) =
        Matrix.trace A := by
    simp [Matrix.trace]
  simp [hleft, hswap, hswap', htrace]

def ancillaMatrix (ρ : Density (m * k)) :
    Matrix (Fin m × Fin k) (Fin m × Fin k) ℂ :=
  Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
    (finProdFinEquiv (m:=m) (n:=k)).symm ρ.mat

lemma ancillaMatrix_isHermitian (ρ : Density (m * k)) :
    (ancillaMatrix (m:=m) (k:=k) ρ).IsHermitian := by
  classical
  set e : Fin m × Fin k ≃ Fin (m * k) := finProdFinEquiv (m:=m) (n:=k)
  have hA : ρ.mat.conjTranspose = ρ.mat := by
    simpa [Matrix.IsHermitian] using ρ.mat_isHermitian
  unfold ancillaMatrix
  unfold Matrix.IsHermitian
  simpa [e, Matrix.conjTranspose_reindex] using congrArg (Matrix.reindex e.symm e.symm) hA

lemma ancillaMatrix_posSemidef (ρ : Density (m * k)) :
    PosSemidef (ancillaMatrix (m:=m) (k:=k) ρ) := by
  classical
  have :=
    PosSemidef.reindex_equiv
      (ι := Fin (m * k))
      (κ := Fin m × Fin k)
      (e := (finProdFinEquiv (m:=m) (n:=k)).symm)
      (A := ρ.mat) ρ.posSemidef
  simpa [ancillaMatrix]
    using this

lemma ancillaMatrix_trace (ρ : Density (m * k)) :
    Matrix.trace (ancillaMatrix (m:=m) (k:=k) ρ) =
      Matrix.trace ρ.mat := by
  classical
  set e : Fin m × Fin k ≃ Fin (m * k) := finProdFinEquiv (m:=m) (n:=k)
  have hreindex :
      ancillaMatrix (m:=m) (k:=k) ρ = ρ.mat.submatrix e e := by
    ext p q
    simp [ancillaMatrix, Matrix.reindex_apply, Matrix.submatrix, e]
  simpa [hreindex] using trace_submatrix_equiv e ρ.mat

def ancillaWeight (ρ : Density (m * k)) (l : Fin k) : ℝ :=
  (Matrix.trace
      (ancillaBlock (m:=m) (k:=k) (ancillaMatrix (m:=m) (k:=k) ρ) l)).re

lemma ancillaWeight_nonneg (ρ : Density (m * k)) (l : Fin k) :
    0 ≤ ancillaWeight (m:=m) (k:=k) ρ l := by
  classical
  have hPos :
      PosSemidef
        (ancillaBlock (m:=m) (k:=k)
          (ancillaMatrix (m:=m) (k:=k) ρ) l) :=
    ancillaBlock_posSemidef
      (A := ancillaMatrix (m:=m) (k:=k) ρ)
      (ancillaMatrix_posSemidef (m:=m) (k:=k) ρ) l
  simpa [ancillaWeight] using
    (PosSemidef.trace_real_nonneg (ι := Fin m) (A :=
      ancillaBlock (m:=m) (k:=k)
        (ancillaMatrix (m:=m) (k:=k) ρ) l) hPos)

lemma ancillaWeight_sum_eq_one (ρ : Density (m * k)) :
    ∑ l : Fin k, ancillaWeight (m:=m) (k:=k) ρ l = 1 := by
  classical
  have hsum :=
    ancillaBlock_trace_sum
      (m:=m) (k:=k)
      (A := ancillaMatrix (m:=m) (k:=k) ρ)
  have hsumRe :
      ∑ l : Fin k,
          (Matrix.trace
              (ancillaBlock (m:=m) (k:=k)
                (ancillaMatrix (m:=m) (k:=k) ρ) l)).re =
        (Matrix.trace (ancillaMatrix (m:=m) (k:=k) ρ)).re := by
    -- `Complex.re` is additive, so we can push it inside the sum using `map_sum`.
    let reAdd : ℂ →+ ℝ :=
      { toFun := Complex.re
        map_zero' := by simp
        map_add' := by intro x y; simp }
    have := congrArg reAdd hsum
    simpa [reAdd, map_sum] using this
  have htraceRe :
      (Matrix.trace (ancillaMatrix (m:=m) (k:=k) ρ)).re = 1 := by
    have htrace :=
      congrArg Complex.re (ancillaMatrix_trace (m:=m) (k:=k) ρ)
    have hρ : (Matrix.trace ρ.mat).re = 1 := by
      simpa [Density.trace] using ρ.realTrace_eq_one
    exact htrace.trans hρ
  simpa [ancillaWeight] using hsumRe.trans htraceRe

lemma ancillaBlock_trace_eq_weight (ρ : Density (m * k)) (l : Fin k) :
    Matrix.trace
        (ancillaBlock (m:=m) (k:=k)
          (ancillaMatrix (m:=m) (k:=k) ρ) l) =
      (ancillaWeight (m:=m) (k:=k) ρ l : ℂ) := by
  classical
  set A :=
    ancillaBlock (m:=m) (k:=k)
      (ancillaMatrix (m:=m) (k:=k) ρ) l
  have hHerm : A.IsHermitian :=
    ancillaBlock_isHermitian
      (A := ancillaMatrix (m:=m) (k:=k) ρ)
      (ancillaMatrix_isHermitian (m:=m) (k:=k) ρ) l
  have him : (Matrix.trace A).im = 0 := by
    have htrace : Matrix.trace A = Matrix.trace A.conjTranspose := by
      simpa [A] using (congrArg Matrix.trace hHerm).symm
    have hconj : Matrix.trace A.conjTranspose = star (Matrix.trace A) :=
      Matrix.trace_conjTranspose A
    have hstar : star (Matrix.trace A) = Matrix.trace A := by
      have : Matrix.trace A = star (Matrix.trace A) := by
        calc
          Matrix.trace A = Matrix.trace A.conjTranspose := htrace
          _ = star (Matrix.trace A) := hconj
      exact this.symm
    have hconj' : conj (Matrix.trace A) = Matrix.trace A := by
      simpa [Complex.star_def] using hstar
    exact (Complex.conj_eq_iff_im).1 hconj'
  apply Complex.ext <;> simp [ancillaWeight, A, him]

lemma ancillaBlock_eq_zero_of_weight_zero
    (ρ : Density (m * k)) (l : Fin k)
    (hw : ancillaWeight (m:=m) (k:=k) ρ l = 0) :
    ancillaBlock (m:=m) (k:=k)
        (ancillaMatrix (m:=m) (k:=k) ρ) l = 0 := by
  classical
  have hHerm :=
    ancillaBlock_isHermitian
      (A := ancillaMatrix (m:=m) (k:=k) ρ)
      (ancillaMatrix_isHermitian (m:=m) (k:=k) ρ) l
  have hPos :=
    ancillaBlock_posSemidef
      (A := ancillaMatrix (m:=m) (k:=k) ρ)
      (ancillaMatrix_posSemidef (m:=m) (k:=k) ρ) l
  have htrace :
      Matrix.trace
          (ancillaBlock (m:=m) (k:=k)
            (ancillaMatrix (m:=m) (k:=k) ρ) l) = 0 := by
    simp [ancillaBlock_trace_eq_weight (ρ := ρ) (l := l), hw]
  exact HeytingLean.Quantum.hermitian_posSemidef_trace_zero_eq_zero
    (n:=m)
    (A := ancillaBlock (m:=m) (k:=k) (ancillaMatrix (m:=m) (k:=k) ρ) l)
    hHerm hPos htrace

noncomputable def basisPointDensity (hm_pos : 0 < m) : Density m := by
  classical
  let i0 : Fin m := ⟨0, hm_pos⟩
  let d : Fin m → ℝ := fun i => if i = i0 then (1 : ℝ) else 0
  have hnonneg : ∀ i, 0 ≤ d i := by
    intro i
    by_cases hi : i = i0
    · simp [d, hi]
    · simp [d, hi]
  have hsum :
      ∑ i : Fin m, d i = 1 := by
    classical
    have hsum' : (∑ i : Fin m, d i) = d i0 := by
      simpa using
        (Finset.sum_eq_single (s := (Finset.univ : Finset (Fin m))) (f := fun i => d i) i0
          (by
            intro i _ hne
            simp [d, hne])
          (by
            intro hi0
            exact (hi0 (by simp)).elim))
    refine hsum'.trans ?_
    simp [d]
  exact Density.diagDensity d (by intro; exact hnonneg _)
    hsum

noncomputable def ancillaBlockDensity (ρ : Density (m * k)) (l : Fin k) :
    Density m := by
  classical
  have hm_pos : 0 < m := by
    have hmk := Density.dim_pos (ρ := ρ)
    have hm_ne : m ≠ 0 := by
      intro hm0
      subst hm0
      have hmk' := hmk
      simp at hmk'
    exact Nat.pos_of_ne_zero hm_ne
  by_cases hw : ancillaWeight (m:=m) (k:=k) ρ l = 0
  · exact basisPointDensity (m:=m) hm_pos
  ·
    have hw_pos :
        0 < ancillaWeight (m:=m) (k:=k) ρ l :=
      lt_of_le_of_ne' (ancillaWeight_nonneg (m:=m) (k:=k) ρ l) hw
    let scale : ℝ := (ancillaWeight (m:=m) (k:=k) ρ l)⁻¹
    have hscale_nonneg : 0 ≤ scale :=
      inv_nonneg.mpr hw_pos.le
    have hHerm :
        (ancillaBlock (m:=m) (k:=k)
            (ancillaMatrix (m:=m) (k:=k) ρ) l).IsHermitian :=
      ancillaBlock_isHermitian
        (A := ancillaMatrix (m:=m) (k:=k) ρ)
        (ancillaMatrix_isHermitian (m:=m) (k:=k) ρ) l
    have hPos :
        PosSemidef
          (ancillaBlock (m:=m) (k:=k)
            (ancillaMatrix (m:=m) (k:=k) ρ) l) :=
      ancillaBlock_posSemidef
        (A := ancillaMatrix (m:=m) (k:=k) ρ)
        (ancillaMatrix_posSemidef (m:=m) (k:=k) ρ) l
    refine
      { mat :=
          ((scale : ℂ) •
            ancillaBlock (m:=m) (k:=k)
              (ancillaMatrix (m:=m) (k:=k) ρ) l)
        hermitian := by
          -- Real scalings preserve Hermitian matrices.
          unfold Matrix.IsHermitian at hHerm ⊢
          simp [Matrix.conjTranspose_smul, hHerm]
        traceOne := ?_
        posSemidef := PosSemidef.smul_real hPos hscale_nonneg }
    have htrace :=
      ancillaBlock_trace_eq_weight (m:=m) (k:=k) (ρ := ρ) (l := l)
    have hw_ne : ancillaWeight (m:=m) (k:=k) ρ l ≠ 0 :=
      by exact hw
    simp [Matrix.trace_smul, scale, htrace, hw_ne]

lemma ancillaBlock_weight_smul_density
    (ρ : Density (m * k)) (l : Fin k) :
    (ancillaWeight (m:=m) (k:=k) ρ l : ℂ) •
        (ancillaBlockDensity (m:=m) (k:=k) ρ l).mat =
      ancillaBlock (m:=m) (k:=k)
        (ancillaMatrix (m:=m) (k:=k) ρ) l := by
  classical
  by_cases hw : ancillaWeight (m:=m) (k:=k) ρ l = 0
  ·
    have hzero :=
      ancillaBlock_eq_zero_of_weight_zero
        (m:=m) (k:=k) (ρ := ρ) (l := l) hw
    simp [ancillaBlockDensity, hw, hzero]
  ·
    have hw_ne : ancillaWeight (m:=m) (k:=k) ρ l ≠ 0 := hw
    have hmat :
        (ancillaBlockDensity (m:=m) (k:=k) ρ l).mat =
          ((ancillaWeight (m:=m) (k:=k) ρ l)⁻¹ : ℂ) •
            ancillaBlock (m:=m) (k:=k)
              (ancillaMatrix (m:=m) (k:=k) ρ) l := by
      simp [ancillaBlockDensity, hw]
    have hw_ne' :
        (ancillaWeight (m:=m) (k:=k) ρ l : ℝ) ≠ 0 :=
      hw_ne
    have hw_ne_complex :
        (ancillaWeight (m:=m) (k:=k) ρ l : ℂ) ≠ 0 := by
      exact_mod_cast hw_ne'
    simp [hmat, hw_ne_complex]


lemma ancillaMask_mul_apply
    (A : Matrix (Fin m × Fin k) (Fin m × Fin k) ℂ)
    (l : Fin k) (p q : Fin m × Fin k) :
    (ancillaMask (m:=m) (k:=k) l * A *
        ancillaMask (m:=m) (k:=k) l) p q =
      if p.2 = l ∧ q.2 = l then A p q else 0 := by
  classical
  have hcalc :
      (ancillaMask (m:=m) (k:=k) l * A *
        ancillaMask (m:=m) (k:=k) l) p q =
      ((if p.2 = l then (1 : ℂ) else 0) * A p q) *
        (if q.2 = l then (1 : ℂ) else 0) := by
    simp [ancillaMask]
  by_cases hp : p.2 = l <;> by_cases hq : q.2 = l <;>
    simp [hcalc, hp, hq]

lemma pinchAncilla_eq_sum
    (A : Matrix (Fin m × Fin k) (Fin m × Fin k) ℂ) :
    pinchAncilla A =
      ∑ l : Fin k,
        ancillaMask (m:=m) (k:=k) l * A *
          ancillaMask (m:=m) (k:=k) l := by
  classical
  ext p q
  -- evaluate the matrix sum entrywise
  simp [Matrix.sum_apply]
  have hterm :
      ∀ l : Fin k,
        (ancillaMask (m:=m) (k:=k) l * A *
            ancillaMask (m:=m) (k:=k) l) p q =
          if p.2 = l ∧ q.2 = l then A p q else 0 :=
    fun l => ancillaMask_mul_apply (A := A) (l := l) (p := p) (q := q)
  have hsum :
      (∑ l : Fin k,
          (ancillaMask (m:=m) (k:=k) l * A *
            ancillaMask (m:=m) (k:=k) l) p q) =
        ∑ l : Fin k,
          (if p.2 = l ∧ q.2 = l then A p q else 0) :=
    Finset.sum_congr rfl fun l _ => hterm l
  by_cases h : p.2 = q.2
  · have hSum :
        (∑ l : Fin k, if p.2 = l ∧ q.2 = l then A p q else 0) =
          A p q := by
      classical
      have hSum' :
          (∑ l : Fin k, if p.2 = l ∧ q.2 = l then A p q else 0) =
            (if p.2 = p.2 ∧ q.2 = p.2 then A p q else 0) := by
        simpa using
          (Finset.sum_eq_single
            (s := (Finset.univ : Finset (Fin k)))
            (f := fun l : Fin k => if p.2 = l ∧ q.2 = l then A p q else 0)
            (a := p.2)
            (by
              intro l _ hl
              have hp : p.2 ≠ l := by simpa [eq_comm] using hl
              simp [hp])
            (by
              intro hnot
              exact (hnot (by simp)).elim))
      refine hSum'.trans ?_
      simp [h]
    simp [h, hsum]
  · have hSum :
        (∑ l : Fin k, if p.2 = l ∧ q.2 = l then A p q else 0) = 0 := by
      classical
      have hzero :
          ∀ l : Fin k,
            (if p.2 = l ∧ q.2 = l then A p q else 0) = 0 := by
        intro l
        by_cases hpq : p.2 = l ∧ q.2 = l
        · exact (h (hpq.1.trans hpq.2.symm)).elim
        · simp [hpq]
      simp [hzero]
    simp [h, hsum, hSum]

lemma pinchAncilla_eq_blockDiagonal
    (A : Matrix (Fin m × Fin k) (Fin m × Fin k) ℂ) :
    pinchAncilla A =
      Matrix.blockDiagonal fun l : Fin k =>
        ancillaBlock (m:=m) (k:=k) A l := by
  classical
  ext p q
  by_cases h : p.2 = q.2
  ·
    have hp : (p.1, q.2) = p := by
      ext <;> simp [h]
    simp [pinchAncilla, Matrix.blockDiagonal_apply, ancillaBlock_apply, h, hp]
  ·
    simp [pinchAncilla, Matrix.blockDiagonal_apply, h]

lemma ancillaMask_conjTranspose
    (l : Fin k) :
    (ancillaMask (m:=m) (k:=k) l).conjTranspose =
      ancillaMask (m:=m) (k:=k) l := by
  classical
  ext p q
  by_cases h : p = q
  · subst q
    simp [ancillaMask]
  ·
    have h' : q ≠ p := by
      simpa [eq_comm] using h
    simp [ancillaMask, Matrix.conjTranspose_apply, h, h']

lemma pinchAncilla_posSemidef
    (A : Matrix (Fin m × Fin k) (Fin m × Fin k) ℂ)
    (hA : PosSemidef A) :
    PosSemidef (pinchAncilla A) := by
  classical
  have hEach :
      ∀ l : Fin k,
        PosSemidef
          (ancillaMask (m:=m) (k:=k) l * A *
            ancillaMask (m:=m) (k:=k) l) := by
    intro l
    simpa [ancillaMask_conjTranspose] using
      PosSemidef.conj_mul (A := A) hA
        (ancillaMask (m:=m) (k:=k) l)
  have hSum :
      PosSemidef
        (∑ l : Fin k,
          ancillaMask (m:=m) (k:=k) l * A *
            ancillaMask (m:=m) (k:=k) l) :=
    PosSemidef.sum
      (s := (Finset.univ : Finset (Fin k)))
      (f := fun l =>
        ancillaMask (m:=m) (k:=k) l * A *
          ancillaMask (m:=m) (k:=k) l)
      (fun l _ => hEach l)
  simpa [pinchAncilla_eq_sum] using hSum

lemma partialTrace_pinchAncilla
    (A : Matrix (Fin m × Fin k) (Fin m × Fin k) ℂ) :
    partialTrace (pinchAncilla A) = partialTrace A := by
  classical
  ext i j
  simp [partialTrace, pinchAncilla]

/-- Pinch a density matrix along the ancillary register. -/
def pinchAncillaDensity {m k : ℕ} (ρ : Density (m * k)) : Density (m * k) := by
  classical
  let e : Fin m × Fin k ≃ Fin (m * k) := finProdFinEquiv
  let subρ :=
    ρ.mat.submatrix
      (fun ik : Fin m × Fin k => e ik)
      (fun ik : Fin m × Fin k => e ik)
  refine
    { mat :=
        (pinchAncilla subρ).submatrix
          (fun idx : Fin (m * k) => e.symm idx)
          (fun idx : Fin (m * k) => e.symm idx)
      hermitian := ?_
      traceOne := ?_
      posSemidef := ?_ }
  ·
    have hHerm :
        subρ.IsHermitian :=
      (Matrix.IsHermitian.submatrix
        (A := ρ.mat) ρ.mat_isHermitian
        (fun ik : Fin m × Fin k => e ik))
    have hPinchHerm :
        (pinchAncilla subρ).IsHermitian :=
      pinchAncilla_isHermitian (A := subρ) hHerm
    simpa using
      (Matrix.IsHermitian.submatrix
        (A := pinchAncilla subρ) hPinchHerm
        (fun idx : Fin (m * k) => e.symm idx))
  ·
    have hTrace_sub :
        Matrix.trace subρ = Matrix.trace ρ.mat :=
      trace_submatrix_equiv e ρ.mat
    have hTrace_pinch :
        Matrix.trace (pinchAncilla subρ) =
          Matrix.trace subρ :=
      trace_pinchAncilla (A := subρ)
    have hTrace_back :
        Matrix.trace
            ((pinchAncilla subρ).submatrix
              (fun idx => e.symm idx) (fun idx => e.symm idx)) =
          Matrix.trace (pinchAncilla subρ) :=
      trace_submatrix_equiv e.symm (pinchAncilla subρ)
    have :
        Matrix.trace
            ((pinchAncilla subρ).submatrix
              (fun idx => e.symm idx) (fun idx => e.symm idx)) =
          Matrix.trace ρ.mat := by
      simpa [hTrace_pinch, hTrace_sub] using hTrace_back
    simpa using this.trans ρ.traceOne
  ·
    have hPos :
        PosSemidef subρ :=
      PosSemidef.submatrix
        (f := fun ik : Fin m × Fin k => e ik)
        (A := ρ.mat) ρ.posSemidef
    have hPinchPos :
        PosSemidef (pinchAncilla subρ) :=
      pinchAncilla_posSemidef (A := subρ) hPos
    simpa using
      (PosSemidef.submatrix
        (f := fun idx : Fin (m * k) => e.symm idx)
        (A := pinchAncilla subρ) hPinchPos)

lemma partialTraceDensity_pinchAncilla {m k : ℕ}
    (ρ : Density (m * k)) :
    partialTraceDensity (pinchAncillaDensity (m:=m) (k:=k) ρ) =
      partialTraceDensity ρ := by
  classical
  let e : Fin m × Fin k ≃ Fin (m * k) := finProdFinEquiv (m:=m) (n:=k)
  let subρ :=
    ρ.mat.submatrix
      (fun ik : Fin m × Fin k => e ik)
      (fun ik : Fin m × Fin k => e ik)
  have hsub :
      ((pinchAncillaDensity (m:=m) (k:=k) ρ).mat).submatrix
          (fun ik : Fin m × Fin k => e ik)
          (fun ik : Fin m × Fin k => e ik) =
        pinchAncilla subρ := by
    have heComp : (fun ik : Fin m × Fin k => e.symm (e ik)) = id := by
      funext ik
      simp [e]
    calc
      ((pinchAncillaDensity (m:=m) (k:=k) ρ).mat).submatrix
            (fun ik : Fin m × Fin k => e ik)
            (fun ik : Fin m × Fin k => e ik) =
          ((pinchAncilla subρ).submatrix (fun idx => e.symm idx) fun idx => e.symm idx).submatrix
              (fun ik : Fin m × Fin k => e ik)
              (fun ik : Fin m × Fin k => e ik) := by
            simp [pinchAncillaDensity, subρ, e]
      _ = (pinchAncilla subρ).submatrix (fun ik : Fin m × Fin k => e.symm (e ik))
            (fun ik : Fin m × Fin k => e.symm (e ik)) := by
          ext i j
          rfl
      _ = pinchAncilla subρ := by
          -- reduce the reindexing maps to `id` and collapse the `submatrix`
          rw [heComp]
          simp
  refine Density.ext ?_
  have hPinch :
      (partialTraceDensity (pinchAncillaDensity (m:=m) (k:=k) ρ)).mat =
        partialTrace (pinchAncilla subρ) := by
    have hdef :
        (partialTraceDensity (pinchAncillaDensity (m:=m) (k:=k) ρ)).mat =
          partialTrace
            (((pinchAncillaDensity (m:=m) (k:=k) ρ).mat).submatrix
              (fun ik : Fin m × Fin k => e ik)
              (fun ik : Fin m × Fin k => e ik)) := by
      simp [partialTraceDensity, e]
    simpa [hdef] using congrArg partialTrace hsub
  have hOrig :
      (partialTraceDensity ρ).mat =
        partialTrace subρ := by
    simp [partialTraceDensity, subρ, e]
  have hTrace :=
      partialTrace_pinchAncilla (A := subρ)
  simp [hPinch, hOrig, hTrace]

lemma pinchAncillaDensity_reindex_blockDiagonal {m k : ℕ}
    (ρ : Density (m * k)) :
    Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
        (finProdFinEquiv (m:=m) (n:=k)).symm
        (pinchAncillaDensity (m:=m) (k:=k) ρ).mat =
      Matrix.blockDiagonal fun l : Fin k =>
        ancillaBlock (m:=m) (k:=k)
          (Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
            (finProdFinEquiv (m:=m) (n:=k)).symm ρ.mat) l := by
  classical
  set e : Fin m × Fin k ≃ Fin (m * k) := finProdFinEquiv (m:=m) (n:=k)
  let subρ :=
    ρ.mat.submatrix
      (fun ik : Fin m × Fin k => e ik)
      (fun ik : Fin m × Fin k => e ik)
  have hsub :
      ((pinchAncillaDensity (m:=m) (k:=k) ρ).mat).submatrix
          (fun ik : Fin m × Fin k => e ik)
          (fun ik : Fin m × Fin k => e ik) =
        pinchAncilla subρ := by
    have heComp : (fun ik : Fin m × Fin k => e.symm (e ik)) = id := by
      funext ik
      simp [e]
    calc
      ((pinchAncillaDensity (m:=m) (k:=k) ρ).mat).submatrix
            (fun ik : Fin m × Fin k => e ik)
            (fun ik : Fin m × Fin k => e ik) =
          ((pinchAncilla subρ).submatrix (fun idx => e.symm idx) fun idx => e.symm idx).submatrix
              (fun ik : Fin m × Fin k => e ik)
              (fun ik : Fin m × Fin k => e ik) := by
            simp [pinchAncillaDensity, subρ, e]
      _ = (pinchAncilla subρ).submatrix (fun ik : Fin m × Fin k => e.symm (e ik))
            (fun ik : Fin m × Fin k => e.symm (e ik)) := by
          ext i j
          rfl
      _ = pinchAncilla subρ := by
          rw [heComp]
          simp
  have hreindex :
      Matrix.reindex e.symm e.symm
          (pinchAncillaDensity (m:=m) (k:=k) ρ).mat =
        pinchAncilla subρ := by
    simpa [Matrix.reindex_apply] using hsub
  have hsubρ :
      Matrix.reindex e.symm e.symm ρ.mat = subρ := by
    simp [Matrix.reindex_apply, subρ]
  simpa [hsubρ, pinchAncilla_eq_blockDiagonal (m:=m) (k:=k) (A := subρ)]
    using hreindex

end

end ActiveInference
end Quantum
end HeytingLean
