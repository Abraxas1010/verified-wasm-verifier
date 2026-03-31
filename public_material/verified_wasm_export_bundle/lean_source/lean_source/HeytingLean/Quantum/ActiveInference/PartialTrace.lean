import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import HeytingLean.Quantum.QChannel
import HeytingLean.Quantum.QState
import HeytingLean.Quantum.ActiveInference.OperatorConvex

namespace Matrix

open scoped BigOperators

variable {ι : Type*} {n : Type*}

lemma isHermitian_sum {s : Finset ι} [DecidableEq ι] {f : ι → Matrix n n ℂ}
    (h : ∀ i ∈ s, (f i).IsHermitian) :
    (∑ i ∈ s, f i).IsHermitian := by
  classical
  refine
    Finset.induction_on (s := s)
      (motive :=
        fun t => (∀ i ∈ t, (f i).IsHermitian) → (∑ i ∈ t, f i).IsHermitian)
      ?base ?step h
  · intro _; simp
  · intro a t ha ih hAll
    have hfa : (f a).IsHermitian := hAll _ (by simp)
    have hRest : ∀ i ∈ t, (f i).IsHermitian := fun i hi => hAll i (by simp [hi])
    have hSum : (∑ i ∈ t, f i).IsHermitian := ih hRest
    simpa [Finset.sum_insert, ha] using hfa.add hSum

end Matrix

/- Finite-dimensional partial trace helper ... -/

namespace HeytingLean
namespace Quantum
namespace ActiveInference

open scoped Matrix BigOperators
open Matrix

noncomputable section

variable {m k : ℕ}

/-- Partial trace over the second (ancilla) subsystem.  This implementation
unfolds to the usual summation over the ancilla index. -/
def partialTrace (A : Matrix (Fin m × Fin k) (Fin m × Fin k) ℂ) :
    Matrix (Fin m) (Fin m) ℂ :=
  fun i j => ∑ l : Fin k, A (i, l) (j, l)

lemma partialTrace_eq_sum_submatrix
    (A : Matrix (Fin m × Fin k) (Fin m × Fin k) ℂ) :
    partialTrace A =
      ∑ l : Fin k,
        A.submatrix (fun i => (i, l)) (fun j => (j, l)) := by
  classical
  ext i j
  simpa [partialTrace, Matrix.submatrix] using
    (Matrix.sum_apply i j (Finset.univ : Finset (Fin k))
        (fun l : Fin k =>
          A.submatrix (fun i : Fin m => (i, l)) (fun j : Fin m => (j, l)))).symm

lemma partialTrace_isHermitian
    (A : Matrix (Fin m × Fin k) (Fin m × Fin k) ℂ)
    (hA : A.IsHermitian) :
    (partialTrace A).IsHermitian := by
  classical
  have hSlice :
      ∀ l : Fin k,
        (A.submatrix (fun i => (i, l)) (fun j => (j, l))).IsHermitian :=
    fun l => hA.submatrix _
  simpa [partialTrace_eq_sum_submatrix] using
    Matrix.isHermitian_sum
      (s := (Finset.univ : Finset (Fin k)))
      (f := fun l => A.submatrix (fun i => (i, l)) (fun j => (j, l)))
      (by
        intro l _
        simpa using hSlice l)

lemma partialTrace_posSemidef
    (A : Matrix (Fin m × Fin k) (Fin m × Fin k) ℂ)
    (hA : PosSemidef A) :
    PosSemidef (partialTrace A) := by
  classical
  have hSlice :
      ∀ l : Fin k,
        PosSemidef
          (A.submatrix (fun i => (i, l)) (fun j => (j, l))) :=
    fun l => PosSemidef.submatrix (f := fun i : Fin m => (i, l)) (A := A) hA
  have :
      PosSemidef
        (∑ l : Fin k,
          A.submatrix (fun i => (i, l)) (fun j => (j, l))) :=
    PosSemidef.sum (s := (Finset.univ : Finset (Fin k)))
      (f := fun l => A.submatrix (fun i => (i, l)) (fun j => (j, l)))
      (by
        intro l _
        simpa using hSlice l)
  simpa [partialTrace_eq_sum_submatrix] using this

lemma partialTrace_trace_eq (A : Matrix (Fin m × Fin k) (Fin m × Fin k) ℂ) :
    Matrix.trace (partialTrace A) = Matrix.trace A := by
  classical
  unfold partialTrace Matrix.trace
  -- turn the iterated sum into a single sum over the product index
  have :=
    (Finset.sum_product
        (s := (Finset.univ : Finset (Fin m)))
        (t := (Finset.univ : Finset (Fin k)))
        (f := fun p : Fin m × Fin k => A (p.1, p.2) (p.1, p.2))).symm
  -- simplify both sides of the equality returned by `sum_product`
  simpa [Finset.univ_product_univ] using this

lemma trace_submatrix_equiv {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (e : m ≃ n) (A : Matrix n n ℂ) :
    Matrix.trace (A.submatrix e e) = Matrix.trace A := by
  classical
  simpa [Matrix.trace, Matrix.submatrix] using
    (Fintype.sum_equiv e (fun i : m => A (e i) (e i)) (fun j : n => A j j)
      (fun _ => rfl))

def partialTraceDensity {m k : ℕ} (ρ : Density (m * k)) : Density m := by
  classical
  let e : Fin m × Fin k ≃ Fin (m * k) := finProdFinEquiv
  let subρ :=
    ρ.mat.submatrix
      (fun ik : Fin m × Fin k => e ik)
      (fun ik : Fin m × Fin k => e ik)
  refine
    { mat := partialTrace subρ
      hermitian := ?_
      traceOne := ?_
      posSemidef := ?_ }
  ·
    have hHerm :
        subρ.IsHermitian :=
      (Matrix.IsHermitian.submatrix
        (A := ρ.mat) ρ.mat_isHermitian
        (fun ik : Fin m × Fin k => e ik))
    simpa using partialTrace_isHermitian (A := subρ) hHerm
  ·
    have htrace :=
      partialTrace_trace_eq (A := subρ)
    have hsub :
        Matrix.trace subρ = Matrix.trace ρ.mat :=
      trace_submatrix_equiv e ρ.mat
    have htrace' :
        Matrix.trace (partialTrace subρ) = Matrix.trace ρ.mat := by
      simpa [hsub] using htrace
    simpa using htrace'.trans ρ.traceOne
  ·
    have hPos :
        PosSemidef subρ :=
      PosSemidef.submatrix
        (f := fun ik : Fin m × Fin k => e ik) (A := ρ.mat) ρ.posSemidef
    simpa using partialTrace_posSemidef (A := subρ) hPos

lemma partialTrace_diagonal {m k : ℕ} (d : Fin m × Fin k → ℂ) :
    partialTrace (Matrix.diagonal fun p => d p) =
      Matrix.diagonal fun i => ∑ l : Fin k, d (i, l) := by
  classical
  ext i j
  by_cases h : i = j
  · subst j
    simp [partialTrace]
  ·
    simp [partialTrace, h, Finset.sum_const_zero]

lemma partialTrace_diagonal_real {m k : ℕ} (d : Fin m × Fin k → ℝ) :
    partialTrace (Matrix.diagonal fun p => (d p : ℂ)) =
      Matrix.diagonal fun i => (∑ l : Fin k, d (i, l) : ℂ) := by
  classical
  simpa using
    (partialTrace_diagonal (m:=m) (k:=k) (d := fun p => (d p : ℂ)))

lemma trace_partialTrace_diagonal_real {m k : ℕ} (d : Fin m × Fin k → ℝ) :
    (Matrix.trace (partialTrace (Matrix.diagonal fun p => (d p : ℂ)))).re =
      ∑ i : Fin m, ∑ l : Fin k, d (i, l) := by
  classical
  have :=
    congrArg Matrix.trace (partialTrace_diagonal_real (m:=m) (k:=k) d)
  have hdiag := Matrix.trace_diagonal (fun i : Fin m => (∑ l : Fin k, d (i, l) : ℂ))
  have hleft : Matrix.trace (partialTrace (Matrix.diagonal fun p => (d p : ℂ))) =
      ∑ i : Fin m, (∑ l : Fin k, d (i, l) : ℂ) := by
    simpa using (this.trans hdiag)
  simpa [Complex.ofReal_sum] using congrArg Complex.re hleft

lemma sum_mul_log_partialTrace_le {m k : ℕ} (d : Fin m × Fin k → ℝ)
    (hd_nonneg : ∀ p, 0 ≤ d p) :
    (∑ p : Fin m × Fin k, d p * Real.log (d p)) ≤
      ∑ i : Fin m,
        (∑ l : Fin k, d (i, l)) * Real.log (∑ l : Fin k, d (i, l)) := by
  classical
  have hiter :
      (∑ p : Fin m × Fin k, d p * Real.log (d p)) =
        ∑ i : Fin m, ∑ l : Fin k, d (i, l) * Real.log (d (i, l)) := by
    classical
    simpa using
      (Fintype.sum_prod_type
        (f := fun p : Fin m × Fin k =>
          d p * Real.log (d p)))
  have hper :
      ∀ i : Fin m,
        ∑ l : Fin k, d (i, l) * Real.log (d (i, l)) ≤
          (∑ l : Fin k, d (i, l)) * Real.log (∑ l : Fin k, d (i, l)) := by
    intro i
    simpa using
      (sum_mul_log_le_total
        (s := (Finset.univ : Finset (Fin k)))
        (x := fun l : Fin k => d (i, l))
        (hx_nonneg := fun l _ => hd_nonneg (i, l)))
  have hsum :
      ∑ i : Fin m, ∑ l : Fin k, d (i, l) * Real.log (d (i, l)) ≤
        ∑ i : Fin m,
          (∑ l : Fin k, d (i, l)) * Real.log (∑ l : Fin k, d (i, l)) :=
    Finset.sum_le_sum fun i _ => hper i
  simpa [hiter] using hsum

lemma sum_logRatio_partialTrace {m k : ℕ} [NeZero k]
    (r s : Fin m × Fin k → ℝ)
    (hr_pos : ∀ p, 0 < r p) (hs_pos : ∀ p, 0 < s p) :
    (∑ p : Fin m × Fin k, r p * (Real.log (r p) - Real.log (s p))) ≥
      ∑ i : Fin m,
        (∑ l : Fin k, r (i, l)) *
          (Real.log (∑ l : Fin k, r (i, l)) -
            Real.log (∑ l : Fin k, s (i, l))) := by
  classical
  have hkpos : 0 < k := Nat.pos_of_ne_zero (NeZero.ne (n := k))
  have hrow :
      ∀ i : Fin m,
        (∑ l : Fin k,
            r (i, l) * (Real.log (r (i, l)) - Real.log (s (i, l)))) ≥
          (∑ l : Fin k, r (i, l)) *
            (Real.log (∑ l : Fin k, r (i, l)) -
              Real.log (∑ l : Fin k, s (i, l))) := by
    intro i
    have ha_pos :
        ∀ l ∈ (Finset.univ : Finset (Fin k)), 0 < r (i, l) := by
      intro l _
      simpa using hr_pos (i, l)
    have hb_pos :
        ∀ l ∈ (Finset.univ : Finset (Fin k)), 0 < s (i, l) := by
      intro l _
      simpa using hs_pos (i, l)
    have ha_sum_pos :
        0 < ∑ l : Fin k, r (i, l) := by
      classical
      let l₀ : Fin k := ⟨0, hkpos⟩
      have hmem : l₀ ∈ (Finset.univ : Finset (Fin k)) := by simp
      have hsingle :
          r (i, l₀) ≤ ∑ l : Fin k, r (i, l) :=
        Finset.single_le_sum
          (fun l _ => (hr_pos (i, l)).le)
          hmem
      exact lt_of_lt_of_le (hr_pos (i, l₀)) hsingle
    have hb_sum_pos :
        0 < ∑ l : Fin k, s (i, l) := by
      classical
      let l₀ : Fin k := ⟨0, hkpos⟩
      have hmem : l₀ ∈ (Finset.univ : Finset (Fin k)) := by simp
      have hsingle :
          s (i, l₀) ≤ ∑ l : Fin k, s (i, l) :=
        Finset.single_le_sum
          (fun l _ => (hs_pos (i, l)).le)
          hmem
      exact lt_of_lt_of_le (hs_pos (i, l₀)) hsingle
    simpa using
      (logSum_inequality
        (s := (Finset.univ : Finset (Fin k)))
        (a := fun l => r (i, l)) (b := fun l => s (i, l))
        (ha_pos := ha_pos) (hb_pos := hb_pos)
        (ha_sum_pos := ha_sum_pos) (hb_sum_pos := hb_sum_pos))
  have hsum_le :
      ∑ i : Fin m,
          (∑ l : Fin k, r (i, l)) *
            (Real.log (∑ l : Fin k, r (i, l)) -
              Real.log (∑ l : Fin k, s (i, l))) ≤
        ∑ i : Fin m,
          ∑ l : Fin k,
            r (i, l) * (Real.log (r (i, l)) - Real.log (s (i, l))) :=
    Finset.sum_le_sum fun i _ => hrow i
  have hsum_pairs :
      (∑ p : Fin m × Fin k,
          r p * (Real.log (r p) - Real.log (s p))) =
        ∑ i : Fin m, ∑ l : Fin k,
          r (i, l) * (Real.log (r (i, l)) - Real.log (s (i, l))) := by
    classical
    simpa using
      (Fintype.sum_prod_type
        (f := fun p : Fin m × Fin k =>
          r p * (Real.log (r p) - Real.log (s p))))
  have hge :
      ∑ i : Fin m, ∑ l : Fin k,
          r (i, l) * (Real.log (r (i, l)) - Real.log (s (i, l))) ≥
        ∑ i : Fin m,
          (∑ l : Fin k, r (i, l)) *
            (Real.log (∑ l : Fin k, r (i, l)) -
              Real.log (∑ l : Fin k, s (i, l))) :=
    hsum_le
  simpa [hsum_pairs] using hge

/-- Extend a density matrix by an isometry `V`.  The result is a density on the
codomain of `V` and will later feed into the Kraus/Stinespring dilation. -/
def isometryExtendDensity {m k : ℕ} (V : Matrix (Fin m) (Fin k) ℂ)
    (hV : IsometryMatrix V) (ρ : Density k) : Density m := by
  classical
  refine
    { mat := V * ρ.mat * V.conjTranspose
      hermitian := ?_
      traceOne := ?_
      posSemidef := ?_ }
  ·
    have hHerm :
        (V * ρ.mat * V.conjTranspose).IsHermitian :=
      Matrix.isHermitian_mul_mul_conjTranspose (B := V) ρ.mat_isHermitian
    simpa using hHerm
  ·
    have htrace :
        Matrix.trace (V * ρ.mat * V.conjTranspose) =
          Matrix.trace ((V.conjTranspose * V) * ρ.mat) := by
      simpa [Matrix.mul_assoc] using
        Matrix.trace_mul_comm (V * ρ.mat) V.conjTranspose
    have hV' : V.conjTranspose * V = 1 := by
      simpa [IsometryMatrix] using hV
    have htrace' :
        Matrix.trace ((V.conjTranspose * V) * ρ.mat) =
          Matrix.trace ρ.mat := by
      calc
        Matrix.trace ((V.conjTranspose * V) * ρ.mat) =
            Matrix.trace ((1 : Matrix (Fin k) (Fin k) ℂ) * ρ.mat) := by
              simp [hV']
        _ = Matrix.trace ρ.mat := by simp
    have := htrace.trans htrace'
    simpa [Density.trace] using this.trans ρ.traceOne
  ·
    have hPSD : PosSemidef (V * ρ.mat * V.conjTranspose) :=
      PosSemidef.conj_mul ρ.posSemidef V
    simpa using hPSD

/-- Every Kraus channel is the partial trace of an isometric extension with an
explicit ancilla register indexed by the Kraus operators. -/
lemma KrausChannel.map_eq_partialTrace {n m : ℕ} (Φ : KrausChannel n m)
    (ρ : Density n) :
    Φ.map ρ.mat =
      (partialTraceDensity
        (isometryExtendDensity Φ.isometryMatrix Φ.isometryMatrix_isometry ρ)).mat := by
  classical
  ext i j
  have hMap :
      Φ.map ρ.mat i j =
        ∑ l : Fin Φ.numOps,
          ((Φ.op l) * ρ.mat * (Φ.op l).conjTranspose) i j := by
    simpa [KrausChannel.map] using
      (Matrix.sum_apply i j (Finset.univ : Finset (Fin Φ.numOps))
        (fun l : Fin Φ.numOps => (Φ.op l) * ρ.mat * (Φ.op l).conjTranspose))
  have hTrace :
      (partialTraceDensity
          (isometryExtendDensity Φ.isometryMatrix Φ.isometryMatrix_isometry ρ)).mat i j =
        ∑ l : Fin Φ.numOps,
          ((Φ.op l) * ρ.mat * (Φ.op l).conjTranspose) i j := by
    simp [partialTraceDensity, partialTrace, Matrix.submatrix, isometryExtendDensity,
      KrausChannel.isometryMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply]
  simpa [hTrace] using hMap

end

end ActiveInference
end Quantum
end HeytingLean
