import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
Basic finite-dimensional quantum state scaffolding.  Everything lives in
`Matrix (Fin n) (Fin n) ℂ`, and we keep the predicates intentionally light so
follow-up passes (including tool-assisted proof search) can build the heavy
spectral/entropy lemmas on top of a clean interface.
-/

noncomputable section

open scoped Matrix ComplexConjugate

namespace HeytingLean
namespace Quantum

open Matrix Complex
open scoped BigOperators

abbrev Ket (n : ℕ) := Fin n → ℂ
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- Conjugate-symmetric dot product used throughout the quantum interface. -/
def inner {ι : Type*} [Fintype ι] [DecidableEq ι] (v w : ι → ℂ) : ℂ :=
  ∑ i, conj (v i) * w i

lemma inner_add_left {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v w u : ι → ℂ) : inner (v + w) u = inner v u + inner w u := by
  classical
  simp [inner, add_mul, Finset.sum_add_distrib]

lemma inner_add_right {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v w u : ι → ℂ) : inner v (w + u) = inner v w + inner v u := by
  classical
  simp [inner, mul_add, Finset.sum_add_distrib]

lemma inner_smul_left {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℂ) (v w : ι → ℂ) : inner (c • v) w = conj c * inner v w := by
  classical
  simp [inner, Finset.mul_sum, mul_comm, mul_left_comm]

lemma inner_smul_right {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℂ) (v w : ι → ℂ) : inner v (c • w) = c * inner v w := by
  classical
  simp [inner, Finset.mul_sum, mul_comm, mul_assoc]

lemma inner_smul_right_euclidean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℂ) (v w : EuclideanSpace ℂ ι) :
    inner (ι := ι) v (c • w) = c * inner (ι := ι) v w := by
  classical
  simp [inner, Finset.mul_sum, mul_comm, mul_assoc]

lemma inner_eq_euclidean_inner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v w : EuclideanSpace ℂ ι) :
    inner (ι := ι) v w = Inner.inner ℂ v w := by
  classical
  simp [inner, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

lemma Complex.real_add_conj (z : ℂ) :
    (z + conj z).re = 2 * z.re := by
  simpa using congrArg Complex.re (Complex.add_conj z)

namespace Matrix

lemma mulVec_add {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : Matrix κ ι ℂ) (v w : ι → ℂ) :
    A.mulVec (v + w) = A.mulVec v + A.mulVec w := by
  classical
  funext i
  simp [Matrix.mulVec]

end Matrix

/-- Positive-semidefinite matrix predicate specialized to finite matrices. -/
def PosSemidef {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) : Prop :=
  ∀ v : ι → ℂ, 0 ≤ (inner v (A.mulVec v)).re

/-- Standard computational basis ket. -/
def basisKet {n : ℕ} (i : Fin n) : Ket n :=
  fun j => if j = i then (1 : ℂ) else 0

@[simp] lemma basisKet_apply {n : ℕ} (i j : Fin n) :
    basisKet (n:=n) i j = (if j = i then (1 : ℂ) else 0) := rfl

@[simp] lemma Matrix.mulVec_basisKet {n : ℕ} (A : Mat n) (i j : Fin n) :
    (A.mulVec (basisKet (n:=n) j)) i = A i j := by
  classical
  simp [Matrix.mulVec, basisKet, dotProduct]

@[simp] lemma inner_basis_mulVec {n : ℕ} (A : Mat n) (i j : Fin n) :
    inner (basisKet (n:=n) i) (A.mulVec (basisKet (n:=n) j)) = A i j := by
  classical
  simp [inner, basisKet, Matrix.mulVec_basisKet]

/-- Density operators are Hermitian, unit-trace, positive-semidefinite matrices. -/
structure Density (n : ℕ) where
  mat : Mat n
  hermitian : mat.IsHermitian
  traceOne : Matrix.trace mat = (1 : ℂ)
  posSemidef : PosSemidef mat

namespace Density

variable {n : ℕ}

@[simp] def trace (ρ : Density n) : ℂ := Matrix.trace ρ.mat

@[simp] lemma trace_eq_one (ρ : Density n) : ρ.trace = 1 := by
  simpa [Density.trace] using ρ.traceOne

@[simp] lemma realTrace_eq_one (ρ : Density n) : (ρ.trace).re = 1 := by
  simpa [Density.trace] using congrArg Complex.re ρ.traceOne

@[simp] lemma mat_isHermitian (ρ : Density n) : ρ.mat.IsHermitian := ρ.hermitian

lemma dim_pos (ρ : Density n) : 0 < n := by
  classical
  by_contra hnonpos
  have hn : n = 0 := Nat.le_zero.mp (not_lt.mp hnonpos)
  have htrace_zero : Matrix.trace ρ.mat = (0 : ℂ) := by
    subst hn
    simp [Matrix.trace]
  have htrace_one : Matrix.trace ρ.mat = (1 : ℂ) := ρ.traceOne
  have : (0 : ℂ) = (1 : ℂ) := htrace_zero.symm.trans htrace_one
  exact zero_ne_one this

lemma isHermitian_trace_isReal {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) : (Matrix.trace A).im = 0 := by
  classical
  have htrace :
      Matrix.trace A = Matrix.trace A.conjTranspose := by
    simpa using (congrArg Matrix.trace hA).symm
  have hconj :
      Matrix.trace A.conjTranspose = star (Matrix.trace A) :=
    Matrix.trace_conjTranspose A
  have hstar : star (Matrix.trace A) = Matrix.trace A := by
    simpa [eq_comm] using htrace.trans hconj
  have hconj' : conj (Matrix.trace A) = Matrix.trace A := by
    simpa [Complex.star_def] using hstar
  exact (Complex.conj_eq_iff_im).1 hconj'

lemma trace_smul (c : ℂ) (A : Mat n) :
    Matrix.trace (c • A) = c * Matrix.trace A := by
  classical
  unfold Matrix.trace
  simp [Finset.mul_sum, Matrix.smul_apply]

lemma Matrix.IsHermitian.smul_real {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) {r : ℝ} :
    (((r : ℂ) • A).IsHermitian) := by
  classical
  -- `conjTranspose` commutes with scalar multiplication, and `star (r : ℂ) = r` for real scalars.
  unfold Matrix.IsHermitian at hA ⊢
  simp [Matrix.conjTranspose_smul, hA]

lemma Matrix.IsHermitian.entry_conj {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (i j : ι) :
    A j i = conj (A i j) := by
  classical
  have := congrArg (fun M : Matrix ι ι ℂ => M j i) hA
  simpa [Matrix.conjTranspose_apply] using this.symm

lemma Matrix.IsHermitian.diag_im_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (i : ι) :
    (A i i).im = 0 := by
  classical
  have := congrArg (fun M : Matrix ι ι ℂ => M i i) hA
  have hdiag : conj (A i i) = A i i := by
    simpa [Matrix.conjTranspose_apply] using this
  exact (Complex.conj_eq_iff_im).1 hdiag

lemma pos (ρ : Density n) : PosSemidef ρ.mat := ρ.posSemidef

section Diagonal

variable {n : ℕ}

lemma diagonal_posSemidef (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) :
    PosSemidef (Matrix.diagonal fun i => (d i : ℂ)) := by
  classical
  intro v
  have hmul :
      (Matrix.diagonal fun i => (d i : ℂ)).mulVec v =
        fun i => (d i : ℂ) * v i := by
    funext i
    simpa using
      (Matrix.mulVec_diagonal (fun i => (d i : ℂ)) v i)
  have hinner :
      inner v
          ((Matrix.diagonal fun i => (d i : ℂ)).mulVec v) =
        ∑ i, (d i : ℂ) * (conj (v i) * v i) := by
    simp [inner, hmul, mul_comm, mul_left_comm, mul_assoc]
  have hterm :
      ∀ i, ((d i : ℂ) * (conj (v i) * v i)).re =
          d i * Complex.normSq (v i) := by
    intro i
    have hconj :
        conj (v i) * v i = (Complex.normSq (v i) : ℂ) := by
      simpa [mul_comm] using
        (Complex.normSq_eq_conj_mul_self (z := v i)).symm
    calc
      ((d i : ℂ) * (conj (v i) * v i)).re
          = ((d i : ℂ) * (Complex.normSq (v i) : ℂ)).re := by
              simp [hconj]
      _ = d i * Complex.normSq (v i) := by
              simp
  have hreal :
      (inner v
          ((Matrix.diagonal fun i => (d i : ℂ)).mulVec v)).re =
        ∑ i, d i * Complex.normSq (v i) := by
    have hReEq :
        (inner v
            ((Matrix.diagonal fun i => (d i : ℂ)).mulVec v)).re =
          (∑ i, (d i : ℂ) * (conj (v i) * v i)).re := by
      simp [hinner]
    have hSumRe :
        (∑ i, (d i : ℂ) * (conj (v i) * v i)).re =
          ∑ i, d i * Complex.normSq (v i) := by
      simp [hterm]
    exact hReEq.trans hSumRe
  have hnonneg :
      0 ≤ ∑ i, d i * Complex.normSq (v i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hd i) (Complex.normSq_nonneg _)
  have hinnerNonneg :
      0 ≤
        (inner v
            ((Matrix.diagonal fun i => (d i : ℂ)).mulVec v)).re := by
    simpa [hreal] using hnonneg
  simpa [PosSemidef] using hinnerNonneg

/-- Construct a density matrix whose entries are given by a nonnegative real vector on the
diagonal. -/
def diagDensity (d : Fin n → ℝ) (hd_nonneg : ∀ i, 0 ≤ d i)
    (hd_sum : ∑ i, d i = 1) : Density n := by
  classical
  refine
    { mat := Matrix.diagonal fun i => (d i : ℂ)
      hermitian := ?_
      traceOne := ?_
      posSemidef := diagonal_posSemidef d hd_nonneg }
  ·
    have hsa :
        IsSelfAdjoint fun i : Fin n => (d i : ℂ) := by
      ext i; simp
    simpa using Matrix.isHermitian_diagonal_of_self_adjoint _ hsa
  ·
    have hsum :
        (∑ i, (d i : ℂ)) = (1 : ℂ) := by
      simpa [Complex.ofReal_sum, Complex.ofReal_one] using congrArg Complex.ofReal hd_sum
    simpa [Matrix.trace_diagonal] using hsum

end Diagonal

@[ext] lemma ext {ρ σ : Density n} (hmat : ρ.mat = σ.mat) : ρ = σ := by
  cases ρ
  cases σ
  cases hmat
  simp

end Density

namespace PosSemidef

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped BigOperators

lemma zero : PosSemidef (0 : Matrix ι ι ℂ) := by
  intro v
  simp [inner, Matrix.zero_mulVec]

lemma add {A B : Matrix ι ι ℂ} (hA : PosSemidef A) (hB : PosSemidef B) :
    PosSemidef (A + B) := by
  intro v
  have h := add_nonneg (hA v) (hB v)
  simpa [PosSemidef, inner, Matrix.add_mulVec, Finset.sum_add_distrib, mul_add, add_mul, map_add]
    using h

lemma sum {α : Type*} [DecidableEq α] (s : Finset α) (f : α → Matrix ι ι ℂ)
    (h : ∀ i ∈ s, PosSemidef (f i)) :
    PosSemidef (∑ i ∈ s, f i) := by
  classical
  refine
      Finset.induction_on (s := s)
        (motive := fun t => (∀ i ∈ t, PosSemidef (f i)) → PosSemidef (∑ i ∈ t, f i))
        ?base ?step h
  · intro _; simpa using (zero : PosSemidef (0 : Matrix ι ι ℂ))
  · intro a t ha hrec hAll
    have hfa : PosSemidef (f a) := hAll _ (by simp)
    have hrest : ∀ i ∈ t, PosSemidef (f i) := by
      intro i hi; exact hAll i (by simp [hi])
    have hsum : PosSemidef (∑ i ∈ t, f i) := hrec hrest
    simpa [Finset.sum_insert, ha] using add hfa hsum

lemma smul_real {A : Matrix ι ι ℂ} (hA : PosSemidef A) {c : ℝ}
    (hc : 0 ≤ c) : PosSemidef ((c : ℂ) • A) := by
  intro v
  have hv := hA v
  have hmul :
      ((c : ℂ) • A).mulVec v = (c : ℂ) • (A.mulVec v) := by
    simpa using (Matrix.smul_mulVec (b := (c : ℂ)) (M := A) (v := v))
  have hinner :
      inner v (((c : ℂ) • A).mulVec v) =
        (c : ℂ) * inner v (A.mulVec v) := by
    -- Rewrite the left side using `hmul`, then pull the scalar out of the inner product.
    rw [hmul]
    simpa using (inner_smul_right (c := (c : ℂ)) (v := v) (w := A.mulVec v))
  have hreal :
      ((c : ℂ) * inner v (A.mulVec v)).re =
        c * (inner v (A.mulVec v)).re := by
    simp [Complex.mul_re, Complex.ofReal_im]
  have hnonneg :
      0 ≤ c * (inner v (A.mulVec v)).re :=
    mul_nonneg hc hv
  -- Rewrite the goal into `0 ≤ c * (inner v (A.mulVec v)).re` using the previous identities.
  have : 0 ≤ (inner v (((c : ℂ) • A).mulVec v)).re := by
    -- Start from the right-hand side inequality and rewrite backwards.
    -- `hinner` gives `inner v ((c • A).mulVec v) = c * inner v (A.mulVec v)`.
    -- `hreal` turns the real part of the right-hand side into a real scalar multiple.
    -- Putting them together yields the desired inequality.
    -- We write the goal in the `c * (inner v (A.mulVec v)).re` form, then close with `hnonneg`.
    -- (Avoid `simp` loops by rewriting explicitly.)
    -- First change the goal to the scalar-multiple form.
    -- `hmul` and `hinner` already relate the two inner products.
    -- Use `hinner` to rewrite the real part.
    -- Then use `hreal` to move `Re` across scalar multiplication.
    -- Finally apply `hnonneg`.
    -- 
    -- Goal: 0 ≤ (inner v (((c : ℂ) • A).mulVec v)).re
    -- Rewrite using `hinner`:
    have : (inner v (((c : ℂ) • A).mulVec v)).re = c * (inner v (A.mulVec v)).re := by
      -- `hinner` gives the complex equality; take real parts and rewrite.
      have := congrArg Complex.re hinner
      -- Now rewrite the right-hand side using `hreal`.
      simpa [hreal] using this
    -- Now finish by rewriting and applying `hnonneg`.
    rw [this]
    exact hnonneg
  exact this

lemma diagonal_entry_nonneg {A : Matrix ι ι ℂ} (hA : PosSemidef A) (i : ι) :
    0 ≤ (A i i).re := by
  classical
  let e : ι → ℂ := Pi.single i 1
  have hmul : A.mulVec e = A.col i := by
    simp [e]
  have hinner : inner e (A.mulVec e) = A i i := by
    have hsum : (∑ x, conj (e x) * A x i) = A i i := by
      -- The only nonzero component of `e` is at `i`.
      refine (Fintype.sum_eq_single i ?_).trans ?_
      · intro x hx
        simp [e, Pi.single_eq_of_ne hx]
      · simp [e]
    simp [inner, e, hmul, Matrix.col_apply, hsum]
  have := hA e
  -- Keep this proof kernel-safe: rewrite the `PosSemidef` inequality using `hinner`.
  simpa [PosSemidef, hinner] using this

lemma trace_real_nonneg {A : Matrix ι ι ℂ} (hA : PosSemidef A) :
    0 ≤ (Matrix.trace A).re := by
  classical
  have htrace :
      (Matrix.trace A).re = ∑ i, (A i i).re := by
    simp [Matrix.trace]
  have hsum_nonneg :
      0 ≤ ∑ i, (A i i).re :=
    Finset.sum_nonneg fun i _ => diagonal_entry_nonneg (ι := ι) (A := A) hA i
  simpa [htrace] using hsum_nonneg

section Conjugation

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

private lemma inner_mulVec_left (B : Matrix m n ℂ) (v : m → ℂ) (w : n → ℂ) :
    inner v (B *ᵥ w) = inner (Bᴴ *ᵥ v) w := by
  classical
  -- Re-express `inner` using `dotProduct` with pointwise `star`, then use the standard identities:
  -- `dotProduct_mulVec` and `star_mulVec`.
  calc
    inner v (B *ᵥ w)
        = (star v) ⬝ᵥ (B *ᵥ w) := by
            simp [inner, dotProduct]
    _ = ((star v) ᵥ* B) ⬝ᵥ w := by
          simpa using (Matrix.dotProduct_mulVec (v := star v) (A := B) (w := w))
    _ = (star (Bᴴ *ᵥ v)) ⬝ᵥ w := by
          -- `star (Bᴴ *ᵥ v) = (star v) ᵥ* (Bᴴ)ᴴ = (star v) ᵥ* B`.
          have h := (Matrix.star_mulVec (M := Bᴴ) (v := v))
          -- Rewrite `(Bᴴ)ᴴ` to `B`.
          simpa [Matrix.conjTranspose_conjTranspose] using congrArg (fun x => x ⬝ᵥ w) h.symm
    _ = inner (Bᴴ *ᵥ v) w := by
          simp [inner, dotProduct]

lemma mul_mul_conjTranspose_same {A : Matrix n n ℂ} (hA : PosSemidef A) (B : Matrix m n ℂ) :
    PosSemidef (B * A * Bᴴ) := by
  classical
  intro v
  -- Let `u := Bᴴ *ᵥ v`. Then `⟪v, (B*A*Bᴴ) v⟫ = ⟪u, A u⟫`.
  let u : n → ℂ := Bᴴ *ᵥ v
  have hinner :
      inner v ((B * A * Bᴴ : Matrix m m ℂ) *ᵥ v) = inner u (A *ᵥ u) := by
    -- Expand the `mulVec` through products, then use the adjoint identity to move `B`.
    calc
      inner v ((B * A * Bᴴ : Matrix m m ℂ) *ᵥ v)
          = inner v (B *ᵥ (A *ᵥ u)) := by
              simp [u, Matrix.mul_assoc, Matrix.mulVec_mulVec]
      _ = inner (Bᴴ *ᵥ v) (A *ᵥ u) := inner_mulVec_left (B := B) (v := v) (w := A *ᵥ u)
      _ = inner u (A *ᵥ u) := by simp [u]
  have hu := hA u
  -- Rewrite the target inequality using `hinner` and close with `hu`.
  simpa [PosSemidef, hinner] using hu

end Conjugation

lemma reindex_equiv {κ : Type*} [Fintype κ] [DecidableEq κ] (e : ι ≃ κ)
    {A : Matrix ι ι ℂ} (hA : PosSemidef A) :
    PosSemidef (Matrix.reindex e e A) := by
  classical
  intro v
  let w : ι → ℂ := fun i => v (e i)
  have hmul :
      (Matrix.reindex e e A).mulVec v =
        fun i => (A.mulVec w) (e.symm i) := by
    funext i
    have hsum :
        ∑ j, A (e.symm i) (e.symm j) * v j =
          ∑ j, A (e.symm i) j * w j := by
      have :=
        Fintype.sum_equiv (e := e.symm)
          (f := fun j => A (e.symm i) (e.symm j) * v j)
          (g := fun j => A (e.symm i) j * w j)
          (by intro j; simp [w])
      simpa [w] using this
    simpa [Matrix.reindex_apply, Matrix.mulVec, hsum]
  have hdot :
      inner v
          ((Matrix.reindex e e A).mulVec v) =
        inner w (A.mulVec w) := by
    have hsum :
        ∑ i, conj (v i) * (A.mulVec w) (e.symm i) =
          ∑ i, conj (w i) * (A.mulVec w) i := by
      have :=
        Fintype.sum_equiv (e := e.symm)
          (f := fun i => conj (v i) * (A.mulVec w) (e.symm i))
          (g := fun j => conj (w j) * (A.mulVec w) j)
          (by intro i; simp [w])
      simpa [w] using this
    have hinner :
        inner v ((Matrix.reindex e e A).mulVec v) =
          inner v (fun i => (A.mulVec w) (e.symm i)) := by
      simpa using congrArg (inner v) hmul
    calc
      inner v ((Matrix.reindex e e A).mulVec v)
          = ∑ i, conj (v i) * (A.mulVec w) (e.symm i) := by
              simpa [inner] using hinner
      _ = ∑ i, conj (w i) * (A.mulVec w) i := hsum
      _ = inner w (A.mulVec w) := by
              simp [inner, w]
  have hw := hA w
  have hre :
      (inner w (A.mulVec w)).re =
        (inner v ((Matrix.reindex e e A).mulVec v)).re := by
    simpa using (congrArg Complex.re hdot).symm
  have : 0 ≤ (inner v ((Matrix.reindex e e A).mulVec v)).re := by
    simpa [hre] using hw
  simpa [PosSemidef] using this

lemma conj_mul {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {A : Matrix ι ι ℂ} (hA : PosSemidef A) (V : Matrix κ ι ℂ) :
    PosSemidef (V * A * Vᴴ) := by
  classical
  intro v
  have hrewrite :
      (V * A * Vᴴ).mulVec v = V.mulVec (A.mulVec (Vᴴ.mulVec v)) := by
    simp [Matrix.mul_assoc, Matrix.mulVec_mulVec]
  have hdot :
      inner v ((V * A * Vᴴ).mulVec v) =
        inner (Vᴴ.mulVec v) (A.mulVec (Vᴴ.mulVec v)) := by
    have dot_transfer :
        ∀ u : ι → ℂ,
          inner v (V.mulVec u) = inner (Vᴴ.mulVec v) u := by
      intro u
      classical
      have hleft :
          inner v (V.mulVec u) =
            ∑ j, (∑ i, conj (v i) * V i j) * u j := by
        have hdouble :
            inner v (V.mulVec u) =
              ∑ i, ∑ j, conj (v i) * (V i j * u j) := by
          simp [inner, Matrix.mulVec, dotProduct, Finset.mul_sum]
        have hswap :
            ∑ i, ∑ j, conj (v i) * (V i j * u j) =
              ∑ j, ∑ i, conj (v i) * (V i j * u j) := by
          simpa using
            Finset.sum_comm
              (s := (Finset.univ : Finset κ))
              (t := (Finset.univ : Finset ι))
              (f := fun i j => conj (v i) * (V i j * u j))
        have hcollect :
            ∑ j, ∑ i, conj (v i) * (V i j * u j) =
              ∑ j, (∑ i, conj (v i) * V i j) * u j := by
          refine Finset.sum_congr rfl ?_
          intro j _
          simp [Finset.sum_mul, mul_left_comm, mul_assoc]
        exact hdouble.trans <| hswap.trans hcollect
      have hstar :
          ∀ j, conj ((Vᴴ.mulVec v) j) = ∑ i, conj (v i) * V i j := by
        intro j
        simp [Matrix.mulVec, Matrix.conjTranspose, dotProduct, mul_comm]
      have hright :
          inner (Vᴴ.mulVec v) u =
            ∑ j, (∑ i, conj (v i) * V i j) * u j := by
        simp [inner, hstar]
      exact hleft.trans hright.symm
    have := dot_transfer (A.mulVec (Vᴴ.mulVec v))
    simpa [hrewrite] using this
  have hw := hA (Vᴴ.mulVec v)
  have hre :
      (inner v ((V * A * Vᴴ).mulVec v)).re =
        (inner (Vᴴ.mulVec v) (A.mulVec (Vᴴ.mulVec v))).re := by
    simpa using congrArg Complex.re hdot
  have hpos : 0 ≤ (inner v ((V * A * Vᴴ).mulVec v)).re := by
    simpa [hre] using hw
  simpa [PosSemidef] using hpos

lemma submatrix {κ : Type*} [Fintype κ] [DecidableEq κ] (f : κ → ι)
    {A : Matrix ι ι ℂ} (hA : PosSemidef A) :
    PosSemidef (A.submatrix f f) := by
  classical
  let V : Matrix κ ι ℂ := fun i j => if j = f i then 1 else 0
  have hrow :
      ∀ i p, (V * A) i p = A (f i) p := by
    intro i p
    classical
    simp [Matrix.mul_apply, V, Finset.mem_univ]
  have hentry :
      ∀ i j, (V * A * Vᴴ) i j = A (f i) (f j) := by
    intro i j
    have hsum :
        ∑ p : ι, (V * A) i p * conj (V j p) = A (f i) (f j) := by
      classical
      simp [V, hrow, Finset.mem_univ]
    have hmul :
        (V * A * Vᴴ) i j = A (f i) (f j) := by
      simpa [Matrix.mul_assoc, Matrix.mul_apply, Matrix.conjTranspose, hrow] using hsum
    exact hmul
  have hSub :
      V * A * Vᴴ = A.submatrix f f := by
    ext i j
    simpa [Matrix.submatrix] using hentry i j
  have := PosSemidef.conj_mul hA V
  simpa [hSub] using this

end PosSemidef

lemma hermitian_posSemidef_trace_zero_eq_zero {n : ℕ}
    {A : Mat n} (hHerm : A.IsHermitian) (hPos : PosSemidef A)
    (htrace : Matrix.trace A = 0) : A = 0 := by
  classical
  have hdiag_nonneg :
      ∀ i : Fin n, 0 ≤ (A i i).re := fun i =>
        PosSemidef.diagonal_entry_nonneg (ι := Fin n) (A := A) hPos i
  have htrace_re :
      ∑ i : Fin n, (A i i).re = 0 := by
    have := congrArg Complex.re htrace
    simpa [Matrix.trace, map_sum] using this
  have hdiag_re_zero :
      ∀ i : Fin n, (A i i).re = 0 := by
    have hzero :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (s := (Finset.univ : Finset (Fin n)))
        (f := fun i : Fin n => (A i i).re)
        (fun i _ => hdiag_nonneg i)).1 htrace_re
    intro i
    simpa using hzero i (by simp)
  have hdiag_im_zero :
      ∀ i : Fin n, (A i i).im = 0 := by
    intro i
    have h := Matrix.IsHermitian.apply (A := A) hHerm i i
    have hconj : conj (A i i) = A i i := by
      simpa [star_def] using h
    exact (Complex.conj_eq_iff_im).1 hconj
  have hdiag_zero :
      ∀ i : Fin n, A i i = 0 := by
    intro i
    have hre := hdiag_re_zero i
    have him := hdiag_im_zero i
    apply Complex.ext <;> simp [hre, him]
  have hcombo :
      ∀ i j : Fin n, ∀ α : ℂ,
        (inner
            (basisKet (n:=n) i + α • basisKet (n:=n) j)
            (A.mulVec
              (basisKet (n:=n) i + α • basisKet (n:=n) j))).re =
          2 * (α * A i j).re := by
    intro i j α
    have hEntry : A j i = conj (A i j) := by
      have h := Matrix.IsHermitian.apply (A := A) hHerm j i
      simpa [star_def] using h.symm
    have hcalc :
        inner
            (basisKet (n:=n) i + α • basisKet (n:=n) j)
            (A.mulVec
              (basisKet (n:=n) i + α • basisKet (n:=n) j)) =
          α * A i j + conj α * conj (A i j) := by
      simp [Matrix.mulVec_add, Matrix.mulVec_smul, inner_add_left, inner_add_right,
        inner_smul_left, inner_smul_right, inner_basis_mulVec, hdiag_zero i, hdiag_zero j, hEntry,
        add_comm]
    have hconj :
        conj α * conj (A i j) = conj (α * A i j) := by
      simp
    calc
      (inner
            (basisKet (n:=n) i + α • basisKet (n:=n) j)
            (A.mulVec
              (basisKet (n:=n) i + α • basisKet (n:=n) j))).re
          = (α * A i j + conj α * conj (A i j)).re := by
            simp [hcalc]
      _ = (α * A i j + conj (α * A i j)).re := by
            rw [hconj]
      _ = 2 * (α * A i j).re := by
            simpa using Complex.real_add_conj (α * A i j)
  have hentry_zero :
      ∀ i j : Fin n, A i j = 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      exact hdiag_zero i
    · have hRe_ge :
          0 ≤ 2 * (A i j).re :=
        by
          have h0 :=
            hPos (basisKet (n:=n) i + (1 : ℂ) • basisKet (n:=n) j)
          have h0' : 0 ≤ 2 * ((1 : ℂ) * A i j).re := by
            -- Rewrite the goal into the `PosSemidef` inequality using `hcombo`.
            rw [← hcombo i j (1 : ℂ)]
            exact h0
          simpa using h0'
      have hRe_le :
          0 ≤ -2 * (A i j).re :=
        by
          have h0 :=
            hPos (basisKet (n:=n) i + (-1 : ℂ) • basisKet (n:=n) j)
          have h0' : 0 ≤ 2 * ((-1 : ℂ) * A i j).re := by
            -- Rewrite the goal into the `PosSemidef` inequality using `hcombo`.
            rw [← hcombo i j (-1 : ℂ)]
            exact h0
          -- `((-1) * z).re = -z.re`.
          simpa [Complex.mul_re] using h0'
      have hRe_zero :
          (A i j).re = 0 := by
        have hle : 2 * (A i j).re ≤ 0 :=
          (neg_nonneg).1 (by simpa [neg_mul, two_mul] using hRe_le)
        have hmulzero :
            2 * (A i j).re = 0 := le_antisymm hle hRe_ge
        exact
          (mul_eq_zero.mp hmulzero).resolve_left (by norm_num : (2 : ℝ) ≠ 0)
      have hIm_ge :
          0 ≤ -2 * (A i j).im :=
        by
          have := hPos (basisKet (n:=n) i + Complex.I • basisKet (n:=n) j)
          simpa [hcombo i j Complex.I] using this
      have hIm_le :
          0 ≤ 2 * (A i j).im :=
        by
          have h0 :=
            hPos (basisKet (n:=n) i + (-Complex.I) • basisKet (n:=n) j)
          have h0' : 0 ≤ 2 * ((-Complex.I) * A i j).re := by
            -- Rewrite the goal into the `PosSemidef` inequality using `hcombo`.
            rw [← hcombo i j (-Complex.I)]
            exact h0
          -- `((-I) * z).re = z.im`.
          simpa [Complex.mul_re] using h0'
      have hIm_zero :
          (A i j).im = 0 := by
        have hneg : -2 * (A i j).im = -(2 * (A i j).im) := by
          simp
        have hle : 2 * (A i j).im ≤ 0 :=
          (neg_nonneg).1 (by simpa [hneg] using hIm_ge)
        have hmulzero :
            2 * (A i j).im = 0 := le_antisymm hle hIm_le
        exact
          (mul_eq_zero.mp hmulzero).resolve_left (by norm_num : (2 : ℝ) ≠ 0)
      apply Complex.ext <;> simp [hRe_zero, hIm_zero]
  ext i j
  exact hentry_zero i j

lemma Matrix.IsHermitian.eigenvalues_nonneg_of_posSemidef {n : ℕ}
    {A : Mat n} (hHerm : A.IsHermitian) (hPos : PosSemidef A) :
    ∀ j : Fin n, 0 ≤ hHerm.eigenvalues j := by
  classical
  intro j
  have hmul :
      A.mulVec (hHerm.eigenvectorBasis j) =
        (hHerm.eigenvalues j : ℂ) • (hHerm.eigenvectorBasis j) := by
    simpa using
      (Matrix.IsHermitian.mulVec_eigenvectorBasis
        (hA := hHerm) (j := j))
  have hvnorm :
      inner (hHerm.eigenvectorBasis j) (hHerm.eigenvectorBasis j) = 1 := by
    have hE :
        inner (hHerm.eigenvectorBasis j) (hHerm.eigenvectorBasis j) =
          Inner.inner ℂ (hHerm.eigenvectorBasis j) (hHerm.eigenvectorBasis j) :=
      inner_eq_euclidean_inner (ι := Fin n)
        (v := hHerm.eigenvectorBasis j) (w := hHerm.eigenvectorBasis j)
    have hO :
        Inner.inner ℂ (hHerm.eigenvectorBasis j) (hHerm.eigenvectorBasis j) = (1 : ℂ) := by
      simp
    exact hE.trans hO
  have hvnorm_real :
      (inner (hHerm.eigenvectorBasis j) (hHerm.eigenvectorBasis j)).re = 1 := by
    simpa using congrArg Complex.re hvnorm
  have hvcalc :
      (inner (hHerm.eigenvectorBasis j)
          ((hHerm.eigenvalues j : ℂ) • hHerm.eigenvectorBasis j)).re =
        (hHerm.eigenvalues j) * 1 := by
    have :
        inner (hHerm.eigenvectorBasis j)
            ((hHerm.eigenvalues j : ℂ) • hHerm.eigenvectorBasis j) =
          (hHerm.eigenvalues j : ℂ) *
            inner (hHerm.eigenvectorBasis j)
              (hHerm.eigenvectorBasis j) := by
      simpa using
        (inner_smul_right_euclidean (ι := Fin n) (c := (hHerm.eigenvalues j : ℂ))
          (v := hHerm.eigenvectorBasis j) (w := hHerm.eigenvectorBasis j))
    have hre :
        (inner (hHerm.eigenvectorBasis j)
              ((hHerm.eigenvalues j : ℂ) • hHerm.eigenvectorBasis j)).re =
          ((hHerm.eigenvalues j : ℂ) *
              inner (hHerm.eigenvectorBasis j)
                (hHerm.eigenvectorBasis j)).re :=
      congrArg Complex.re this
    have hReal :
        ((hHerm.eigenvalues j : ℂ) *
              inner (hHerm.eigenvectorBasis j)
                (hHerm.eigenvectorBasis j)).re =
          (hHerm.eigenvalues j) *
            (inner (hHerm.eigenvectorBasis j)
                (hHerm.eigenvectorBasis j)).re := by
      simp [Complex.mul_re]
    calc
      (inner (hHerm.eigenvectorBasis j)
          ((hHerm.eigenvalues j : ℂ) • hHerm.eigenvectorBasis j)).re
          = (hHerm.eigenvalues j) *
              (inner (hHerm.eigenvectorBasis j)
                (hHerm.eigenvectorBasis j)).re := hre.trans hReal
      _ = (hHerm.eigenvalues j) * 1 := by simp [hvnorm_real]
  have hge :
      0 ≤ (hHerm.eigenvalues j) := by
    have :=
      hPos (hHerm.eigenvectorBasis j)
    have hrewrite :
        (inner (hHerm.eigenvectorBasis j)
            (A.mulVec (hHerm.eigenvectorBasis j))).re =
          (inner (hHerm.eigenvectorBasis j)
              ((hHerm.eigenvalues j : ℂ) •
                hHerm.eigenvectorBasis j)).re := by
      simp [hmul]
    have hv' :
        0 ≤ (inner (hHerm.eigenvectorBasis j)
              ((hHerm.eigenvalues j : ℂ) • hHerm.eigenvectorBasis j)).re := by
      simpa [hrewrite] using this
    have hmain : 0 ≤ (hHerm.eigenvalues j) * 1 := by
      -- Avoid `simp` orientation issues; rewrite the goal explicitly.
      rw [← hvcalc]
      exact hv'
    simpa using hmain
  exact hge

end Quantum
end HeytingLean

end
