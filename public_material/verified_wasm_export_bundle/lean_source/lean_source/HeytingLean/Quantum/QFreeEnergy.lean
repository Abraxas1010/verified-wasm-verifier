import HeytingLean.Quantum.QState
import HeytingLean.Quantum.ActiveInference.OperatorPinching
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.HermitianFunctionalCalculus
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Topology.Instances.Matrix

/-
Von Neumann entropy / relative entropy scaffolding for the qRelEnt plan. The
entrywise logarithm `matrixLog` remains available for
backwards compatibility and diagnostics, while `matrixLogDensity`
uses mathlib's Hermitian functional calculus and powers `vnEntropy`
and `qRelEnt`.
-/

namespace Matrix

open scoped Matrix BigOperators
open scoped Polynomial
open HeytingLean.Quantum

variable {o m : Type*} [Fintype o] [DecidableEq o] [Fintype m] [DecidableEq m]

@[simp] lemma blockDiagonal_algebraMap_complex (r : ℂ) :
    blockDiagonal (fun _ : o => algebraMap ℂ (Matrix m m ℂ) r) =
      algebraMap ℂ (Matrix (m × o) (m × o) ℂ) r := by
  classical
  ext p q
  rcases p with ⟨p₁, p₂⟩
  rcases q with ⟨q₁, q₂⟩
  by_cases h₂ : p₂ = q₂
  · subst h₂
    by_cases h₁ : p₁ = q₁
    · subst h₁
      simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal, blockDiagonal]
    ·
      have hpq : (p₁, p₂) ≠ (q₁, p₂) := by
        intro hpq
        exact h₁ (congrArg Prod.fst hpq)
      simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal, blockDiagonal, h₁, hpq]
  ·
    have hpq : (p₁, p₂) ≠ (q₁, q₂) := by
      intro hpq
      exact h₂ (congrArg Prod.snd hpq)
    simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal, blockDiagonal, h₂, hpq]

@[simp] lemma blockDiagonal_algebraMap_real (x : ℝ) :
    blockDiagonal (fun _ : o => algebraMap ℝ (Matrix m m ℂ) x) =
      algebraMap ℝ (Matrix (m × o) (m × o) ℂ) x := by
  classical
  simpa [Matrix.algebraMap_eq_diagonal, Matrix.diagonal] using
    (blockDiagonal_diagonal (o := o) (m := m)
      (d := fun _ : o => fun _ : m => (algebraMap ℝ ℂ x)))

lemma spectrum_blockDiagonal_subset_of_block (A : o → Matrix m m ℂ) (k : o) :
    spectrum ℝ (A k) ⊆ spectrum ℝ (blockDiagonal A) := by
  classical
  intro x hx
  have hxNonunit : ¬ IsUnit (algebraMap ℝ (Matrix m m ℂ) x - A k) :=
    (spectrum.mem_iff (r := x) (a := A k)).1 hx
  have hxDetNonunit : ¬ IsUnit ((algebraMap ℝ (Matrix m m ℂ) x - A k).det) := by
    intro hDet
    have hMat : IsUnit (algebraMap ℝ (Matrix m m ℂ) x - A k) :=
      (Matrix.isUnit_iff_isUnit_det _).2 hDet
    exact hxNonunit hMat
  let B : o → Matrix m m ℂ := fun l => algebraMap ℝ (Matrix m m ℂ) x - A l
  have hxBigNonunit :
      ¬ IsUnit (algebraMap ℝ (Matrix (m × o) (m × o) ℂ) x - blockDiagonal A) := by
    have hdiff :
        algebraMap ℝ (Matrix (m × o) (m × o) ℂ) x - blockDiagonal A =
          blockDiagonal B := by
      calc
        algebraMap ℝ (Matrix (m × o) (m × o) ℂ) x - blockDiagonal A =
            blockDiagonal (fun _ : o => algebraMap ℝ (Matrix m m ℂ) x) - blockDiagonal A := by
              simp
        _ = blockDiagonal B := by
              dsimp [B]
              exact (blockDiagonal_sub
                (M := fun _ : o => algebraMap ℝ (Matrix m m ℂ) x) (N := A)).symm
    intro hUnitBig
    have hDetBig : IsUnit ((blockDiagonal B).det) := by
      have :
          IsUnit
            ((algebraMap ℝ (Matrix (m × o) (m × o) ℂ) x - blockDiagonal A).det) :=
        (Matrix.isUnit_iff_isUnit_det _).1 hUnitBig
      simpa [hdiff] using this
    have hDetProd : IsUnit (∏ l : o, (B l).det) := by
      simpa [Matrix.det_blockDiagonal] using hDetBig
    have hAll : ∀ l : o, IsUnit ((B l).det) := (IsUnit.prod_univ_iff).1 hDetProd
    exact hxDetNonunit (by simpa [B] using hAll k)
  exact (spectrum.mem_iff (r := x) (a := blockDiagonal A)).2 hxBigNonunit

/-- `Matrix.blockDiagonal` upgraded to a complex `AlgHom`. -/
noncomputable def blockDiagonalAlgHomComplex :
    (o → Matrix m m ℂ) →ₐ[ℂ] Matrix (m × o) (m × o) ℂ :=
  { blockDiagonalRingHom m o ℂ with
    commutes' := fun r => blockDiagonal_algebraMap_complex (o:=o) (m:=m) r }

/-- `Matrix.blockDiagonal` upgraded to a complex `StarAlgHom`. -/
noncomputable def blockDiagonalStarAlgHomComplex :
    (o → Matrix m m ℂ) →⋆ₐ[ℂ] Matrix (m × o) (m × o) ℂ :=
  { blockDiagonalAlgHomComplex (o:=o) (m:=m) with
    map_star' := by
      intro M
      -- Avoid `simp` here: `Matrix.blockDiagonal_conjTranspose` is a simp lemma and would
      -- simplify the goal/proof term away.
      change Matrix.blockDiagonal (fun i => (M i)ᴴ) = (Matrix.blockDiagonal M)ᴴ
      exact (Matrix.blockDiagonal_conjTranspose (M := M)).symm }

lemma blockDiagonalStarAlgHomComplex_continuous :
    Continuous (blockDiagonalStarAlgHomComplex (o:=o) (m:=m)) := by
  classical
  let L :=
    (blockDiagonalStarAlgHomComplex (o:=o) (m:=m) :
      (o → Matrix m m ℂ) →ₗ[ℂ] Matrix (m × o) (m × o) ℂ)
  exact L.continuous_of_finiteDimensional

omit [Fintype o] [Fintype m] [DecidableEq m] in
lemma blockDiagonal_isHermitian {A : o → Matrix m m ℂ}
    (hA : ∀ k, (A k).IsHermitian) :
    (blockDiagonal A).IsHermitian := by
  classical
  unfold Matrix.IsHermitian
  have hfun : (fun k => (A k)ᴴ) = A := by
    funext k
    simpa [Matrix.IsHermitian] using hA k
  calc
    (blockDiagonal A)ᴴ = blockDiagonal (fun k => (A k)ᴴ) :=
      Matrix.blockDiagonal_conjTranspose (M := A)
    _ = blockDiagonal A := by
      simp [hfun]

omit [Fintype o] [Fintype m] [DecidableEq m] in
lemma blockDiagonal_isHermitian_iff (A : o → Matrix m m ℂ) :
    (blockDiagonal A).IsHermitian ↔ ∀ k, (A k).IsHermitian := by
  classical
  constructor
  · intro h
    have hcongr :
        blockDiagonal (fun k => (A k)ᴴ) = blockDiagonal A := by
      simpa [Matrix.IsHermitian, Pi.star_def] using h
    have hfun :
        (fun k => (A k)ᴴ) = A :=
      (blockDiagonal_injective (o:=o) (m:=m) (n:=m) (α:=ℂ))
        (by simpa using hcongr)
    intro k
    have := congrArg (fun f => f k) hfun
    simpa [Matrix.IsHermitian] using this
  · intro h
    exact blockDiagonal_isHermitian (A := A) h

lemma blockDiagonal_cfc (A : o → Matrix m m ℂ)
    (hA : ∀ k, (A k).IsHermitian) (f : ℝ → ℝ) :
    (blockDiagonal_isHermitian (o:=o) (m:=m) hA).cfc (A := blockDiagonal A) f =
      blockDiagonal fun k => (hA k).cfc (A := A k) f := by
  classical
  -- Reduce to the unbundled `cfc` on matrices, then use polynomial interpolation
  -- (finite spectrum) + `cfc_polynomial`.
  have hresult :
      cfc f (blockDiagonal A) = blockDiagonal fun k => cfc f (A k) := by
    let hs : (spectrum ℝ (blockDiagonal A)).Finite := Matrix.finite_real_spectrum (A := blockDiagonal A)
    let s : Finset ℝ := hs.toFinset
    let q : ℝ[X] := (Lagrange.interpolate s (fun x : ℝ => x)) f

    have hEqOn_big : (spectrum ℝ (blockDiagonal A)).EqOn f q.eval := by
      intro x hx
      have hxmem : x ∈ s := by
        simpa [s, hs.mem_toFinset] using hx
      have hEval : q.eval x = f x := by
        simpa [q] using
          (Lagrange.eval_interpolate_at_node (r := f) (s := s) (v := fun x : ℝ => x) (i := x)
            (hvs := Function.injective_id.injOn) (hi := hxmem))
      exact hEval.symm

    have hEqOn_block (k : o) : (spectrum ℝ (A k)).EqOn f q.eval := by
      intro x hx
      exact hEqOn_big (spectrum_blockDiagonal_subset_of_block (o := o) (m := m) A k hx)

    have hcfc_big : cfc f (blockDiagonal A) = cfc q.eval (blockDiagonal A) :=
      cfc_congr (R := ℝ) (a := blockDiagonal A) hEqOn_big

    have hcfc_block (k : o) : cfc f (A k) = cfc q.eval (A k) :=
      cfc_congr (R := ℝ) (a := A k) (hEqOn_block k)

    have hpoly_aeval :
        (Polynomial.aeval (blockDiagonal A) : ℝ[X] →ₐ[ℝ] Matrix (m × o) (m × o) ℂ) q =
          blockDiagonal fun k =>
            (Polynomial.aeval (A k) : ℝ[X] →ₐ[ℝ] Matrix m m ℂ) q := by
      let φ : (o → Matrix m m ℂ) →ₐ[ℝ] Matrix (m × o) (m × o) ℂ :=
        (blockDiagonalAlgHomComplex (o := o) (m := m)).restrictScalars ℝ
      have hφ :
          (Polynomial.aeval (φ A) : ℝ[X] →ₐ[ℝ] Matrix (m × o) (m × o) ℂ) q =
            φ ((Polynomial.aeval A : ℝ[X] →ₐ[ℝ] (o → Matrix m m ℂ)) q) := by
        simpa using (Polynomial.aeval_algHom_apply φ A q)
      have hPi :
          (Polynomial.aeval A : ℝ[X] →ₐ[ℝ] (o → Matrix m m ℂ)) q =
            fun k => (Polynomial.aeval (A k) : ℝ[X] →ₐ[ℝ] Matrix m m ℂ) q := by
        funext k
        let ev : (o → Matrix m m ℂ) →ₐ[ℝ] Matrix m m ℂ :=
          Pi.evalAlgHom ℝ (fun _ : o => Matrix m m ℂ) k
        have :
            (Polynomial.aeval (ev A) : ℝ[X] →ₐ[ℝ] Matrix m m ℂ) q =
              ev ((Polynomial.aeval A : ℝ[X] →ₐ[ℝ] (o → Matrix m m ℂ)) q) := by
          simpa using (Polynomial.aeval_algHom_apply ev A q)
        simpa [ev] using this.symm
      simpa [φ, hPi] using hφ

    have hpoly_big :
        cfc q.eval (blockDiagonal A) =
          (Polynomial.aeval (blockDiagonal A) : ℝ[X] →ₐ[ℝ] Matrix (m × o) (m × o) ℂ) q := by
      simpa using
        (cfc_polynomial (R := ℝ) (q := q) (a := blockDiagonal A)
          (ha := blockDiagonal_isHermitian (o := o) (m := m) hA))

    have hpoly_block (k : o) :
        cfc q.eval (A k) =
          (Polynomial.aeval (A k) : ℝ[X] →ₐ[ℝ] Matrix m m ℂ) q := by
      simpa using (cfc_polynomial (R := ℝ) (q := q) (a := A k) (ha := hA k))

    calc
      cfc f (blockDiagonal A)
          = cfc q.eval (blockDiagonal A) := hcfc_big
      _ = (Polynomial.aeval (blockDiagonal A) : ℝ[X] →ₐ[ℝ] Matrix (m × o) (m × o) ℂ) q :=
          hpoly_big
      _ = blockDiagonal fun k =>
            (Polynomial.aeval (A k) : ℝ[X] →ₐ[ℝ] Matrix m m ℂ) q := hpoly_aeval
      _ = blockDiagonal fun k => cfc q.eval (A k) := by
            refine congrArg blockDiagonal ?_
            funext k
            simpa using (hpoly_block k).symm
      _ = blockDiagonal fun k => cfc f (A k) := by
            refine congrArg blockDiagonal ?_
            funext k
            simpa using (hcfc_block k).symm

  -- Turn the unbundled `cfc` statement into the `IsHermitian.cfc` statement.
  have hbig :
      (blockDiagonal_isHermitian (o := o) (m := m) hA).cfc (A := blockDiagonal A) f =
        cfc f (blockDiagonal A) := by
    simpa using
      (Matrix.IsHermitian.cfc_eq (A := blockDiagonal A)
        (blockDiagonal_isHermitian (o := o) (m := m) hA) f).symm
  have hblocks :
      (blockDiagonal fun k => cfc f (A k)) =
        blockDiagonal fun k => (hA k).cfc (A := A k) f := by
    refine congrArg blockDiagonal ?_
    funext k
    simpa using (Matrix.IsHermitian.cfc_eq (A := A k) (hA k) f)
  -- Assemble.
  simpa [hbig, hblocks] using hresult

section Reindex

variable {o o' : Type*} [Fintype o] [DecidableEq o] [Fintype o'] [DecidableEq o']

@[simp] lemma reindex_algebraMap_complex (e : o ≃ o') (r : ℂ) :
    Matrix.reindex e e (algebraMap ℂ (Matrix o o ℂ) r) =
      algebraMap ℂ (Matrix o' o' ℂ) r := by
  classical
  ext i j
  simp [Matrix.reindex_apply, Matrix.algebraMap_eq_diagonal, Matrix.diagonal]

/-- `Matrix.reindex` viewed as a complex `StarAlgHom`. -/
noncomputable def reindexStarAlgHomComplex (e : o ≃ o') :
    Matrix o o ℂ →⋆ₐ[ℂ] Matrix o' o' ℂ :=
  { (Matrix.reindexAlgEquiv ℂ ℂ e : Matrix o o ℂ ≃ₐ[ℂ] Matrix o' o' ℂ).toAlgHom with
    map_star' := by
      intro A
      ext i j
      simp [Matrix.reindex_apply, Matrix.submatrix] }

lemma reindexStarAlgHomComplex_continuous (e : o ≃ o') :
    Continuous (reindexStarAlgHomComplex (o:=o) (o':=o') e) := by
  classical
  let L :=
    (reindexStarAlgHomComplex (o:=o) (o':=o') e : Matrix o o ℂ →ₗ[ℂ] Matrix o' o' ℂ)
  exact L.continuous_of_finiteDimensional

omit [Fintype o] [DecidableEq o] [Fintype o'] [DecidableEq o'] in
lemma reindex_isHermitian {A : Matrix o o ℂ} (hA : A.IsHermitian) (e : o ≃ o') :
    (Matrix.reindex e e A).IsHermitian := by
  classical
  have := congrArg (Matrix.reindex e e) hA
  simpa [Matrix.IsHermitian, Matrix.conjTranspose_reindex] using this

lemma IsHermitian.cfc_congr {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} {h₁ h₂ : A.IsHermitian} (f : ℝ → ℝ) :
    h₁.cfc (A := A) f = h₂.cfc (A := A) f := by
  classical
  have h1 : cfc f A = h₁.cfc (A := A) f :=
    Matrix.IsHermitian.cfc_eq (A := A) h₁ f
  have h2 : cfc f A = h₂.cfc (A := A) f :=
    Matrix.IsHermitian.cfc_eq (A := A) h₂ f
  exact h1.symm.trans h2

lemma trace_reindex_symm {o o' : Type*} [Fintype o] [DecidableEq o]
    [Fintype o'] [DecidableEq o'] (e : o ≃ o') (A : Matrix o' o' ℂ) :
    Matrix.trace (Matrix.reindex e.symm e.symm A) = Matrix.trace A := by
  classical
  unfold Matrix.trace
  simpa [Matrix.reindex_apply, Matrix.submatrix] using
    (Fintype.sum_equiv e (f := fun i : o => A (e i) (e i))
      (g := fun j : o' => A j j) (fun i => rfl))

section BlockTrace

variable {m k : ℕ}

lemma trace_blockDiagonal_mul_ancilla
    (A : Fin k → Matrix (Fin m) (Fin m) ℂ)
    (B : Matrix (Fin m × Fin k) (Fin m × Fin k) ℂ) :
    Matrix.trace (blockDiagonal A * B) =
      ∑ l : Fin k,
        Matrix.trace
          (A l *
            ActiveInference.ancillaBlock (m:=m) (k:=k) B l) := by
  classical
  unfold Matrix.trace
  -- Split the trace sum over the product index `(i, l)`.
  rw [Fintype.sum_prod_type_right]
  -- Reduce to a pointwise statement on diagonal entries.
  refine Fintype.sum_congr (f := fun l : Fin k => ∑ i : Fin m, (blockDiagonal A * B) (i, l) (i, l))
    (g := fun l : Fin k =>
      ∑ i : Fin m, (A l * ActiveInference.ancillaBlock (m := m) (k := k) B l) i i) ?_
  intro l
  refine Fintype.sum_congr
    (f := fun i : Fin m => (blockDiagonal A * B) (i, l) (i, l))
    (g := fun i : Fin m => (A l * ActiveInference.ancillaBlock (m := m) (k := k) B l) i i) ?_
  intro i
  simp [Matrix.mul_apply, Matrix.blockDiagonal_apply, Fintype.sum_prod_type_right,
    ActiveInference.ancillaBlock, Matrix.submatrix]

end BlockTrace

end Reindex

end Matrix

namespace HeytingLean
namespace Quantum

open Matrix Complex
open scoped Matrix

noncomputable section

variable {n : ℕ}

/-- Entrywise complex logarithm (diagnostic only). -/
def matrixLog (A : Mat n) : Mat n :=
  Matrix.map A Complex.log

@[simp] lemma matrixLog_zero : matrixLog (0 : Mat n) = 0 := by
  classical
  ext i j
  simp [matrixLog]

/-- Spectral logarithm of a density matrix via the Hermitian functional calculus. -/
def matrixLogDensity (ρ : Density n) : Mat n :=
  (ρ.mat_isHermitian).cfc (A := ρ.mat) fun x => Real.log x

/-- `matrixLogDensity` respects equality of the underlying matrices. -/
lemma matrixLogDensity_congr {ρ σ : Density n} (h : ρ.mat = σ.mat) :
    matrixLogDensity ρ = matrixLogDensity σ := by
  have hρσ : ρ = σ := Density.ext h
  subst hρσ
  rfl

/-- Von Neumann entropy (base *e*). -/
def vnEntropy (ρ : Density n) : ℝ :=
  -((Matrix.trace (ρ.mat * matrixLogDensity ρ)).re)

/-- Quantum relative entropy using the spectral logarithm. -/
def qRelEnt (ρ σ : Density n) : ℝ :=
  (Matrix.trace (ρ.mat * (matrixLogDensity ρ - matrixLogDensity σ))).re

/-- `qRelEnt` is invariant under pointwise matrix equality. -/
lemma qRelEnt_congr {ρ ρ' σ σ' : Density n}
    (hρ : ρ.mat = ρ'.mat) (hσ : σ.mat = σ'.mat) :
    qRelEnt ρ σ = qRelEnt ρ' σ' := by
  have hρeq : ρ = ρ' := Density.ext hρ
  have hσeq : σ = σ' := Density.ext hσ
  subst hρeq
  subst hσeq
  rfl

@[simp] lemma qRelEnt_self (ρ : Density n) : qRelEnt ρ ρ = 0 := by
  classical
  simp [qRelEnt]

/-- Helmholtz free energy for inverse temperature `β` and Hamiltonian `H`. -/
def freeEnergy (β : ℝ) (H : Mat n) (ρ : Density n) : ℝ :=
  (Matrix.trace (ρ.mat * H)).re - (1 / β) * vnEntropy ρ

end

end Quantum
end HeytingLean

namespace Matrix

open scoped Matrix BigOperators
open HeytingLean.Quantum

variable {m k : ℕ}

lemma matrixLogDensity_reindex_blockDiagonal
    {ρ : Density (m * k)} {A : Fin k → Matrix (Fin m) (Fin m) ℂ}
    (hA : ∀ l, (A l).IsHermitian)
    (hmat :
      Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
        (finProdFinEquiv (m:=m) (n:=k)).symm ρ.mat =
        blockDiagonal A) :
    Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
        (finProdFinEquiv (m:=m) (n:=k)).symm (matrixLogDensity ρ) =
      blockDiagonal fun l =>
        (hA l).cfc (A := A l) fun x => Real.log x := by
  classical
  set e := (finProdFinEquiv (m:=m) (n:=k)).symm with he
  have hmat' : Matrix.reindex e e ρ.mat = blockDiagonal A := by
    simpa [he] using hmat
  have hf : ContinuousOn (fun x : ℝ => Real.log x) (spectrum ℝ ρ.mat) := by
    simpa using
      (Set.Finite.continuousOn (hs := (Matrix.finite_real_spectrum (A := ρ.mat)))
        (f := fun x : ℝ => Real.log x))
  have hmap :=
    (reindexStarAlgHomComplex (o:=Fin (m * k)) (o':=Fin m × Fin k) e).map_cfc
      (f := fun x : ℝ => Real.log x) (a := ρ.mat)
      (hf := hf)
      (hφ := reindexStarAlgHomComplex_continuous (o:=Fin (m * k)) (o':=Fin m × Fin k) e)
      (ha := ρ.mat_isHermitian)
      (hφa :=
        Matrix.reindex_isHermitian
          (A := ρ.mat) (o:=Fin (m * k)) (o':=Fin m × Fin k) ρ.mat_isHermitian e)
  have hreindex :
      Matrix.reindex e e (cfc (fun x : ℝ => Real.log x) ρ.mat) =
        cfc (fun x : ℝ => Real.log x) (Matrix.reindex e e ρ.mat) := by
    simpa [reindexStarAlgHomComplex, Matrix.reindexAlgEquiv_apply] using hmap
  have htarget :
      Matrix.reindex e e (matrixLogDensity ρ) =
        blockDiagonal fun l =>
          (hA l).cfc (A := A l) fun x => Real.log x := by
    calc
      Matrix.reindex e e (matrixLogDensity ρ)
          = Matrix.reindex e e (cfc (fun x : ℝ => Real.log x) ρ.mat) := by
              simp [matrixLogDensity, Matrix.IsHermitian.cfc_eq]
      _ = cfc (fun x : ℝ => Real.log x) (Matrix.reindex e e ρ.mat) := hreindex
      _ = cfc (fun x : ℝ => Real.log x) (blockDiagonal A) := by
            simp [hmat']
      _ = (blockDiagonal_isHermitian (o := Fin k) (m := Fin m) hA).cfc
            (A := blockDiagonal A) (fun x : ℝ => Real.log x) := by
            simpa using
              (Matrix.IsHermitian.cfc_eq
                (blockDiagonal_isHermitian (o := Fin k) (m := Fin m) hA)
                (fun x : ℝ => Real.log x))
      _ = blockDiagonal fun l =>
            (hA l).cfc (A := A l) (fun x : ℝ => Real.log x) := by
            simpa using
              (blockDiagonal_cfc (o := Fin k) (m := Fin m) (A := A) hA (fun x : ℝ => Real.log x))
  simpa [he] using htarget

lemma matrixLogDensity_reindex_pinchAncilla
    {ρ : Density (m * k)} :
    Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
        (finProdFinEquiv (m:=m) (n:=k)).symm
        (matrixLogDensity (ActiveInference.pinchAncillaDensity (m:=m) (k:=k) ρ)) =
      blockDiagonal fun l =>
        ((ActiveInference.ancillaBlock_isHermitian
            (A :=
              Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                (finProdFinEquiv (m:=m) (n:=k)).symm ρ.mat)
            (hA :=
              Matrix.reindex_isHermitian
                (A := ρ.mat) ρ.mat_isHermitian
                (finProdFinEquiv (m:=m) (n:=k)).symm) l).cfc
          (A :=
            ActiveInference.ancillaBlock (m:=m) (k:=k)
              (Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                (finProdFinEquiv (m:=m) (n:=k)).symm ρ.mat) l)
          fun x => Real.log x) := by
  classical
  set e :=
      (finProdFinEquiv (m:=m) (n:=k)).symm with he
  let ρBlocks :=
    Matrix.reindex e e ρ.mat
  have hHerm :
      ρBlocks.IsHermitian :=
    Matrix.reindex_isHermitian (A := ρ.mat) ρ.mat_isHermitian e
  have hAncilla :
      ∀ l : Fin k,
        (ActiveInference.ancillaBlock (m:=m) (k:=k) ρBlocks l).IsHermitian := by
    intro l
    exact ActiveInference.ancillaBlock_isHermitian
      (A := ρBlocks) hHerm l
  have hPinch :
      Matrix.reindex e e
          (ActiveInference.pinchAncillaDensity (m:=m) (k:=k) ρ).mat =
        blockDiagonal fun l : Fin k =>
          ActiveInference.ancillaBlock (m:=m) (k:=k) ρBlocks l := by
    simpa [ρBlocks, he] using
      (ActiveInference.pinchAncillaDensity_reindex_blockDiagonal (m:=m) (k:=k) ρ)
  simpa [ρBlocks, he] using
    (matrixLogDensity_reindex_blockDiagonal (m:=m) (k:=k)
      (ρ := ActiveInference.pinchAncillaDensity (m:=m) (k:=k) ρ)
      (A := fun l => ActiveInference.ancillaBlock (m:=m) (k:=k) ρBlocks l)
      hAncilla hPinch)

lemma pinchAncillaDensity_trace_matrixLog_blockSum
    {ρ : Density (m * k)} :
    Matrix.trace
        ((ActiveInference.pinchAncillaDensity (m:=m) (k:=k) ρ).mat *
          matrixLogDensity (ActiveInference.pinchAncillaDensity (m:=m) (k:=k) ρ)) =
      ∑ l : Fin k,
        Matrix.trace
          (ActiveInference.ancillaBlock (m:=m) (k:=k)
              (Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                (finProdFinEquiv (m:=m) (n:=k)).symm ρ.mat) l *
            ((ActiveInference.ancillaBlock_isHermitian
                (A :=
                  Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                    (finProdFinEquiv (m:=m) (n:=k)).symm ρ.mat)
                (hA :=
                  Matrix.reindex_isHermitian
                    (A := ρ.mat) ρ.mat_isHermitian
                    (finProdFinEquiv (m:=m) (n:=k)).symm) l).cfc
              (A :=
                ActiveInference.ancillaBlock (m:=m) (k:=k)
                  (Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                    (finProdFinEquiv (m:=m) (n:=k)).symm ρ.mat) l)
              fun x => Real.log x)) := by
  classical
  set e : Fin m × Fin k ≃ Fin (m * k) :=
      finProdFinEquiv (m:=m) (n:=k)
  set es := e.symm
  set ρPinch :=
      ActiveInference.pinchAncillaDensity (m:=m) (k:=k) ρ
  set ρBlocks :=
      Matrix.reindex es es ρ.mat
  have hTraceEq :
      Matrix.trace (ρPinch.mat * matrixLogDensity ρPinch) =
        Matrix.trace (Matrix.reindex es es
          (ρPinch.mat * matrixLogDensity ρPinch)) := by
    simpa [ρPinch, e, es] using
      (trace_reindex_symm (o:=Fin m × Fin k) (o':=Fin (m * k))
        e (A := ρPinch.mat * matrixLogDensity ρPinch)).symm
  have hMul :
      Matrix.reindex es es
          (ρPinch.mat * matrixLogDensity ρPinch) =
        Matrix.reindex es es ρPinch.mat *
          Matrix.reindex es es (matrixLogDensity ρPinch) := by
    exact
      (reindexAlgEquiv ℂ ℂ es).map_mul ρPinch.mat
        (matrixLogDensity ρPinch)
  have hMat :
      Matrix.reindex es es ρPinch.mat =
        Matrix.blockDiagonal fun l : Fin k =>
          ActiveInference.ancillaBlock (m:=m) (k:=k) ρBlocks l := by
    simpa [ρPinch, ρBlocks, e, es] using
      (ActiveInference.pinchAncillaDensity_reindex_blockDiagonal
        (m:=m) (k:=k) ρ)
  have hLog :
      Matrix.reindex es es (matrixLogDensity ρPinch) =
        Matrix.blockDiagonal fun l : Fin k =>
          ((ActiveInference.ancillaBlock_isHermitian
              (A := ρBlocks)
              (hA :=
                Matrix.reindex_isHermitian
                  (A := ρ.mat) ρ.mat_isHermitian es) l).cfc
            (A := ActiveInference.ancillaBlock (m:=m) (k:=k) ρBlocks l)
            fun x => Real.log x) := by
    simpa [ρPinch, ρBlocks, e, es] using
      (matrixLogDensity_reindex_pinchAncilla (m:=m) (k:=k) (ρ := ρ))
  have hDiagMul :
      Matrix.reindex es es ρPinch.mat *
          Matrix.reindex es es (matrixLogDensity ρPinch) =
        Matrix.blockDiagonal fun l : Fin k =>
          ActiveInference.ancillaBlock (m:=m) (k:=k) ρBlocks l *
            ((ActiveInference.ancillaBlock_isHermitian
                (A := ρBlocks)
                (hA :=
                  Matrix.reindex_isHermitian
                    (A := ρ.mat) ρ.mat_isHermitian es) l).cfc
              (A := ActiveInference.ancillaBlock (m:=m) (k:=k) ρBlocks l)
              fun x => Real.log x) := by
    have hblock :=
      (Matrix.blockDiagonal_mul
          (M := fun l : Fin k =>
            ActiveInference.ancillaBlock (m:=m) (k:=k) ρBlocks l)
          (N := fun l : Fin k =>
            ((ActiveInference.ancillaBlock_isHermitian
                (A := ρBlocks)
                (hA :=
                  Matrix.reindex_isHermitian
                    (A := ρ.mat) ρ.mat_isHermitian es) l).cfc
              (A := ActiveInference.ancillaBlock (m:=m) (k:=k) ρBlocks l)
              fun x => Real.log x))).symm
    rw [hMat, hLog]
    exact hblock
  have hBlock :
      Matrix.reindex es es
          (ρPinch.mat * matrixLogDensity ρPinch) =
        Matrix.blockDiagonal fun l : Fin k =>
          ActiveInference.ancillaBlock (m:=m) (k:=k) ρBlocks l *
            ((ActiveInference.ancillaBlock_isHermitian
                (A := ρBlocks)
                (hA :=
                  Matrix.reindex_isHermitian
                    (A := ρ.mat) ρ.mat_isHermitian es) l).cfc
              (A := ActiveInference.ancillaBlock (m:=m) (k:=k) ρBlocks l)
              fun x => Real.log x) :=
    hMul.trans hDiagMul
  have hTraceBlock :
      Matrix.trace (ρPinch.mat * matrixLogDensity ρPinch) =
        Matrix.trace (Matrix.blockDiagonal fun l : Fin k =>
          ActiveInference.ancillaBlock (m:=m) (k:=k) ρBlocks l *
            ((ActiveInference.ancillaBlock_isHermitian
                (A := ρBlocks)
                (hA :=
                  Matrix.reindex_isHermitian
                    (A := ρ.mat) ρ.mat_isHermitian es) l).cfc
              (A := ActiveInference.ancillaBlock (m:=m) (k:=k) ρBlocks l)
              fun x => Real.log x)) := by
    simpa [hBlock] using hTraceEq
  have hSum :
      Matrix.trace (Matrix.blockDiagonal fun l : Fin k =>
        ActiveInference.ancillaBlock (m:=m) (k:=k) ρBlocks l *
          ((ActiveInference.ancillaBlock_isHermitian
              (A := ρBlocks)
              (hA :=
                Matrix.reindex_isHermitian
                  (A := ρ.mat) ρ.mat_isHermitian es) l).cfc
            (A := ActiveInference.ancillaBlock (m:=m) (k:=k) ρBlocks l)
            fun x => Real.log x)) =
        ∑ l : Fin k,
          Matrix.trace
            (ActiveInference.ancillaBlock (m:=m) (k:=k) ρBlocks l *
              ((ActiveInference.ancillaBlock_isHermitian
                  (A := ρBlocks)
                  (hA :=
                    Matrix.reindex_isHermitian
                      (A := ρ.mat) ρ.mat_isHermitian es) l).cfc
                (A := ActiveInference.ancillaBlock (m:=m) (k:=k) ρBlocks l)
                fun x => Real.log x)) := by
    simpa using (Matrix.trace_blockDiagonal (M := fun l : Fin k =>
      ActiveInference.ancillaBlock (m:=m) (k:=k) ρBlocks l *
        ((ActiveInference.ancillaBlock_isHermitian
            (A := ρBlocks)
            (hA :=
              Matrix.reindex_isHermitian
                (A := ρ.mat) ρ.mat_isHermitian es) l).cfc
          (A := ActiveInference.ancillaBlock (m:=m) (k:=k) ρBlocks l)
          fun x => Real.log x)))
  simpa [ρPinch, ρBlocks, e, es] using hTraceBlock.trans hSum

lemma pinchAncillaDensity_trace_matrixLog_blockSum_re
    {ρ : Density (m * k)} :
    (Matrix.trace
        ((ActiveInference.pinchAncillaDensity (m:=m) (k:=k) ρ).mat *
          matrixLogDensity
            (ActiveInference.pinchAncillaDensity (m:=m) (k:=k) ρ))).re =
      ∑ l : Fin k,
        (Matrix.trace
          (ActiveInference.ancillaBlock (m:=m) (k:=k)
              (Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                (finProdFinEquiv (m:=m) (n:=k)).symm ρ.mat) l *
            ((ActiveInference.ancillaBlock_isHermitian
                (A :=
                  Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                    (finProdFinEquiv (m:=m) (n:=k)).symm ρ.mat)
                (hA :=
                  Matrix.reindex_isHermitian
                    ρ.mat_isHermitian
                    (finProdFinEquiv (m:=m) (n:=k)).symm) l).cfc
              (A :=
                ActiveInference.ancillaBlock (m:=m) (k:=k)
                  (Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                    (finProdFinEquiv (m:=m) (n:=k)).symm ρ.mat) l)
              fun x => Real.log x))).re := by
  classical
  have :=
    pinchAncillaDensity_trace_matrixLog_blockSum (m:=m) (k:=k) (ρ := ρ)
  have hre := congrArg Complex.re this
  simpa [Complex.re_sum] using hre

lemma vnEntropy_pinchAncilla_eq_blockSum
    {ρ : Density (m * k)} :
    vnEntropy
        (ActiveInference.pinchAncillaDensity (m:=m) (k:=k) ρ) =
      -∑ l : Fin k,
          (Matrix.trace
            (ActiveInference.ancillaBlock (m:=m) (k:=k)
                (Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                  (finProdFinEquiv (m:=m) (n:=k)).symm ρ.mat) l *
              ((ActiveInference.ancillaBlock_isHermitian
                  (A :=
                    Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                      (finProdFinEquiv (m:=m) (n:=k)).symm ρ.mat)
                  (hA :=
                    Matrix.reindex_isHermitian
                      ρ.mat_isHermitian
                      (finProdFinEquiv (m:=m) (n:=k)).symm) l).cfc
                (A :=
                  ActiveInference.ancillaBlock (m:=m) (k:=k)
                    (Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                      (finProdFinEquiv (m:=m) (n:=k)).symm ρ.mat) l)
                fun x => Real.log x))).re := by
  classical
  simp [vnEntropy, pinchAncillaDensity_trace_matrixLog_blockSum_re]

lemma pinchAncillaDensity_trace_matrixLog_reindexed
    {ρ σ : Density (m * k)} :
    Matrix.trace
        ((ActiveInference.pinchAncillaDensity (m:=m) (k:=k) ρ).mat *
          matrixLogDensity σ) =
      Matrix.trace
        (Matrix.blockDiagonal
            (fun l : Fin k =>
              ActiveInference.ancillaBlock (m:=m) (k:=k)
                (Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                  (finProdFinEquiv (m:=m) (n:=k)).symm ρ.mat) l) *
          Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
            (finProdFinEquiv (m:=m) (n:=k)).symm
            (matrixLogDensity σ)) := by
  classical
  set e : Fin m × Fin k ≃ Fin (m * k) :=
      finProdFinEquiv (m:=m) (n:=k)
  set es := e.symm
  set ρPinch :=
      ActiveInference.pinchAncillaDensity (m:=m) (k:=k) ρ
  have htrace :=
    (Matrix.trace_reindex_symm (o:=Fin m × Fin k) (o':=Fin (m * k)) e
      (A := ρPinch.mat * matrixLogDensity σ)).symm
  have hmul :
      Matrix.reindex es es
          (ρPinch.mat * matrixLogDensity σ) =
        Matrix.reindex es es ρPinch.mat *
          Matrix.reindex es es (matrixLogDensity σ) := by
    exact (reindexAlgEquiv ℂ ℂ es).map_mul ρPinch.mat (matrixLogDensity σ)
  have hmat :
      Matrix.reindex es es ρPinch.mat =
        Matrix.blockDiagonal
          (fun l : Fin k =>
            ActiveInference.ancillaBlock (m:=m) (k:=k)
              (Matrix.reindex es es ρ.mat) l) := by
    simpa [ρPinch, es, e] using
      (ActiveInference.pinchAncillaDensity_reindex_blockDiagonal
        (m:=m) (k:=k) ρ)
  have hrewrite :
      Matrix.trace
          ((ActiveInference.pinchAncillaDensity (m:=m) (k:=k) ρ).mat *
            matrixLogDensity σ) =
        Matrix.trace
            (Matrix.blockDiagonal
                (fun l : Fin k =>
                  ActiveInference.ancillaBlock (m:=m) (k:=k)
                    (Matrix.reindex es es ρ.mat) l) *
              Matrix.reindex es es (matrixLogDensity σ)) := by
    simpa [ρPinch, es, e, hmul, hmat] using htrace
  simpa [e, es] using hrewrite

lemma pinchAncillaDensity_trace_matrixLog_sum
    {ρ σ : Density (m * k)} :
    Matrix.trace
        ((ActiveInference.pinchAncillaDensity (m:=m) (k:=k) ρ).mat *
          matrixLogDensity σ) =
      ∑ l : Fin k,
        Matrix.trace
          (ActiveInference.ancillaBlock (m:=m) (k:=k)
              (Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                (finProdFinEquiv (m:=m) (n:=k)).symm ρ.mat) l *
            ActiveInference.ancillaBlock (m:=m) (k:=k)
              (Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                (finProdFinEquiv (m:=m) (n:=k)).symm
                (matrixLogDensity σ)) l) := by
  classical
  have :=
    pinchAncillaDensity_trace_matrixLog_reindexed
      (m:=m) (k:=k) (ρ := ρ) (σ := σ)
  have h :=
    Matrix.trace_blockDiagonal_mul_ancilla
      (m:=m) (k:=k)
      (A := fun l : Fin k =>
        ActiveInference.ancillaBlock (m:=m) (k:=k)
          (Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
            (finProdFinEquiv (m:=m) (n:=k)).symm ρ.mat) l)
      (B :=
        Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
          (finProdFinEquiv (m:=m) (n:=k)).symm
          (matrixLogDensity σ))
  simpa using this.trans h

lemma qRelEnt_pinchAncilla_decompose
    {ρ σ : Density (m * k)} :
    qRelEnt
        (ActiveInference.pinchAncillaDensity (m:=m) (k:=k) ρ) σ =
      (∑ l : Fin k,
          (Matrix.trace
            (ActiveInference.ancillaBlock (m:=m) (k:=k)
                (Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                  (finProdFinEquiv (m:=m) (n:=k)).symm ρ.mat) l *
              ((ActiveInference.ancillaBlock_isHermitian
                  (A :=
                    Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                      (finProdFinEquiv (m:=m) (n:=k)).symm ρ.mat)
                  (hA :=
                    Matrix.reindex_isHermitian
                      ρ.mat_isHermitian
                      (finProdFinEquiv (m:=m) (n:=k)).symm) l).cfc
                (A :=
                  ActiveInference.ancillaBlock (m:=m) (k:=k)
                    (Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                      (finProdFinEquiv (m:=m) (n:=k)).symm ρ.mat) l)
                fun x => Real.log x))).re) -
        (∑ l : Fin k,
            (Matrix.trace
              (ActiveInference.ancillaBlock (m:=m) (k:=k)
                  (Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                    (finProdFinEquiv (m:=m) (n:=k)).symm ρ.mat) l *
                ActiveInference.ancillaBlock (m:=m) (k:=k)
                  (Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                    (finProdFinEquiv (m:=m) (n:=k)).symm
                    (matrixLogDensity σ)) l)).re) := by
  classical
  have hlog :
      (Matrix.trace
          ((ActiveInference.pinchAncillaDensity (m:=m) (k:=k) ρ).mat *
            matrixLogDensity (ActiveInference.pinchAncillaDensity
              (m:=m) (k:=k) ρ))).re =
        ∑ l : Fin k,
          (Matrix.trace
            (ActiveInference.ancillaBlock (m:=m) (k:=k)
                (Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                  (finProdFinEquiv (m:=m) (n:=k)).symm ρ.mat) l *
              ((ActiveInference.ancillaBlock_isHermitian
                  (A :=
                    Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                      (finProdFinEquiv (m:=m) (n:=k)).symm ρ.mat)
                  (hA :=
                    Matrix.reindex_isHermitian
                      ρ.mat_isHermitian
                      (finProdFinEquiv (m:=m) (n:=k)).symm) l).cfc
                (A :=
                  ActiveInference.ancillaBlock (m:=m) (k:=k)
                    (Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                      (finProdFinEquiv (m:=m) (n:=k)).symm ρ.mat) l)
                fun x => Real.log x))).re :=
    pinchAncillaDensity_trace_matrixLog_blockSum_re
      (m:=m) (k:=k) (ρ := ρ)
  have hcross :
      (Matrix.trace
          ((ActiveInference.pinchAncillaDensity (m:=m) (k:=k) ρ).mat *
            matrixLogDensity σ)).re =
        ∑ l : Fin k,
          (Matrix.trace
            (ActiveInference.ancillaBlock (m:=m) (k:=k)
                (Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                  (finProdFinEquiv (m:=m) (n:=k)).symm ρ.mat) l *
              ActiveInference.ancillaBlock (m:=m) (k:=k)
                (Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                  (finProdFinEquiv (m:=m) (n:=k)).symm
                  (matrixLogDensity σ)) l)).re := by
    have :=
      pinchAncillaDensity_trace_matrixLog_sum
        (m:=m) (k:=k) (ρ := ρ) (σ := σ)
    have hre := congrArg Complex.re this
    simpa [Complex.re_sum] using hre
  -- Expand `qRelEnt` and distribute over the subtraction in the logarithm term.
  have hdist :
      (Matrix.trace
          ((ActiveInference.pinchAncillaDensity (m:=m) (k:=k) ρ).mat *
            (matrixLogDensity (ActiveInference.pinchAncillaDensity (m:=m) (k:=k) ρ) -
              matrixLogDensity σ))).re =
        (Matrix.trace
            ((ActiveInference.pinchAncillaDensity (m:=m) (k:=k) ρ).mat *
              matrixLogDensity (ActiveInference.pinchAncillaDensity (m:=m) (k:=k) ρ))).re -
          (Matrix.trace
              ((ActiveInference.pinchAncillaDensity (m:=m) (k:=k) ρ).mat *
                matrixLogDensity σ)).re := by
    -- `A * (B - C)` and linearity of `trace`, then take real parts.
    have hTrace :
        Matrix.trace
            ((ActiveInference.pinchAncillaDensity (m:=m) (k:=k) ρ).mat *
              (matrixLogDensity (ActiveInference.pinchAncillaDensity (m:=m) (k:=k) ρ) -
                matrixLogDensity σ)) =
          Matrix.trace
              ((ActiveInference.pinchAncillaDensity (m:=m) (k:=k) ρ).mat *
                matrixLogDensity (ActiveInference.pinchAncillaDensity (m:=m) (k:=k) ρ)) -
            Matrix.trace
              ((ActiveInference.pinchAncillaDensity (m:=m) (k:=k) ρ).mat *
                matrixLogDensity σ) := by
      -- First push the subtraction outside of the multiplication, then outside the trace.
      simp [Matrix.mul_sub, Matrix.trace_sub]
    have hre := congrArg Complex.re hTrace
    simpa [Complex.sub_re] using hre
  -- Substitute the blockwise trace identities.
  -- `Finset.sum_sub_distrib` handles the difference of sums on the RHS.
  simp [qRelEnt, hdist, hlog, hcross]

lemma ancillaBlock_reindex_matrixLogDensity_pinchAncilla
    {σ : Density (m * k)} (l : Fin k) :
    ActiveInference.ancillaBlock (m:=m) (k:=k)
        ((matrixLogDensity
            (ActiveInference.pinchAncillaDensity (m:=m) (k:=k) σ)).submatrix
          (finProdFinEquiv (m:=m) (n:=k))
          (finProdFinEquiv (m:=m) (n:=k))) l =
      ((ActiveInference.ancillaBlock_isHermitian
          (A :=
            Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
              (finProdFinEquiv (m:=m) (n:=k)).symm σ.mat)
          (hA :=
            Matrix.reindex_isHermitian
              (A := σ.mat) σ.mat_isHermitian
              (finProdFinEquiv (m:=m) (n:=k)).symm) l).cfc
        (A :=
          ActiveInference.ancillaBlock (m:=m) (k:=k)
            (Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
              (finProdFinEquiv (m:=m) (n:=k)).symm σ.mat) l)
        fun x => Real.log x) := by
  classical
  have hreindex :=
    matrixLogDensity_reindex_pinchAncilla (m:=m) (k:=k) (ρ := σ)
  -- Apply `ancillaBlock` to both sides and collapse the block diagonal.
  have hBlock :=
    congrArg
      (fun M =>
        ActiveInference.ancillaBlock (m:=m) (k:=k) M l)
      hreindex
  -- `ancillaBlock` of a block diagonal matrix is its diagonal block.
  -- The `simp` proof avoids having to name intermediate maps.
  simpa [Matrix.reindex_apply, ActiveInference.ancillaBlock, Matrix.blockDiagonal_apply, Matrix.submatrix] using hBlock

lemma qRelEnt_pinchAncilla_decompose_pinch
    {ρ σ : Density (m * k)} :
    qRelEnt
        (ActiveInference.pinchAncillaDensity (m:=m) (k:=k) ρ)
        (ActiveInference.pinchAncillaDensity (m:=m) (k:=k) σ) =
      (∑ l : Fin k,
          (Matrix.trace
              (ActiveInference.ancillaBlock (m:=m) (k:=k)
                  (Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                    (finProdFinEquiv (m:=m) (n:=k)).symm ρ.mat) l *
                ((ActiveInference.ancillaBlock_isHermitian
                    (A :=
                      Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                        (finProdFinEquiv (m:=m) (n:=k)).symm ρ.mat)
                    (hA :=
                      Matrix.reindex_isHermitian
                        (A := ρ.mat) ρ.mat_isHermitian
                        (finProdFinEquiv (m:=m) (n:=k)).symm) l).cfc
                  (A :=
                    ActiveInference.ancillaBlock (m:=m) (k:=k)
                      (Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                        (finProdFinEquiv (m:=m) (n:=k)).symm ρ.mat) l)
                  fun x => Real.log x))).re) -
        (∑ l : Fin k,
            (Matrix.trace
              (ActiveInference.ancillaBlock (m:=m) (k:=k)
                  (Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                    (finProdFinEquiv (m:=m) (n:=k)).symm ρ.mat) l *
                ((ActiveInference.ancillaBlock_isHermitian
                    (A :=
                      Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                        (finProdFinEquiv (m:=m) (n:=k)).symm σ.mat)
                    (hA :=
                      Matrix.reindex_isHermitian
                        (A := σ.mat) σ.mat_isHermitian
                        (finProdFinEquiv (m:=m) (n:=k)).symm) l).cfc
                  (A :=
                    ActiveInference.ancillaBlock (m:=m) (k:=k)
                      (Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                        (finProdFinEquiv (m:=m) (n:=k)).symm σ.mat) l)
                  fun x => Real.log x))).re) := by
  classical
  -- Start from the one-sided decomposition and specialize `σ` to its pinched version.
  have h :=
    qRelEnt_pinchAncilla_decompose (m:=m) (k:=k)
      (ρ := ρ) (σ := ActiveInference.pinchAncillaDensity (m:=m) (k:=k) σ)
  -- Rewrite the cross term using `matrixLogDensity_reindex_pinchAncilla`.
  -- `simp` with `ancillaBlock_reindex_matrixLogDensity_pinchAncilla` collapses each block.
  simpa [ancillaBlock_reindex_matrixLogDensity_pinchAncilla (m:=m) (k:=k) (σ := σ)] using h

end Matrix

namespace HeytingLean
namespace Quantum

open Matrix Complex
open scoped Matrix

noncomputable section

variable {n : ℕ}

section MatrixLogDensity

variable (ρ : Density n)

lemma matrixLogDensity_mulVec_eigenvector {v : Fin n → ℂ} {μ : ℝ}
    (hv : ρ.mat.mulVec v = (μ : ℂ) • v) :
    (matrixLogDensity ρ).mulVec v = (Real.log μ : ℂ) • v := by
  classical
  set h := ρ.mat_isHermitian
  set U : Matrix (Fin n) (Fin n) ℂ :=
      (h.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
  set d := fun i => (h.eigenvalues i : ℂ)
  set x := (star U).mulVec v
  have hDiagFun :
      (Complex.ofReal ∘ (fun x => Real.log x) ∘ h.eigenvalues) =
        fun i => (Complex.ofReal (Real.log (h.eigenvalues i))) := by
    funext i; simp
  have hSpectral :
      ρ.mat = U * Matrix.diagonal d * star U := by
    simpa [h, U, d] using h.spectral_theorem
  have hUnitary_star :
      (star U) * U = (1 : Matrix (Fin n) (Fin n) ℂ) :=
    unitary.star_mul_self_of_mem (hU := h.eigenvectorUnitary.property)
  have hUnitary :
      U * star U = (1 : Matrix (Fin n) (Fin n) ℂ) :=
    unitary.mul_star_self_of_mem (hU := h.eigenvectorUnitary.property)
  have hLeft :
      (star U) * ρ.mat = Matrix.diagonal d * star U := by
    calc
      (star U) * ρ.mat
          = (star U) * (U * Matrix.diagonal d * star U) := by
              simp [hSpectral]
      _ = ((star U) * U) * Matrix.diagonal d * star U := by
              simp [Matrix.mul_assoc]
      _ = Matrix.diagonal d * star U := by
              simp [hUnitary_star]
  have hx_eq :
      (Matrix.diagonal d).mulVec x = (μ : ℂ) • x := by
    have := congrArg (fun w : Fin n → ℂ => (star U).mulVec w) hv
    simpa [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mulVec_smul, x,
      hLeft]
      using this
  have hdiag :
      (Matrix.diagonal fun i => (Complex.ofReal (Real.log (h.eigenvalues i)))).mulVec x =
        (Real.log μ : ℂ) • x := by
    funext i
    have hxEntry :
        d i * x i = (μ : ℂ) * x i := by
      simpa [Matrix.mulVec_diagonal, x] using
        congrArg (fun w : Fin n → ℂ => w i) hx_eq
    by_cases hxi : x i = 0
    · have hx0 : x i = 0 := hxi
      simp [Matrix.mulVec_diagonal, x, hx0]
    · have hi :
        d i = (μ : ℂ) := by
          exact mul_right_cancel₀ hxi hxEntry
      have hReal : h.eigenvalues i = μ := by
        simpa [d] using hi
      simp [Matrix.mulVec_diagonal, x, hReal]
  have hLog :
      matrixLogDensity ρ =
        U * Matrix.diagonal
            (fun i => (Complex.ofReal (Real.log (h.eigenvalues i))))
          * star U := by
    simp [matrixLogDensity, Matrix.IsHermitian.cfc, U, hDiagFun]
  have hMul :
      (matrixLogDensity ρ).mulVec v =
        U.mulVec
          ((Matrix.diagonal fun i => (Complex.ofReal (Real.log (h.eigenvalues i)))).mulVec x) := by
    simp [hLog, Matrix.mulVec_mulVec, Matrix.mul_assoc, x]
  have hMul_log := hMul
  simp [hdiag] at hMul_log
  have hUx :
      U.mulVec x = v := by
    have := congrArg (fun A => A.mulVec v) hUnitary
    simpa [Matrix.mulVec_mulVec, Matrix.mul_assoc, x] using this
  calc
    (matrixLogDensity ρ).mulVec v
        = U.mulVec ((Real.log μ : ℂ) • x) := hMul_log
    _ = (Real.log μ : ℂ) • U.mulVec x := by
          simp [Matrix.mulVec_smul]
    _ = (Real.log μ : ℂ) • v := by
          simp [hUx]

/-- `matrixLogDensity` acts diagonally on the eigenbasis from the spectral theorem. -/
lemma matrixLogDensity_mulVec_eigenvectorBasis (j : Fin n) :
    (matrixLogDensity ρ).mulVec (ρ.mat_isHermitian.eigenvectorBasis j) =
      (Real.log (ρ.mat_isHermitian.eigenvalues j) : ℂ) •
        (ρ.mat_isHermitian.eigenvectorBasis j) := by
  classical
  set h := ρ.mat_isHermitian
  simpa [h] using
    matrixLogDensity_mulVec_eigenvector (ρ := ρ)
      (v := h.eigenvectorBasis j) (μ := h.eigenvalues j)
      (by
        simpa [h] using
          Matrix.IsHermitian.mulVec_eigenvectorBasis (hA := ρ.mat_isHermitian) (j := j))

/-- Scaling a Hermitian matrix by a real scalar preserves Hermitian-ness. -/
lemma isHermitian_smul_real {n : ℕ} {A : Mat n} (hA : A.IsHermitian) (c : ℝ) :
    (((c : ℂ) • A).IsHermitian) := by
  classical
  unfold Matrix.IsHermitian at *
  calc
    Matrix.conjTranspose ((c : ℂ) • A) = star (c : ℂ) • Matrix.conjTranspose A := by
      simp [Matrix.conjTranspose_smul]
    _ = (c : ℂ) • A := by
      simp [hA]

/-- `Real.log` under the Hermitian functional calculus acts diagonally on eigenvectors. -/
lemma cfc_log_mulVec_eigenvector {n : ℕ} {A : Mat n} (hA : A.IsHermitian)
    {v : Fin n → ℂ} {μ : ℝ} (hv : A.mulVec v = (μ : ℂ) • v) :
    (hA.cfc (A := A) (fun x => Real.log x)).mulVec v = (Real.log μ : ℂ) • v := by
  classical
  set U : Matrix (Fin n) (Fin n) ℂ :=
      (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
  set d := fun i : Fin n => (hA.eigenvalues i : ℂ)
  set x := (star U).mulVec v
  have hDiagFun :
      (Complex.ofReal ∘ (fun x => Real.log x) ∘ hA.eigenvalues) =
        fun i => (Complex.ofReal (Real.log (hA.eigenvalues i))) := by
    funext i; simp
  have hSpectral :
      A = U * Matrix.diagonal d * star U := by
    simpa [U, d] using hA.spectral_theorem
  have hUnitary_star :
      (star U) * U = (1 : Matrix (Fin n) (Fin n) ℂ) :=
    unitary.star_mul_self_of_mem (hU := hA.eigenvectorUnitary.property)
  have hUnitary :
      U * star U = (1 : Matrix (Fin n) (Fin n) ℂ) :=
    unitary.mul_star_self_of_mem (hU := hA.eigenvectorUnitary.property)
  have hLeft :
      (star U) * A = Matrix.diagonal d * star U := by
    calc
      (star U) * A
          = (star U) * (U * Matrix.diagonal d * star U) := by
              simp [hSpectral]
      _ = ((star U) * U) * Matrix.diagonal d * star U := by
              simp [Matrix.mul_assoc]
      _ = Matrix.diagonal d * star U := by
              simp [hUnitary_star]
  have hx_eq :
      (Matrix.diagonal d).mulVec x = (μ : ℂ) • x := by
    have := congrArg (fun w : Fin n → ℂ => (star U).mulVec w) hv
    simpa [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mulVec_smul, x, hLeft] using this
  have hdiag :
      (Matrix.diagonal fun i => (Complex.ofReal (Real.log (hA.eigenvalues i)))).mulVec x =
        (Real.log μ : ℂ) • x := by
    funext i
    have hxEntry :
        d i * x i = (μ : ℂ) * x i := by
      simpa [Matrix.mulVec_diagonal, x] using
        congrArg (fun w : Fin n → ℂ => w i) hx_eq
    by_cases hxi : x i = 0
    · have hx0 : x i = 0 := hxi
      simp [Matrix.mulVec_diagonal, x, hx0]
    · have hi : d i = (μ : ℂ) :=
        mul_right_cancel₀ hxi hxEntry
      have hReal : hA.eigenvalues i = μ := by
        simpa [d] using hi
      simp [Matrix.mulVec_diagonal, x, hReal]
  have hLog :
      hA.cfc (A := A) (fun x => Real.log x) =
        U * Matrix.diagonal
            (fun i => (Complex.ofReal (Real.log (hA.eigenvalues i))))
          * star U := by
    simp [Matrix.IsHermitian.cfc, U, hDiagFun]
  have hMul :
      (hA.cfc (A := A) (fun x => Real.log x)).mulVec v =
        U.mulVec
          ((Matrix.diagonal fun i => (Complex.ofReal (Real.log (hA.eigenvalues i)))).mulVec x) := by
    simp [hLog, Matrix.mulVec_mulVec, Matrix.mul_assoc, x]
  have hMul_log := hMul
  simp [hdiag] at hMul_log
  have hUx : U.mulVec x = v := by
    have := congrArg (fun A => A.mulVec v) hUnitary
    simpa [Matrix.mulVec_mulVec, Matrix.mul_assoc, x] using this
  calc
    (hA.cfc (A := A) (fun x => Real.log x)).mulVec v
        = U.mulVec ((Real.log μ : ℂ) • x) := hMul_log
    _ = (Real.log μ : ℂ) • U.mulVec x := by
          simp [Matrix.mulVec_smul]
    _ = (Real.log μ : ℂ) • v := by
          simp [hUx]

/-- Kernel-safe scaling identity for the spectral logarithm evaluated via a trace. -/
lemma trace_mul_log_smul {n : ℕ} {A : Mat n}
    (hHerm : A.IsHermitian) (hPos : PosSemidef A)
    {c : ℝ} (hc : 0 < c) :
    Matrix.trace (A * cfc (fun x : ℝ => Real.log x) ((c : ℂ) • A)) =
      Matrix.trace (A * cfc (fun x : ℝ => Real.log x) A) +
        (Real.log c : ℂ) * Matrix.trace A := by
  classical
  set h := hHerm
  set U : Matrix (Fin n) (Fin n) ℂ := (h.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
  set evals : Fin n → ℝ := fun i => h.eigenvalues i
  set D := Matrix.diagonal fun i : Fin n => (evals i : ℂ)
  set L := Matrix.diagonal fun i : Fin n => (Real.log (evals i) : ℂ)
  set Lc := Matrix.diagonal fun i : Fin n => (Real.log (c * evals i) : ℂ)
  let hScaled : (((c : ℂ) • A).IsHermitian) :=
    isHermitian_smul_real (A := A) hHerm c
  have hcfcA :
      cfc (fun x : ℝ => Real.log x) A = h.cfc (A := A) (fun x => Real.log x) :=
    Matrix.IsHermitian.cfc_eq (A := A) h (fun x => Real.log x)
  have hcfcScaled :
      cfc (fun x : ℝ => Real.log x) ((c : ℂ) • A) =
        hScaled.cfc (A := (c : ℂ) • A) (fun x => Real.log x) :=
    Matrix.IsHermitian.cfc_eq (A := (c : ℂ) • A) hScaled (fun x => Real.log x)
  have hSpectral :
      A = U * D * star U := by
    simpa [U, D, evals] using h.spectral_theorem
  have hLogA :
      (h.cfc (A := A) fun x => Real.log x) =
        U * L * star U := by
    have hdiag :
        Matrix.diagonal (Complex.ofReal ∘ (fun x : ℝ => Real.log x) ∘ h.eigenvalues) = L := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [L, evals, Matrix.diagonal, Function.comp]
      · simp [L, Matrix.diagonal, hij]
    -- `Matrix.IsHermitian.cfc` is defined via the spectral theorem using a diagonal matrix.
    simp [U, Matrix.IsHermitian.cfc, hdiag]
  have hUnitary :
      U * star U = (1 : Mat n) :=
    unitary.mul_star_self_of_mem (hU := h.eigenvectorUnitary.property)
  have hUnitary' :
      star U * U = (1 : Mat n) :=
    unitary.star_mul_self_of_mem (hU := h.eigenvectorUnitary.property)
  have hTraceA :
      Matrix.trace A = ∑ i : Fin n, (evals i : ℂ) := by
    have hcycle₁ :
        Matrix.trace ((U * D) * star U) = Matrix.trace ((star U * U) * D) := by
      simpa [Matrix.mul_assoc] using Matrix.trace_mul_cycle (A := U) (B := D) (C := star U)
    have hcycle₂ :
        Matrix.trace ((star U * U) * D) = Matrix.trace ((D * star U) * U) := by
      simpa [Matrix.mul_assoc] using Matrix.trace_mul_cycle (A := star U) (B := U) (C := D)
    have hcycle :
        Matrix.trace (U * D * star U) = Matrix.trace (D * star U * U) := by
      simpa [Matrix.mul_assoc] using hcycle₁.trans hcycle₂
    calc
      Matrix.trace A = Matrix.trace (U * D * star U) := by
            simp [hSpectral]
      _ = Matrix.trace (D * star U * U) := hcycle
      _ = Matrix.trace D := by
            simp [Matrix.mul_assoc, hUnitary']
      _ = ∑ i : Fin n, (evals i : ℂ) := by
            simp [D, Matrix.trace_diagonal]
  have hTraceLog :
      Matrix.trace (A * (h.cfc (A := A) fun x => Real.log x)) =
        ∑ i : Fin n, (evals i : ℂ) * Real.log (evals i) := by
    have hProd :
        A * (h.cfc fun x => Real.log x) =
          U * (D * L) * star U := by
      calc
        A * (h.cfc fun x => Real.log x)
            = (U * D * star U) * (U * L * star U) := by
                simp [hSpectral, hLogA]
        _ = U * (D * (star U * (U * (L * star U)))) := by
              simp [Matrix.mul_assoc]
        _ = U * (D * (L * star U)) := by
              -- Simplify `star U * (U * X)` using `star U * U = 1`.
              have hinner : star U * (U * (L * star U)) = L * star U := by
                calc
                  star U * (U * (L * star U)) = (star U * U) * (L * star U) := by
                        simp [Matrix.mul_assoc]
                  _ = 1 * (L * star U) := by
                        simp [hUnitary']
                  _ = L * star U := by
                        simp
              simp [hinner]
        _ = U * (D * L) * star U := by
              simp [Matrix.mul_assoc]
    have :
        Matrix.trace (U * (D * L) * star U) =
          Matrix.trace (D * L) := by
      simpa [Matrix.mul_assoc, Matrix.trace_mul_cycle, hUnitary'] using
        Matrix.trace_mul_cycle (A := U) (B := D * L) (C := star U)
    have hDiag :
        Matrix.trace (D * L) =
          ∑ i, (evals i : ℂ) * Real.log (evals i) := by
      have hmulDiag :
          D * L =
            Matrix.diagonal fun i =>
              (evals i : ℂ) * Real.log (evals i) := by
        simp [D, L]
      calc
        Matrix.trace (D * L)
            = Matrix.trace (Matrix.diagonal fun i =>
                (evals i : ℂ) * Real.log (evals i)) := by
                  simp [hmulDiag]
        _ = ∑ i, (evals i : ℂ) * Real.log (evals i) := by
              simp [Matrix.trace_diagonal]
    calc
      Matrix.trace (A * (h.cfc (A := A) fun x => Real.log x))
          = Matrix.trace (U * (D * L) * star U) := by
                simp [hProd]
      _ = Matrix.trace (D * L) := this
      _ = ∑ i : Fin n, (evals i : ℂ) * Real.log (evals i) := hDiag
  have hConj :
      star U * (hScaled.cfc (A := (c : ℂ) • A) fun x => Real.log x) * U = Lc := by
    -- Identify the conjugated matrix by its action on the standard basis vectors `Pi.single j 1`.
    ext i j
    have hvec :
        (star U * (hScaled.cfc (A := (c : ℂ) • A) fun x => Real.log x) * U).mulVec
            (Pi.single (M := fun _ : Fin n => ℂ) j (1 : ℂ)) =
          Lc.mulVec (Pi.single (M := fun _ : Fin n => ℂ) j (1 : ℂ)) := by
      have hUj :
          U.mulVec (Pi.single j (1 : ℂ)) = WithLp.ofLp (h.eigenvectorBasis j) := by
        dsimp [U]
        exact Matrix.IsHermitian.eigenvectorUnitary_mulVec (hA := h) j
      have hUhj :
          (star U).mulVec (WithLp.ofLp (h.eigenvectorBasis j)) = Pi.single j (1 : ℂ) := by
        simpa [U] using Matrix.IsHermitian.star_eigenvectorUnitary_mulVec (hA := h) j
      have hvA :
          A.mulVec (WithLp.ofLp (h.eigenvectorBasis j)) =
            (evals j : ℂ) • WithLp.ofLp (h.eigenvectorBasis j) := by
        simpa [evals] using Matrix.IsHermitian.mulVec_eigenvectorBasis (hA := h) (j := j)
      have hvScaled :
          (((c : ℂ) • A).mulVec (WithLp.ofLp (h.eigenvectorBasis j))) =
            (c * evals j : ℂ) • WithLp.ofLp (h.eigenvectorBasis j) := by
        calc
          ((c : ℂ) • A).mulVec (WithLp.ofLp (h.eigenvectorBasis j))
              = (c : ℂ) • A.mulVec (WithLp.ofLp (h.eigenvectorBasis j)) := by
                  simpa using
                    (Matrix.smul_mulVec (b := (c : ℂ)) (M := A) (v := WithLp.ofLp (h.eigenvectorBasis j)))
          _ = (c : ℂ) • ((evals j : ℂ) • WithLp.ofLp (h.eigenvectorBasis j)) := by
                simp [hvA]
          _ = (↑c * ↑(evals j) : ℂ) • WithLp.ofLp (h.eigenvectorBasis j) := by
                simpa [mul_assoc] using
                  (smul_smul (a₁ := (c : ℂ)) (a₂ := (evals j : ℂ))
                    (b := WithLp.ofLp (h.eigenvectorBasis j)))
          _ = (c * evals j : ℂ) • WithLp.ofLp (h.eigenvectorBasis j) := by
                simp
      have hLogScaled :
          (hScaled.cfc (A := (c : ℂ) • A) (fun x => Real.log x)).mulVec
              (WithLp.ofLp (h.eigenvectorBasis j)) =
            (Real.log (c * evals j) : ℂ) • WithLp.ofLp (h.eigenvectorBasis j) := by
        have hvScaled' :
            (((c : ℂ) • A).mulVec (WithLp.ofLp (h.eigenvectorBasis j))) =
              ((c * evals j : ℝ) : ℂ) • WithLp.ofLp (h.eigenvectorBasis j) := by
          simpa [Complex.ofReal_mul, mul_assoc] using hvScaled
        simpa using
          (cfc_log_mulVec_eigenvector (A := (c : ℂ) • A) hScaled (v := WithLp.ofLp (h.eigenvectorBasis j))
            (μ := c * evals j) hvScaled')
      calc
        (star U * (hScaled.cfc (A := (c : ℂ) • A) fun x => Real.log x) * U).mulVec
            (Pi.single (M := fun _ : Fin n => ℂ) j (1 : ℂ))
            = (star U).mulVec
                ((hScaled.cfc (A := (c : ℂ) • A) fun x => Real.log x).mulVec
                  (U.mulVec (Pi.single (M := fun _ : Fin n => ℂ) j (1 : ℂ)))) := by
                    -- Avoid `simp` here: it tends to rewrite `mulVec (Pi.single _ 1)` into columns.
                    -- Use `mulVec_mulVec` explicitly instead.
                    let H :=
                      hScaled.cfc (A := (c : ℂ) • A) (fun x => Real.log x)
                    have h1 :
                        ((star U * H) * U).mulVec
                            (Pi.single (M := fun _ : Fin n => ℂ) j (1 : ℂ)) =
                          (star U * H).mulVec
                            (U.mulVec (Pi.single (M := fun _ : Fin n => ℂ) j (1 : ℂ))) := by
                      -- `mulVec` respects matrix multiplication.
                      simpa using
                        (Matrix.mulVec_mulVec
                          (v := Pi.single (M := fun _ : Fin n => ℂ) j (1 : ℂ))
                          (M := star U * H) (N := U)).symm
                    have h2 :
                        (star U * H).mulVec
                            (U.mulVec (Pi.single (M := fun _ : Fin n => ℂ) j (1 : ℂ))) =
                          (star U).mulVec
                            (H.mulVec (U.mulVec (Pi.single (M := fun _ : Fin n => ℂ) j (1 : ℂ)))) := by
                      exact
                        (Matrix.mulVec_mulVec
                          (v := U.mulVec (Pi.single (M := fun _ : Fin n => ℂ) j (1 : ℂ)))
                          (M := star U) (N := H)).symm
                    simpa [H, Matrix.mul_assoc] using h1.trans h2
        _ = (star U).mulVec
              ((hScaled.cfc (A := (c : ℂ) • A) fun x => Real.log x).mulVec
                (WithLp.ofLp (h.eigenvectorBasis j))) := by
                  simp [hUj]
        _ = (star U).mulVec ((Real.log (c * evals j) : ℂ) • WithLp.ofLp (h.eigenvectorBasis j)) := by
              simp [hLogScaled]
        _ = (Real.log (c * evals j) : ℂ) • Pi.single (M := fun _ : Fin n => ℂ) j (1 : ℂ) := by
              simp [Matrix.mulVec_smul, hUhj]
        _ = Lc.mulVec (Pi.single (M := fun _ : Fin n => ℂ) j (1 : ℂ)) := by
              ext k
              by_cases hk : k = j
              · subst hk
                simp [Lc, Matrix.mulVec_diagonal]
              · simp [Lc, Matrix.mulVec_diagonal, hk]
    -- Convert equality of mulVec on basis vectors into equality of matrix entries.
    have hcol :
        (star U * (hScaled.cfc (A := (c : ℂ) • A) fun x => Real.log x) * U).col j =
          Lc.col j := by
      simpa [Matrix.mulVec_single_one] using hvec
    have := congrArg (fun v : Fin n → ℂ => v i) hcol
    -- `Matrix.col` is defined as transpose; avoid rewriting transpose of products.
    simpa [Matrix.col, Matrix.transpose_apply] using this
  have hTraceLogc :
      Matrix.trace
          (A * (hScaled.cfc (A := (c : ℂ) • A) fun x => Real.log x)) =
        ∑ i : Fin n, (evals i : ℂ) * Real.log (c * evals i) := by
    have hProd :
        A * (hScaled.cfc (A := (c : ℂ) • A) fun x => Real.log x) =
          U * (D * Lc) * star U := by
      -- Insert `U * star U = 1` to use the conjugation identity `hConj`.
      calc
        A * (hScaled.cfc (A := (c : ℂ) • A) fun x => Real.log x)
            = (U * D * star U) * (hScaled.cfc (A := (c : ℂ) • A) fun x => Real.log x) := by
                simp [hSpectral]
        _ = U * D * (star U * (hScaled.cfc (A := (c : ℂ) • A) fun x => Real.log x)) := by
              simp [Matrix.mul_assoc]
        _ = U * D * ((star U * (hScaled.cfc (A := (c : ℂ) • A) fun x => Real.log x) * U) * star U) := by
              simp [Matrix.mul_assoc, hUnitary]
        _ = U * D * (Lc * star U) := by
              simp [hConj, Matrix.mul_assoc]
        _ = U * (D * Lc) * star U := by
              simp [Matrix.mul_assoc]
    have :
        Matrix.trace (U * (D * Lc) * star U) =
          Matrix.trace (D * Lc) := by
      simpa [Matrix.mul_assoc, Matrix.trace_mul_cycle, hUnitary'] using
        Matrix.trace_mul_cycle (A := U) (B := D * Lc) (C := star U)
    have hDiag :
        Matrix.trace (D * Lc) =
          ∑ i, (evals i : ℂ) * Real.log (c * evals i) := by
      have hmulDiag :
          D * Lc =
            Matrix.diagonal fun i =>
              (evals i : ℂ) * Real.log (c * evals i) := by
        simp [D, Lc]
      calc
        Matrix.trace (D * Lc)
            = Matrix.trace (Matrix.diagonal fun i =>
                (evals i : ℂ) * Real.log (c * evals i)) := by
                  simp [hmulDiag]
        _ = ∑ i : Fin n, (evals i : ℂ) * Real.log (c * evals i) := by
              simp [Matrix.trace_diagonal]
    calc
      Matrix.trace
          (A * (hScaled.cfc (A := (c : ℂ) • A) fun x => Real.log x))
          = Matrix.trace (U * (D * Lc) * star U) := by
              simp [hProd]
      _ = Matrix.trace (D * Lc) := this
      _ = ∑ i : Fin n, (evals i : ℂ) * Real.log (c * evals i) := hDiag
  have hTraceScale :
      (Real.log c : ℂ) * Matrix.trace A =
        ∑ i : Fin n, (Real.log c : ℂ) * (evals i : ℂ) := by
    simp [hTraceA, Finset.mul_sum]
  have hEigen_nonneg :
      ∀ i : Fin n, 0 ≤ evals i :=
    Matrix.IsHermitian.eigenvalues_nonneg_of_posSemidef
      (A := A) hHerm hPos
  have hscalar :
      ∀ i : Fin n,
        (evals i : ℂ) * Real.log (c * evals i) =
          (evals i : ℂ) * Real.log (evals i) +
            (Real.log c : ℂ) * (evals i : ℂ) := by
    intro i
    by_cases hEval0 : evals i = 0
    · simp [hEval0]
    · have hEvalPos :
          0 < evals i :=
        lt_of_le_of_ne' (hEigen_nonneg i) hEval0
      have hlog :
          Real.log (c * evals i) =
            Real.log c + Real.log (evals i) :=
        Real.log_mul (ne_of_gt hc) (ne_of_gt hEvalPos)
      have hcomm :
          (Real.log c : ℂ) * (evals i : ℂ) =
            (evals i : ℂ) * Real.log c := by
        simp [mul_comm]
      simp [hlog, mul_add, hcomm, add_comm]
  have hsum :
      ∑ i : Fin n, (evals i : ℂ) * Real.log (c * evals i) =
        ∑ i, (evals i : ℂ) * Real.log (evals i) +
          ∑ i, (Real.log c : ℂ) * (evals i : ℂ) := by
    have hpoint :
        (fun i : Fin n => (evals i : ℂ) * Real.log (c * evals i)) =
          fun i =>
            (evals i : ℂ) * Real.log (evals i) + (Real.log c : ℂ) * (evals i : ℂ) := by
      funext i
      simp [hscalar i]
    -- Sum the pointwise identity.
    calc
      (∑ i : Fin n, (evals i : ℂ) * Real.log (c * evals i))
          = ∑ i : Fin n,
              ((evals i : ℂ) * Real.log (evals i) + (Real.log c : ℂ) * (evals i : ℂ)) := by
                simp [hpoint]
      _ = (∑ i : Fin n, (evals i : ℂ) * Real.log (evals i)) +
            ∑ i : Fin n, (Real.log c : ℂ) * (evals i : ℂ) := by
                simp [Finset.sum_add_distrib]
  -- Rewrite the `cfc` terms to the chosen Hermitian functional calculus witnesses and finish.
  have hGoal :
      Matrix.trace
          (A * (hScaled.cfc (A := (c : ℂ) • A) fun x => Real.log x)) =
        Matrix.trace (A * (h.cfc (A := A) fun x => Real.log x)) +
          (Real.log c : ℂ) * Matrix.trace A := by
    calc
      Matrix.trace
          (A * (hScaled.cfc (A := (c : ℂ) • A) fun x => Real.log x))
          = ∑ i : Fin n, (evals i : ℂ) * Real.log (c * evals i) := hTraceLogc
      _ = ∑ i, (evals i : ℂ) * Real.log (evals i) +
              ∑ i, (Real.log c : ℂ) * (evals i : ℂ) := hsum
      _ = Matrix.trace (A * (h.cfc (A := A) fun x => Real.log x)) +
              (Real.log c : ℂ) * Matrix.trace A := by
            simp [hTraceLog, hTraceScale]
  -- Convert back to the `cfc` notation used in the statement.
  calc
    Matrix.trace (A * cfc (fun x : ℝ => Real.log x) ((c : ℂ) • A))
        = Matrix.trace (A * (hScaled.cfc (A := (c : ℂ) • A) fun x => Real.log x)) := by
              -- Rewrite the `cfc` term using the Hermitian functional calculus witness.
              rw [hcfcScaled]
    _ = Matrix.trace (A * (h.cfc (A := A) fun x => Real.log x)) +
          (Real.log c : ℂ) * Matrix.trace A := hGoal
    _ = Matrix.trace (A * cfc (fun x : ℝ => Real.log x) A) +
          (Real.log c : ℂ) * Matrix.trace A := by
          simp [hcfcA]

lemma trace_smul_mul_log_smul {n : ℕ} {A : Mat n}
    (hHerm : A.IsHermitian) (hPos : PosSemidef A)
    {c : ℝ} (hc : 0 < c) :
    Matrix.trace
        (((c : ℂ) • A) * cfc (fun x : ℝ => Real.log x) ((c : ℂ) • A)) =
      (c : ℂ) * Matrix.trace (A * cfc (fun x : ℝ => Real.log x) A) +
        (Real.log c : ℂ) * ((c : ℂ) * Matrix.trace A) := by
  classical
  have hbase :=
    trace_mul_log_smul (n := n) (A := A) hHerm hPos (c := c) hc
  have hleft :
      Matrix.trace (((c : ℂ) • A) * cfc (fun x : ℝ => Real.log x) ((c : ℂ) • A)) =
        (c : ℂ) * Matrix.trace (A * cfc (fun x : ℝ => Real.log x) ((c : ℂ) • A)) := by
    -- `((c:ℂ)•A) * X = (c:ℂ)•(A*X)`, then pull the scalar out of `trace`.
    calc
      Matrix.trace (((c : ℂ) • A) * cfc (fun x : ℝ => Real.log x) ((c : ℂ) • A))
          = Matrix.trace ((c : ℂ) • (A * cfc (fun x : ℝ => Real.log x) ((c : ℂ) • A))) := by
              simp
      _ = (c : ℂ) * Matrix.trace (A * cfc (fun x : ℝ => Real.log x) ((c : ℂ) • A)) := by
            simp [Matrix.trace_smul]
  calc
    Matrix.trace (((c : ℂ) • A) * cfc (fun x : ℝ => Real.log x) ((c : ℂ) • A))
        = (c : ℂ) * Matrix.trace (A * cfc (fun x : ℝ => Real.log x) ((c : ℂ) • A)) := hleft
    _ = (c : ℂ) *
          (Matrix.trace (A * cfc (fun x : ℝ => Real.log x) A) +
            (Real.log c : ℂ) * Matrix.trace A) := by
          exact congrArg (fun z => (c : ℂ) * z) hbase
    _ = (c : ℂ) * Matrix.trace (A * cfc (fun x : ℝ => Real.log x) A) +
          (Real.log c : ℂ) * ((c : ℂ) * Matrix.trace A) := by
          ring

/-- Scaling identity for the spectral logarithm on the right, with the kernel handled by a
support-indicator functional calculus term. -/
lemma cfc_log_smul_eq_add_supportIndicator {n : ℕ} {A : Mat n}
    (hHerm : A.IsHermitian) (hPos : PosSemidef A)
    {c : ℝ} (hc : 0 < c) :
    cfc (fun x : ℝ => Real.log x) ((c : ℂ) • A) =
      cfc (fun x : ℝ => Real.log x) A +
        (Real.log c : ℂ) •
          cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) A := by
  classical
  -- Rewrite `log(c•A)` as `log ∘ (c*·)` applied to `A` using `cfc_comp_const_mul`.
  have hCompCont :
      ContinuousOn (fun x : ℝ => Real.log x) ((fun x : ℝ => c * x) '' spectrum ℝ A) := by
    have hs :
        ((fun x : ℝ => c * x) '' spectrum ℝ A).Finite :=
      (Matrix.finite_real_spectrum (A := A)).image (fun x : ℝ => c * x)
    simpa using
      (Set.Finite.continuousOn (hs := hs) (f := fun x : ℝ => Real.log x))
  have hComp :
      cfc (fun x : ℝ => Real.log (c * x)) A =
        cfc (fun x : ℝ => Real.log x) ((c : ℂ) • A) := by
    -- `cfc_comp_const_mul` is stated with scalar multiplication over `ℝ`;
    -- `simp` converts `(c : ℝ) • A` to `((c : ℂ) • A)`.
    simpa using
      (cfc_comp_const_mul (r := c) (f := fun x : ℝ => Real.log x) (a := A) (hf := hCompCont))
  -- Pointwise identity on the (nonnegative) spectrum.
  have hEqOn :
      Set.EqOn (fun x : ℝ => Real.log (c * x))
        (fun x : ℝ => Real.log x + Real.log c * (if x = 0 then 0 else 1))
        (spectrum ℝ A) := by
    intro x hx
    by_cases hx0 : x = 0
    · subst hx0
      simp
    ·
      have hx_nonneg : 0 ≤ x := by
        -- Every point in the real spectrum of a Hermitian matrix is an eigenvalue.
        obtain ⟨j, rfl⟩ := (hHerm.spectrum_real_eq_range_eigenvalues ▸ hx : x ∈ Set.range hHerm.eigenvalues)
        exact Matrix.IsHermitian.eigenvalues_nonneg_of_posSemidef (A := A) hHerm hPos j
      have hx_pos : 0 < x := lt_of_le_of_ne' hx_nonneg hx0
      have hlog :
          Real.log (c * x) = Real.log c + Real.log x :=
        Real.log_mul (ne_of_gt hc) (ne_of_gt hx_pos)
      -- Rearrange to match the target expression.
      simp [hlog, hx0, add_comm]
  have hContLog :
      ContinuousOn (fun x : ℝ => Real.log x) (spectrum ℝ A) := by
    simpa using
      (Set.Finite.continuousOn (hs := (Matrix.finite_real_spectrum (A := A)))
        (f := fun x : ℝ => Real.log x))
  have hContInd :
      ContinuousOn (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) (spectrum ℝ A) := by
    simpa using
      (Set.Finite.continuousOn (hs := (Matrix.finite_real_spectrum (A := A)))
        (f := fun x : ℝ => if x = 0 then (0 : ℝ) else 1))
  have hContScaled :
      ContinuousOn (fun x : ℝ => Real.log c * (if x = 0 then 0 else 1)) (spectrum ℝ A) := by
    simpa [mul_assoc] using (continuousOn_const.mul hContInd)
  have hContSum :
      ContinuousOn (fun x : ℝ => Real.log x + Real.log c * (if x = 0 then 0 else 1)) (spectrum ℝ A) := by
    simpa using hContLog.add hContScaled
  -- Replace the function inside `cfc` using `EqOn`, then split the sum.
  calc
    cfc (fun x : ℝ => Real.log x) ((c : ℂ) • A)
        = cfc (fun x : ℝ => Real.log (c * x)) A := by
            exact hComp.symm
    _ = cfc (fun x : ℝ =>
            Real.log x + Real.log c * (if x = 0 then 0 else 1)) A := by
          exact cfc_congr (a := A) hEqOn
    _ = cfc (fun x : ℝ => Real.log x) A +
          cfc (fun x : ℝ => Real.log c * (if x = 0 then 0 else 1)) A := by
          -- `cfc_add` requires continuity on the spectrum, which we have from finiteness.
          simpa using
            (cfc_add (a := A)
              (f := fun x : ℝ => Real.log x)
              (g := fun x : ℝ => Real.log c * (if x = 0 then 0 else 1))
              (hf := hContLog) (hg := hContScaled))
    _ = cfc (fun x : ℝ => Real.log x) A +
          (Real.log c : ℂ) • cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) A := by
          -- Pull out the constant `Real.log c` from the second term via `cfc_smul`.
          have hPull :
              cfc (fun x : ℝ => Real.log c * (if x = 0 then 0 else 1)) A =
                (Real.log c : ℂ) • cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) A := by
              have hfun :
                  (fun x : ℝ => Real.log c * (if x = 0 then 0 else 1)) =
                    fun x : ℝ => (Real.log c) • (if x = 0 then (0 : ℝ) else 1) := by
                funext x
                simp [smul_eq_mul]
              calc
                cfc (fun x : ℝ => Real.log c * (if x = 0 then 0 else 1)) A
                    = cfc (fun x : ℝ => (Real.log c) • (if x = 0 then (0 : ℝ) else 1)) A := by
                        exact congrArg (fun f : ℝ → ℝ => cfc f A) hfun
                _ = (Real.log c) • cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) A := by
                      simpa using
                        (cfc_smul (s := Real.log c)
                          (f := fun x : ℝ => if x = 0 then (0 : ℝ) else 1)
                          (a := A) (hf := hContInd))
                _ = (Real.log c : ℂ) • cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) A := by
                      simp
          -- Add the unchanged `cfc (Real.log) A` term on the left.
          exact congrArg (fun M : Mat n => cfc (fun x : ℝ => Real.log x) A + M) hPull

lemma trace_mul_log_smul_supportIndicator {n : ℕ} {ρ A : Mat n}
    (hHerm : A.IsHermitian) (hPos : PosSemidef A)
    {c : ℝ} (hc : 0 < c) :
    Matrix.trace (ρ * cfc (fun x : ℝ => Real.log x) ((c : ℂ) • A)) =
      Matrix.trace (ρ * cfc (fun x : ℝ => Real.log x) A) +
        (Real.log c : ℂ) * Matrix.trace (ρ * cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) A) := by
  classical
  -- Expand using the matrix identity `cfc_log_smul_eq_add_supportIndicator`.
  have h := cfc_log_smul_eq_add_supportIndicator (n := n) (A := A) hHerm hPos (c := c) hc
  -- Multiply on the left by `ρ`, then take traces.
  calc
    Matrix.trace (ρ * cfc (fun x : ℝ => Real.log x) ((c : ℂ) • A)) =
        Matrix.trace (ρ *
          (cfc (fun x : ℝ => Real.log x) A +
            (Real.log c : ℂ) • cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) A)) := by
          simpa [h] using congrArg (fun M => Matrix.trace (ρ * M)) h
    _ = Matrix.trace (ρ * cfc (fun x : ℝ => Real.log x) A) +
          Matrix.trace (ρ * ((Real.log c : ℂ) • cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) A)) := by
          simp [Matrix.mul_add, Matrix.trace_add]
    _ = Matrix.trace (ρ * cfc (fun x : ℝ => Real.log x) A) +
          (Real.log c : ℂ) * Matrix.trace (ρ * cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) A) := by
          -- Pull the scalar out of the trace.
          simp

/-- The support-indicator term acts as the identity after multiplying by `A` on the left. -/
lemma mul_cfc_supportIndicator_eq_self {n : ℕ} {A : Mat n} (hA : A.IsHermitian) :
    A * cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) A = A := by
  classical
  -- View `A` as the `cfc` of the identity function.
  have ha : IsSelfAdjoint A := by
    simpa [Matrix.IsHermitian, IsSelfAdjoint, Matrix.star_eq_conjTranspose] using hA
  have hAid : cfc (fun x : ℝ => x) A = A := by
    simpa using (cfc_id' (R := ℝ) (a := A) ha)
  have hs : (spectrum ℝ A).Finite := Matrix.finite_real_spectrum (A := A)
  have hf : ContinuousOn (fun x : ℝ => x) (spectrum ℝ A) := by
    simpa using (Set.Finite.continuousOn (hs := hs) (f := fun x : ℝ => x))
  have hg : ContinuousOn (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) (spectrum ℝ A) := by
    simpa using
      (Set.Finite.continuousOn (hs := hs)
        (f := fun x : ℝ => if x = 0 then (0 : ℝ) else 1))
  -- Multiply using `cfc_mul` and simplify pointwise.
  have hMul :
      cfc (fun x : ℝ => x) A *
          cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) A =
        cfc (fun x : ℝ => x * (if x = 0 then (0 : ℝ) else 1)) A := by
    simpa using
      (cfc_mul (R := ℝ)
          (f := fun x : ℝ => x)
          (g := fun x : ℝ => if x = 0 then (0 : ℝ) else 1)
          (a := A) (hf := hf) (hg := hg)).symm
  have hEqOn :
      Set.EqOn (fun x : ℝ => x * (if x = 0 then (0 : ℝ) else 1))
        (fun x : ℝ => x) (spectrum ℝ A) := by
    intro x _
    by_cases hx : x = 0 <;> simp [hx]
  have hCong :
      cfc (fun x : ℝ => x * (if x = 0 then (0 : ℝ) else 1)) A =
        cfc (fun x : ℝ => x) A :=
    cfc_congr (a := A) hEqOn
  calc
    A * cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) A =
        cfc (fun x : ℝ => x) A *
          cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) A := by
          simp [hAid]
    _ = cfc (fun x : ℝ => x * (if x = 0 then (0 : ℝ) else 1)) A := hMul
    _ = cfc (fun x : ℝ => x) A := hCong
    _ = A := hAid

/-- Kernel-safe scaling identity: multiplying on the left by `A` kills the kernel issue in
`Real.log 0 = 0`. -/
lemma mul_cfc_log_smul_eq_add {n : ℕ} {A : Mat n}
    (hHerm : A.IsHermitian) (hPos : PosSemidef A)
    {c : ℝ} (hc : 0 < c) :
    A * cfc (fun x : ℝ => Real.log x) ((c : ℂ) • A) =
      A * cfc (fun x : ℝ => Real.log x) A + (Real.log c : ℂ) • A := by
  classical
  have hlog :=
    cfc_log_smul_eq_add_supportIndicator (n := n) (A := A) hHerm hPos (c := c) hc
  -- Multiply by `A` on the left and simplify the support-indicator term.
  calc
    A * cfc (fun x : ℝ => Real.log x) ((c : ℂ) • A) =
        A *
          (cfc (fun x : ℝ => Real.log x) A +
            (Real.log c : ℂ) • cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) A) := by
          simpa [hlog] using congrArg (fun M : Mat n => A * M) hlog
    _ = A * cfc (fun x : ℝ => Real.log x) A +
          A * ((Real.log c : ℂ) • cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) A) := by
          simp [Matrix.mul_add]
    _ = A * cfc (fun x : ℝ => Real.log x) A +
          (Real.log c : ℂ) • (A * cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) A) := by
          simp
    _ = A * cfc (fun x : ℝ => Real.log x) A + (Real.log c : ℂ) • A := by
          simp [mul_cfc_supportIndicator_eq_self (n := n) (A := A) hHerm]

/-- The support-indicator functional calculus term `cfc (if x = 0 then 0 else 1) A` is Hermitian
whenever `A` is Hermitian. -/
lemma cfc_supportIndicator_isHermitian {n : ℕ} {A : Mat n} (_hA : A.IsHermitian) :
    (cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) A).IsHermitian := by
  classical
  -- `cfc` is defined with a junk value when `A` is not self-adjoint; in either case the result is
  -- self-adjoint, hence Hermitian.
  have hSelf :
      IsSelfAdjoint (cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) A) := by
    exact IsSelfAdjoint.cfc (f := fun x : ℝ => if x = 0 then (0 : ℝ) else 1) (a := A)
  -- Convert `IsSelfAdjoint` into the `conjTranspose` equality defining `IsHermitian`.
  have hEq :
      star (cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) A) =
        cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) A := by
    simpa [IsSelfAdjoint] using hSelf
  simpa [Matrix.IsHermitian, Matrix.star_eq_conjTranspose] using hEq

/-- The support-indicator term is idempotent: `P^2 = P`. -/
lemma cfc_supportIndicator_mul_self {n : ℕ} {A : Mat n} :
    cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) A *
        cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) A =
      cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) A := by
  classical
  let f : ℝ → ℝ := fun x : ℝ => if x = 0 then (0 : ℝ) else 1
  have hf : ContinuousOn f (spectrum ℝ A) := by
    simpa [f] using
      (Set.Finite.continuousOn (hs := (Matrix.finite_real_spectrum (A := A))) (f := f))
  have hMul :
      cfc (fun x : ℝ => f x * f x) A = cfc f A * cfc f A := by
    simpa [f] using (cfc_mul (f := f) (g := f) (a := A) (hf := hf) (hg := hf))
  have hEqOn : Set.EqOn (fun x : ℝ => f x * f x) f (spectrum ℝ A) := by
    intro x _
    by_cases hx : x = 0 <;> simp [f, hx]
  -- Use `cfc_mul` followed by pointwise simplification on the spectrum.
  calc
    cfc f A * cfc f A = cfc (fun x : ℝ => f x * f x) A := by
      exact hMul.symm
    _ = cfc f A := by
      exact cfc_congr (a := A) hEqOn

/-- For PSD `ρ`, the support-indicator term has trace at most `trace ρ` when multiplied on the
right.  In particular, for a density matrix this trace is at most `1`. -/
lemma trace_mul_cfc_supportIndicator_re_le_trace {n : ℕ} {ρ A : Mat n}
    (hρ : PosSemidef ρ) (hA : A.IsHermitian) :
    (Matrix.trace (ρ * cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) A)).re ≤
      (Matrix.trace ρ).re := by
  classical
  set P : Mat n := cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) A
  have hPherm : P.IsHermitian := by
    simpa [P] using cfc_supportIndicator_isHermitian (n := n) (A := A) hA
  have hPid : P * P = P := by
    simpa [P] using (cfc_supportIndicator_mul_self (n := n) (A := A))
  set W : Mat n := 1 - P
  have hWherm : W.IsHermitian := by
    simpa [W] using (Matrix.isHermitian_one (n := Fin n) (α := ℂ)).sub hPherm
  have hWid : W * W = W := by
    -- Expand `(1 - P)^2` using `P^2 = P`.
    simp [W, sub_eq_add_neg, Matrix.mul_add, Matrix.add_mul, hPid]
  have hWstar : star W = W := by
    -- `IsHermitian` is `Wᴴ = W`, and `star = conjTranspose`.
    simpa [Matrix.IsHermitian] using hWherm
  have hWstarW : star W * W = W := by
    simp [hWstar, hWid]
  have hTraceW_nonneg : 0 ≤ (Matrix.trace (ρ * W)).re := by
    -- Rewrite `trace (ρ * W)` as the trace of a conjugated PSD matrix.
    have hCycle :
        Matrix.trace (ρ * star W * W) = Matrix.trace (W * ρ * star W) := by
      simpa [Matrix.mul_assoc] using
        (Matrix.trace_mul_cycle (A := ρ) (B := star W) (C := W))
    have hRewrite :
        Matrix.trace (ρ * W) = Matrix.trace (W * ρ * star W) := by
      calc
        Matrix.trace (ρ * W)
            = Matrix.trace (ρ * (star W * W)) := by
                simp [hWstarW]
        _ = Matrix.trace (ρ * star W * W) := by
              simp [Matrix.mul_assoc]
        _ = Matrix.trace (W * ρ * star W) := hCycle
    have hPos : PosSemidef (W * ρ * star W) := by
      -- `PosSemidef` is preserved by conjugation.
      simpa [W, Matrix.mul_assoc] using
        (PosSemidef.conj_mul (A := ρ) hρ (V := W))
    have hPosTrace : 0 ≤ (Matrix.trace (W * ρ * star W)).re :=
      PosSemidef.trace_real_nonneg (ι := Fin n) (A := W * ρ * star W) hPos
    simpa [hRewrite] using hPosTrace
  -- Split `trace ρ` into the `P` and `W = 1 - P` contributions.
  have hsplit :
      Matrix.trace ρ = Matrix.trace (ρ * P) + Matrix.trace (ρ * W) := by
    calc
      Matrix.trace ρ = Matrix.trace (ρ * (P + W)) := by
          simp [W, sub_eq_add_neg, add_left_comm, add_comm]
      _ = Matrix.trace (ρ * P + ρ * W) := by
          simp [Matrix.mul_add]
      _ = Matrix.trace (ρ * P) + Matrix.trace (ρ * W) := by
          simp [Matrix.trace_add]
  have hsplit_re :
      (Matrix.trace ρ).re = (Matrix.trace (ρ * P)).re + (Matrix.trace (ρ * W)).re := by
    simpa [map_add] using congrArg Complex.re hsplit
  have hEq :
      (Matrix.trace (ρ * P)).re = (Matrix.trace ρ).re - (Matrix.trace (ρ * W)).re := by
    linarith
  exact
    (le_of_eq_of_le hEq (sub_le_self _ hTraceW_nonneg)).trans_eq (by rfl)

namespace ActiveInference

open Matrix
open scoped Matrix

variable {m k : ℕ}

/-
Isometry invariance for the spectral logarithm / relative entropy.

The Stinespring dilation used in the CPTP story extends an input density by an
isometry `V`.  Because `Real.log 0 = 0` in our conventions, the spectral
logarithm commutes with this extension without requiring full-rank hypotheses,
and `qRelEnt` is invariant under the same embedding.
-/

/-- Conjugation by an isometry, viewed as a non-unital `*`-algebra homomorphism. -/
private def isometryConjHom (V : Matrix (Fin m) (Fin k) ℂ) (hV : IsometryMatrix V) :
    Matrix (Fin k) (Fin k) ℂ →⋆ₙₐ[ℂ] Matrix (Fin m) (Fin m) ℂ := by
  classical
  refine NonUnitalStarAlgHom.mk ?_ ?_
  ·
    refine
      { toFun := fun A => V * A * V.conjTranspose
        map_smul' := ?_
        map_zero' := by simp
        map_add' := by
          intro A B
          simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
        map_mul' := ?_ }
    · intro c A
      simp [Matrix.mul_assoc]
    · intro A B
      have hVV : V.conjTranspose * V = 1 := by
        simpa [IsometryMatrix] using hV
      calc
        V * (A * B) * V.conjTranspose
            = V * A * B * V.conjTranspose := by simp [Matrix.mul_assoc]
        _ = V * A * (V.conjTranspose * V) * B * V.conjTranspose := by
              simp [Matrix.mul_assoc, hVV]
        _ = (V * A * V.conjTranspose) * (V * B * V.conjTranspose) := by
              simp [Matrix.mul_assoc]
  · intro A
    simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.mul_assoc]

private lemma isometryConjHom_map_cfc_log
    (V : Matrix (Fin m) (Fin k) ℂ) (hV : IsometryMatrix V)
    (A : Matrix (Fin k) (Fin k) ℂ) (hA : A.IsHermitian) :
    isometryConjHom (m:=m) (k:=k) V hV (cfc (fun x : ℝ => Real.log x) A) =
      cfc (fun x : ℝ => Real.log x) (isometryConjHom (m:=m) (k:=k) V hV A) := by
  classical
  let φ : Matrix (Fin k) (Fin k) ℂ →⋆ₙₐ[ℂ] Matrix (Fin m) (Fin m) ℂ :=
    isometryConjHom (m:=m) (k:=k) V hV
  have hs_spec : (spectrum ℝ A).Finite := Matrix.finite_real_spectrum (A := A)
  have hs : (quasispectrum ℝ A).Finite := by
    simpa [quasispectrum_eq_spectrum_union_zero] using hs_spec.union (Set.finite_singleton 0)
  have hf : ContinuousOn (fun x : ℝ => Real.log x) (quasispectrum ℝ A) := by
    simpa using (Set.Finite.continuousOn hs (fun x : ℝ => Real.log x))
  have hf0 : (fun x : ℝ => Real.log x) 0 = 0 := by simp
  have ha : IsSelfAdjoint A := by
    simpa [Matrix.IsHermitian, IsSelfAdjoint, Matrix.star_eq_conjTranspose] using hA
  have hφa : IsSelfAdjoint (φ A) := by
    have hstar : φ (star A) = star (φ A) := φ.map_star' A
    have hstarA : star A = A := ha
    calc
      star (φ A) = φ (star A) := by simpa using hstar.symm
      _ = φ A := by simp [hstarA]
  have hLeft : Continuous (fun _ : Matrix (Fin k) (Fin k) ℂ => (V : Matrix (Fin m) (Fin k) ℂ)) :=
    continuous_const
  have hId : Continuous (fun A : Matrix (Fin k) (Fin k) ℂ => A) := continuous_id
  have hMulLeft :
      Continuous (fun A : Matrix (Fin k) (Fin k) ℂ => (V : Matrix (Fin m) (Fin k) ℂ) * A) :=
    hLeft.matrix_mul hId
  have hRight :
      Continuous (fun _ : Matrix (Fin k) (Fin k) ℂ => (V.conjTranspose : Matrix (Fin k) (Fin m) ℂ)) :=
    continuous_const
  have hcont :
      Continuous (fun A : Matrix (Fin k) (Fin k) ℂ => ((V : Matrix (Fin m) (Fin k) ℂ) * A) * V.conjTranspose) :=
    hMulLeft.matrix_mul hRight
  have hcont' : Continuous (fun A : Matrix (Fin k) (Fin k) ℂ => φ A) := by
    simpa [φ, isometryConjHom, Matrix.mul_assoc] using hcont
  have h_eq1 : cfcₙ (fun x : ℝ => Real.log x) A = cfc (fun x : ℝ => Real.log x) A :=
    cfcₙ_eq_cfc (f := fun x : ℝ => Real.log x) (a := A) (hf := hf) (hf0 := hf0)
  have hs_spec' : (spectrum ℝ (φ A)).Finite := Matrix.finite_real_spectrum (A := φ A)
  have hs' : (quasispectrum ℝ (φ A)).Finite := by
    simpa [quasispectrum_eq_spectrum_union_zero] using hs_spec'.union (Set.finite_singleton 0)
  have hf' : ContinuousOn (fun x : ℝ => Real.log x) (quasispectrum ℝ (φ A)) := by
    simpa using (Set.Finite.continuousOn hs' (fun x : ℝ => Real.log x))
  have h_eq2 :
      cfcₙ (fun x : ℝ => Real.log x) (φ A) =
        cfc (fun x : ℝ => Real.log x) (φ A) :=
    cfcₙ_eq_cfc (f := fun x : ℝ => Real.log x) (a := φ A) (hf := hf') (hf0 := hf0)
  have hmapₙ :
      φ (cfcₙ (fun x : ℝ => Real.log x) A) =
        cfcₙ (fun x : ℝ => Real.log x) (φ A) := by
    simpa using
      (NonUnitalStarAlgHom.map_cfcₙ (R := ℝ) (S := ℂ) (φ := φ)
        (f := fun x : ℝ => Real.log x) (a := A)
        (hf := hf) (hf₀ := hf0) (hφ := hcont') (ha := ha) (hφa := hφa))
  calc
    φ (cfc (fun x : ℝ => Real.log x) A)
        = φ (cfcₙ (fun x : ℝ => Real.log x) A) := by
            simp [h_eq1]
    _ = cfcₙ (fun x : ℝ => Real.log x) (φ A) := hmapₙ
    _ = cfc (fun x : ℝ => Real.log x) (φ A) := by
            simp [h_eq2]

lemma matrixLogDensity_isometryExtendDensity
    (V : Matrix (Fin m) (Fin k) ℂ) (hV : IsometryMatrix V) (ρ : Density k) :
    matrixLogDensity (isometryExtendDensity V hV ρ) =
      V * matrixLogDensity ρ * V.conjTranspose := by
  classical
  let ρ' : Density m := isometryExtendDensity V hV ρ
  have hρ' : matrixLogDensity ρ' = cfc (fun x : ℝ => Real.log x) ρ'.mat := by
    simp [matrixLogDensity, Matrix.IsHermitian.cfc_eq]
  have hρ : matrixLogDensity ρ = cfc (fun x : ℝ => Real.log x) ρ.mat := by
    simp [matrixLogDensity, Matrix.IsHermitian.cfc_eq]
  have hmap :=
    (isometryConjHom_map_cfc_log (m:=m) (k:=k) V hV ρ.mat ρ.mat_isHermitian).symm
  calc
    matrixLogDensity ρ' = cfc (fun x : ℝ => Real.log x) ρ'.mat := hρ'
    _ = V * cfc (fun x : ℝ => Real.log x) ρ.mat * V.conjTranspose := by
          simpa [ρ', isometryExtendDensity, isometryConjHom, Matrix.mul_assoc] using hmap
    _ = V * matrixLogDensity ρ * V.conjTranspose := by
          simp [hρ, Matrix.mul_assoc]

lemma qRelEnt_isometryExtendDensity
    (V : Matrix (Fin m) (Fin k) ℂ) (hV : IsometryMatrix V) (ρ σ : Density k) :
    qRelEnt (isometryExtendDensity V hV ρ) (isometryExtendDensity V hV σ) =
      qRelEnt ρ σ := by
  classical
  let ρ' : Density m := isometryExtendDensity V hV ρ
  let σ' : Density m := isometryExtendDensity V hV σ
  have hV' : V.conjTranspose * V = 1 := by
    simpa [IsometryMatrix] using hV
  have hLogρ : matrixLogDensity ρ' = V * matrixLogDensity ρ * V.conjTranspose := by
    simpa [ρ'] using matrixLogDensity_isometryExtendDensity (m:=m) (k:=k) V hV ρ
  have hLogσ : matrixLogDensity σ' = V * matrixLogDensity σ * V.conjTranspose := by
    simpa [σ'] using matrixLogDensity_isometryExtendDensity (m:=m) (k:=k) V hV σ
  have hSelf :
      Matrix.trace (ρ'.mat * matrixLogDensity ρ') =
        Matrix.trace (ρ.mat * matrixLogDensity ρ) := by
    calc
      Matrix.trace (ρ'.mat * matrixLogDensity ρ') =
          Matrix.trace (ρ'.mat * (V * matrixLogDensity ρ * V.conjTranspose)) := by
            rw [hLogρ]
      _ =
          Matrix.trace ((V * ρ.mat * V.conjTranspose) *
            (V * matrixLogDensity ρ * V.conjTranspose)) := by
            simp [ρ', isometryExtendDensity]
      _ =
          Matrix.trace (V * ρ.mat * (V.conjTranspose * V) *
            matrixLogDensity ρ * V.conjTranspose) := by
            simp [Matrix.mul_assoc]
      _ = Matrix.trace (V * ρ.mat * matrixLogDensity ρ * V.conjTranspose) := by
            simp [hV', Matrix.mul_assoc]
      _ = Matrix.trace ((V * (ρ.mat * matrixLogDensity ρ)) * V.conjTranspose) := by
            simp [Matrix.mul_assoc]
      _ =
          Matrix.trace (V.conjTranspose *
            (V * (ρ.mat * matrixLogDensity ρ))) := by
            simpa using
              (Matrix.trace_mul_comm (A := V * (ρ.mat * matrixLogDensity ρ))
                (B := V.conjTranspose))
      _ = Matrix.trace ((V.conjTranspose * V) * (ρ.mat * matrixLogDensity ρ)) := by
            simp [Matrix.mul_assoc]
      _ = Matrix.trace (ρ.mat * matrixLogDensity ρ) := by
            simp [hV']
  have hCross :
      Matrix.trace (ρ'.mat * matrixLogDensity σ') =
        Matrix.trace (ρ.mat * matrixLogDensity σ) := by
    calc
      Matrix.trace (ρ'.mat * matrixLogDensity σ') =
          Matrix.trace (ρ'.mat * (V * matrixLogDensity σ * V.conjTranspose)) := by
            rw [hLogσ]
      _ =
          Matrix.trace ((V * ρ.mat * V.conjTranspose) *
            (V * matrixLogDensity σ * V.conjTranspose)) := by
            simp [ρ', isometryExtendDensity]
      _ =
          Matrix.trace (V * ρ.mat * (V.conjTranspose * V) *
            matrixLogDensity σ * V.conjTranspose) := by
            simp [Matrix.mul_assoc]
      _ = Matrix.trace (V * ρ.mat * matrixLogDensity σ * V.conjTranspose) := by
            simp [hV', Matrix.mul_assoc]
      _ = Matrix.trace ((V * (ρ.mat * matrixLogDensity σ)) * V.conjTranspose) := by
            simp [Matrix.mul_assoc]
      _ =
          Matrix.trace (V.conjTranspose *
            (V * (ρ.mat * matrixLogDensity σ))) := by
            simpa using
              (Matrix.trace_mul_comm (A := V * (ρ.mat * matrixLogDensity σ))
                (B := V.conjTranspose))
      _ = Matrix.trace ((V.conjTranspose * V) * (ρ.mat * matrixLogDensity σ)) := by
            simp [Matrix.mul_assoc]
      _ = Matrix.trace (ρ.mat * matrixLogDensity σ) := by
            simp [hV']
  have htrace :
      Matrix.trace (ρ'.mat * (matrixLogDensity ρ' - matrixLogDensity σ')) =
        Matrix.trace (ρ.mat * (matrixLogDensity ρ - matrixLogDensity σ)) := by
    calc
      Matrix.trace (ρ'.mat * (matrixLogDensity ρ' - matrixLogDensity σ')) =
          Matrix.trace (ρ'.mat * matrixLogDensity ρ' - ρ'.mat * matrixLogDensity σ') := by
            simp [Matrix.mul_sub]
      _ =
          Matrix.trace (ρ'.mat * matrixLogDensity ρ') -
            Matrix.trace (ρ'.mat * matrixLogDensity σ') := by
            simp [Matrix.trace_sub]
      _ =
          Matrix.trace (ρ.mat * matrixLogDensity ρ) -
            Matrix.trace (ρ.mat * matrixLogDensity σ) := by
            simp [hSelf, hCross]
      _ = Matrix.trace (ρ.mat * (matrixLogDensity ρ - matrixLogDensity σ)) := by
            simp [Matrix.mul_sub, Matrix.trace_sub]
  simp [qRelEnt, ρ', σ', htrace]

lemma trace_ancillaBlock_mul_log_eq_weighted
    (ρ : Density (m * k)) (l : Fin k) :
    Matrix.trace
        (ancillaBlock (m:=m) (k:=k)
              (ancillaMatrix (m:=m) (k:=k) ρ) l *
            cfc (fun x : ℝ => Real.log x)
              ((ancillaWeight (m:=m) (k:=k) ρ l : ℂ) •
                (ancillaBlockDensity (m:=m) (k:=k) ρ l).mat)) =
      (ancillaWeight (m:=m) (k:=k) ρ l : ℂ) *
          Matrix.trace
            ((ancillaBlockDensity (m:=m) (k:=k) ρ l).mat *
              cfc (fun x : ℝ => Real.log x)
                (ancillaBlockDensity (m:=m) (k:=k) ρ l).mat) +
        (Real.log (ancillaWeight (m:=m) (k:=k) ρ l) : ℂ) *
          ((ancillaWeight (m:=m) (k:=k) ρ l : ℂ) *
            Matrix.trace (ancillaBlockDensity (m:=m) (k:=k) ρ l).mat) := by
  classical
  set w : ℝ := ancillaWeight (m:=m) (k:=k) ρ l
  set ρHat : Density m := ancillaBlockDensity (m:=m) (k:=k) ρ l
  have hBlock : (w : ℂ) • ρHat.mat = ancillaBlock (m:=m) (k:=k) (ancillaMatrix (m:=m) (k:=k) ρ) l := by
    simpa [w, ρHat] using ancillaBlock_weight_smul_density (m:=m) (k:=k) ρ l
  by_cases hw : w = 0
  ·
    -- Degenerate case: the block has zero trace weight.
    simp [hw, w, ρHat]
  ·
    have hw_pos : 0 < w :=
      lt_of_le_of_ne' (ancillaWeight_nonneg (m:=m) (k:=k) ρ l) hw
    have htrace :=
      trace_smul_mul_log_smul (n := m) (A := ρHat.mat)
        (hHerm := ρHat.mat_isHermitian) (hPos := ρHat.posSemidef)
        (c := w) hw_pos
    -- Rewrite `ancillaBlock` as `w • ρHat.mat` and match the statement.
    simpa [w, ρHat, hBlock, Matrix.mul_assoc] using htrace

lemma trace_ancillaBlock_mul_log_weighted_support
    (ρ σ : Density (m * k)) (l : Fin k)
    (hv : 0 < ancillaWeight (m:=m) (k:=k) σ l) :
    Matrix.trace
        (ancillaBlock (m:=m) (k:=k)
              (ancillaMatrix (m:=m) (k:=k) ρ) l *
            cfc (fun x : ℝ => Real.log x)
              ((ancillaWeight (m:=m) (k:=k) σ l : ℂ) •
                (ancillaBlockDensity (m:=m) (k:=k) σ l).mat)) =
      (ancillaWeight (m:=m) (k:=k) ρ l : ℂ) *
          Matrix.trace
            ((ancillaBlockDensity (m:=m) (k:=k) ρ l).mat *
              cfc (fun x : ℝ => Real.log x)
                (ancillaBlockDensity (m:=m) (k:=k) σ l).mat) +
        (Real.log (ancillaWeight (m:=m) (k:=k) σ l) : ℂ) *
          ((ancillaWeight (m:=m) (k:=k) ρ l : ℂ) *
            Matrix.trace
              ((ancillaBlockDensity (m:=m) (k:=k) ρ l).mat *
                cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1)
                  (ancillaBlockDensity (m:=m) (k:=k) σ l).mat)) := by
  classical
  set w : ℝ := ancillaWeight (m:=m) (k:=k) ρ l
  set v : ℝ := ancillaWeight (m:=m) (k:=k) σ l
  set ρHat : Density m := ancillaBlockDensity (m:=m) (k:=k) ρ l
  set σHat : Density m := ancillaBlockDensity (m:=m) (k:=k) σ l
  have hρBlock : (w : ℂ) • ρHat.mat = ancillaBlock (m:=m) (k:=k) (ancillaMatrix (m:=m) (k:=k) ρ) l := by
    simpa [w, ρHat] using ancillaBlock_weight_smul_density (m:=m) (k:=k) ρ l
  have htrace :=
    trace_mul_log_smul_supportIndicator (n := m)
      (ρ := ρHat.mat) (A := σHat.mat)
      (hHerm := σHat.mat_isHermitian) (hPos := σHat.posSemidef)
      (c := v) (hc := by simpa [v] using hv)
  have hscale :
      Matrix.trace (((w : ℂ) • ρHat.mat) * cfc (fun x : ℝ => Real.log x) ((v : ℂ) • σHat.mat)) =
        (w : ℂ) * Matrix.trace (ρHat.mat * cfc (fun x : ℝ => Real.log x) ((v : ℂ) • σHat.mat)) := by
    calc
      Matrix.trace (((w : ℂ) • ρHat.mat) * cfc (fun x : ℝ => Real.log x) ((v : ℂ) • σHat.mat)) =
      Matrix.trace ((w : ℂ) • (ρHat.mat * cfc (fun x : ℝ => Real.log x) ((v : ℂ) • σHat.mat))) := by
            simp
      _ = (w : ℂ) * Matrix.trace (ρHat.mat * cfc (fun x : ℝ => Real.log x) ((v : ℂ) • σHat.mat)) := by
            simp [Matrix.trace_smul]
  calc
    Matrix.trace
        (ancillaBlock (m:=m) (k:=k)
              (ancillaMatrix (m:=m) (k:=k) ρ) l *
            cfc (fun x : ℝ => Real.log x) ((v : ℂ) • σHat.mat)) =
        Matrix.trace (((w : ℂ) • ρHat.mat) * cfc (fun x : ℝ => Real.log x) ((v : ℂ) • σHat.mat)) := by
          simp [hρBlock]
    _ = (w : ℂ) * Matrix.trace (ρHat.mat * cfc (fun x : ℝ => Real.log x) ((v : ℂ) • σHat.mat)) := hscale
    _ = (w : ℂ) *
          (Matrix.trace (ρHat.mat * cfc (fun x : ℝ => Real.log x) σHat.mat) +
            (Real.log v : ℂ) * Matrix.trace (ρHat.mat *
              cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) σHat.mat)) := by
          exact congrArg (fun z => (w : ℂ) * z) htrace
    _ = (w : ℂ) * Matrix.trace (ρHat.mat * cfc (fun x : ℝ => Real.log x) σHat.mat) +
          (Real.log v : ℂ) * ((w : ℂ) * Matrix.trace (ρHat.mat *
              cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) σHat.mat)) := by
          ring
    _ = (ancillaWeight (m:=m) (k:=k) ρ l : ℂ) *
          Matrix.trace
            ((ancillaBlockDensity (m:=m) (k:=k) ρ l).mat *
              cfc (fun x : ℝ => Real.log x)
                (ancillaBlockDensity (m:=m) (k:=k) σ l).mat) +
        (Real.log (ancillaWeight (m:=m) (k:=k) σ l) : ℂ) *
          ((ancillaWeight (m:=m) (k:=k) ρ l : ℂ) *
            Matrix.trace
              ((ancillaBlockDensity (m:=m) (k:=k) ρ l).mat *
                cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1)
                  (ancillaBlockDensity (m:=m) (k:=k) σ l).mat)) := by
          simp [w, v, ρHat, σHat]

lemma qRelEnt_pinchAncilla_decompose_pinch_weighted_support
    (ρ σ : Density (m * k))
    (hv : ∀ l : Fin k, 0 < ancillaWeight (m:=m) (k:=k) σ l) :
    qRelEnt
        (pinchAncillaDensity (m:=m) (k:=k) ρ)
        (pinchAncillaDensity (m:=m) (k:=k) σ) =
      ∑ l : Fin k,
        (ancillaWeight (m:=m) (k:=k) ρ l *
              qRelEnt (ancillaBlockDensity (m:=m) (k:=k) ρ l)
                      (ancillaBlockDensity (m:=m) (k:=k) σ l) +
            ancillaWeight (m:=m) (k:=k) ρ l *
                Real.log (ancillaWeight (m:=m) (k:=k) ρ l) -
              Real.log (ancillaWeight (m:=m) (k:=k) σ l) *
                (ancillaWeight (m:=m) (k:=k) ρ l *
                  (Matrix.trace
                    ((ancillaBlockDensity (m:=m) (k:=k) ρ l).mat *
                      cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1)
                        (ancillaBlockDensity (m:=m) (k:=k) σ l).mat)).re)) := by
  classical
  -- Start from the block decomposition of `qRelEnt` for pinched densities.
  have hdecomp :=
    Matrix.qRelEnt_pinchAncilla_decompose_pinch (m:=m) (k:=k) (ρ := ρ) (σ := σ)
  rw [hdecomp]
  -- Rewrite the difference of sums into a sum of per-block differences.
  let selfTerm : Fin k → ℝ := fun l : Fin k =>
    (Matrix.trace
        (ancillaBlock (m:=m) (k:=k)
              (Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                (finProdFinEquiv (m:=m) (n:=k)).symm ρ.mat) l *
            ((ancillaBlock_isHermitian
                  (A :=
                    Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                      (finProdFinEquiv (m:=m) (n:=k)).symm ρ.mat)
                  (hA :=
                    Matrix.reindex_isHermitian
                      (A := ρ.mat) ρ.mat_isHermitian
                      (finProdFinEquiv (m:=m) (n:=k)).symm) l).cfc
              (A :=
                ancillaBlock (m:=m) (k:=k)
                  (Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                    (finProdFinEquiv (m:=m) (n:=k)).symm ρ.mat) l)
              (fun x : ℝ => Real.log x)))).re
  let crossTerm : Fin k → ℝ := fun l : Fin k =>
    (Matrix.trace
        (ancillaBlock (m:=m) (k:=k)
              (Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                (finProdFinEquiv (m:=m) (n:=k)).symm ρ.mat) l *
            ((ancillaBlock_isHermitian
                  (A :=
                    Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                      (finProdFinEquiv (m:=m) (n:=k)).symm σ.mat)
                  (hA :=
                    Matrix.reindex_isHermitian
                      (A := σ.mat) σ.mat_isHermitian
                      (finProdFinEquiv (m:=m) (n:=k)).symm) l).cfc
              (A :=
                ancillaBlock (m:=m) (k:=k)
                  (Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                    (finProdFinEquiv (m:=m) (n:=k)).symm σ.mat) l)
              (fun x : ℝ => Real.log x)))).re
  have hsum :
      (∑ l : Fin k, selfTerm l) - ∑ l : Fin k, crossTerm l =
        ∑ l : Fin k, (selfTerm l - crossTerm l) := by
    exact
      (Finset.sum_sub_distrib
          (s := (Finset.univ : Finset (Fin k)))
          (f := selfTerm) (g := crossTerm)).symm
  -- Replace the LHS with the sum of per-block differences.
  rw [hsum]
  -- Now prove equality termwise.
  -- Help typeclass inference by naming the RHS summand as an `ℝ`-valued function.
  let rhsSummand : Fin k → ℝ := fun l : Fin k =>
    ancillaWeight (m:=m) (k:=k) ρ l *
        qRelEnt (ancillaBlockDensity (m:=m) (k:=k) ρ l)
                (ancillaBlockDensity (m:=m) (k:=k) σ l) +
      ancillaWeight (m:=m) (k:=k) ρ l *
          Real.log (ancillaWeight (m:=m) (k:=k) ρ l) -
        Real.log (ancillaWeight (m:=m) (k:=k) σ l) *
          (ancillaWeight (m:=m) (k:=k) ρ l *
            (Matrix.trace
              ((ancillaBlockDensity (m:=m) (k:=k) ρ l).mat *
                cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1)
                  (ancillaBlockDensity (m:=m) (k:=k) σ l).mat)).re)
  have hRhs :
      (∑ l : Fin k, rhsSummand l) =
        ∑ l : Fin k,
          (ancillaWeight (m:=m) (k:=k) ρ l *
                qRelEnt (ancillaBlockDensity (m:=m) (k:=k) ρ l)
                        (ancillaBlockDensity (m:=m) (k:=k) σ l) +
              ancillaWeight (m:=m) (k:=k) ρ l *
                  Real.log (ancillaWeight (m:=m) (k:=k) ρ l) -
                Real.log (ancillaWeight (m:=m) (k:=k) σ l) *
                  (ancillaWeight (m:=m) (k:=k) ρ l *
                    (Matrix.trace
                      ((ancillaBlockDensity (m:=m) (k:=k) ρ l).mat *
                        cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1)
                          (ancillaBlockDensity (m:=m) (k:=k) σ l).mat)).re)) := by
    rfl
  -- Rewrite the RHS as a sum of the named `rhsSummand`.
  rw [← hRhs]
  refine Finset.sum_congr rfl ?_
  intro l _
  -- Shorthand for weights and normalized blocks.
  set w : ℝ := ancillaWeight (m:=m) (k:=k) ρ l
  set v : ℝ := ancillaWeight (m:=m) (k:=k) σ l
  set ρHat : Density m := ancillaBlockDensity (m:=m) (k:=k) ρ l
  set σHat : Density m := ancillaBlockDensity (m:=m) (k:=k) σ l
  -- Rewrite the two trace terms using the per-block trace identities.
  have hSelf :
      (Matrix.trace
            (ancillaBlock (m:=m) (k:=k)
                  (ancillaMatrix (m:=m) (k:=k) ρ) l *
                cfc (fun x : ℝ => Real.log x)
                  ((w : ℂ) • ρHat.mat))).re =
        w *
            (Matrix.trace (ρHat.mat * cfc (fun x : ℝ => Real.log x) ρHat.mat)).re +
          Real.log w * w := by
    have h := congrArg Complex.re
      (trace_ancillaBlock_mul_log_eq_weighted (m:=m) (k:=k) ρ l)
    simpa [w, ρHat, Complex.mul_re, (ρHat.traceOne), mul_assoc, mul_left_comm, mul_comm] using h
  have hCross :
      (Matrix.trace
            (ancillaBlock (m:=m) (k:=k)
                  (ancillaMatrix (m:=m) (k:=k) ρ) l *
                cfc (fun x : ℝ => Real.log x)
                  ((v : ℂ) • σHat.mat))).re =
        w *
            (Matrix.trace (ρHat.mat * cfc (fun x : ℝ => Real.log x) σHat.mat)).re +
          Real.log v *
            (w *
              (Matrix.trace
                (ρHat.mat *
                  cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) σHat.mat)).re) := by
    have h := congrArg Complex.re
      (trace_ancillaBlock_mul_log_weighted_support (m:=m) (k:=k) (ρ := ρ) (σ := σ) l
        (by simpa [v] using hv l))
    simpa [w, v, ρHat, σHat, Complex.mul_re, mul_assoc, mul_left_comm, mul_comm] using h
  -- Combine the two identities and rewrite the trace difference as `qRelEnt` on the normalized blocks.
  have hqRel :
      qRelEnt ρHat σHat =
        (Matrix.trace (ρHat.mat * cfc (fun x : ℝ => Real.log x) ρHat.mat)).re -
          (Matrix.trace (ρHat.mat * cfc (fun x : ℝ => Real.log x) σHat.mat)).re := by
    -- Expand `qRelEnt` and `matrixLogDensity` into `cfc` form.
    simp [qRelEnt, matrixLogDensity, Matrix.trace_sub, Matrix.mul_sub, Complex.sub_re,
      Matrix.IsHermitian.cfc_eq, ρHat, σHat]
  -- Finish by algebra.
  -- Note: the RHS in the statement uses `ancillaWeight`/`ancillaBlockDensity`, so we `simp` them back at the end.
  calc
    selfTerm l - crossTerm l =
        (Matrix.trace
            (ancillaBlock (m:=m) (k:=k)
                  (ancillaMatrix (m:=m) (k:=k) ρ) l *
                cfc (fun x : ℝ => Real.log x)
                  ((w : ℂ) • ρHat.mat))).re -
          (Matrix.trace
            (ancillaBlock (m:=m) (k:=k)
                  (ancillaMatrix (m:=m) (k:=k) ρ) l *
                cfc (fun x : ℝ => Real.log x)
                  ((v : ℂ) • σHat.mat))).re := by
          -- Convert the raw `.cfc` terms from the pinching decomposition into `cfc` on the
          -- weight-scaled normalized blocks.
          have hSelfConv :
              selfTerm l =
                (Matrix.trace
                  (ancillaBlock (m:=m) (k:=k) (ancillaMatrix (m:=m) (k:=k) ρ) l *
                    cfc (fun x : ℝ => Real.log x)
                      ((ancillaWeight (m:=m) (k:=k) ρ l : ℂ) •
                        (ancillaBlockDensity (m:=m) (k:=k) ρ l).mat))).re := by
            have hBlockHerm :=
              (ancillaBlock_isHermitian
                (A :=
                  Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                    (finProdFinEquiv (m:=m) (n:=k)).symm ρ.mat)
                (hA :=
                  Matrix.reindex_isHermitian
                    (A := ρ.mat) ρ.mat_isHermitian
                    (finProdFinEquiv (m:=m) (n:=k)).symm) l)
            have hcfc :
                hBlockHerm.cfc
                    (A :=
                      ancillaBlock (m:=m) (k:=k)
                        (Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                          (finProdFinEquiv (m:=m) (n:=k)).symm ρ.mat) l)
                    (fun x : ℝ => Real.log x) =
                  cfc (fun x : ℝ => Real.log x)
                    (ancillaBlock (m:=m) (k:=k)
                      (Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                        (finProdFinEquiv (m:=m) (n:=k)).symm ρ.mat) l) := by
              simpa using
                (Matrix.IsHermitian.cfc_eq hBlockHerm (fun x : ℝ => Real.log x)).symm
            have hBlock :
                ((ancillaWeight (m:=m) (k:=k) ρ l : ℂ) •
                    (ancillaBlockDensity (m:=m) (k:=k) ρ l).mat) =
                  ancillaBlock (m:=m) (k:=k)
                      (ancillaMatrix (m:=m) (k:=k) ρ) l := by
              simpa [ActiveInference.ancillaMatrix] using
                (ancillaBlock_weight_smul_density (m:=m) (k:=k) ρ l)
            simp [selfTerm, ActiveInference.ancillaMatrix, Matrix.reindex_apply, hcfc, hBlock]
          have hCrossConv :
              crossTerm l =
                (Matrix.trace
                  (ancillaBlock (m:=m) (k:=k) (ancillaMatrix (m:=m) (k:=k) ρ) l *
                    cfc (fun x : ℝ => Real.log x)
                      ((ancillaWeight (m:=m) (k:=k) σ l : ℂ) •
                        (ancillaBlockDensity (m:=m) (k:=k) σ l).mat))).re := by
            have hBlockHerm :=
              (ancillaBlock_isHermitian
                (A :=
                  Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                    (finProdFinEquiv (m:=m) (n:=k)).symm σ.mat)
                (hA :=
                  Matrix.reindex_isHermitian
                    (A := σ.mat) σ.mat_isHermitian
                    (finProdFinEquiv (m:=m) (n:=k)).symm) l)
            have hcfc :
                hBlockHerm.cfc
                    (A :=
                      ancillaBlock (m:=m) (k:=k)
                        (Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                          (finProdFinEquiv (m:=m) (n:=k)).symm σ.mat) l)
                    (fun x : ℝ => Real.log x) =
                  cfc (fun x : ℝ => Real.log x)
                    (ancillaBlock (m:=m) (k:=k)
                      (Matrix.reindex (finProdFinEquiv (m:=m) (n:=k)).symm
                        (finProdFinEquiv (m:=m) (n:=k)).symm σ.mat) l) := by
              simpa using
                (Matrix.IsHermitian.cfc_eq hBlockHerm (fun x : ℝ => Real.log x)).symm
            have hBlock :
                ((ancillaWeight (m:=m) (k:=k) σ l : ℂ) •
                    (ancillaBlockDensity (m:=m) (k:=k) σ l).mat) =
                  ancillaBlock (m:=m) (k:=k)
                      (ancillaMatrix (m:=m) (k:=k) σ) l := by
              simpa [ActiveInference.ancillaMatrix] using
                (ancillaBlock_weight_smul_density (m:=m) (k:=k) σ l)
            simp [crossTerm, ActiveInference.ancillaMatrix, Matrix.reindex_apply, hcfc, hBlock]
          -- Apply the shorthands `w,v,ρHat,σHat`.
          simp [hSelfConv, hCrossConv, w, v, ρHat, σHat]
    _ =
        (w *
              (Matrix.trace (ρHat.mat * cfc (fun x : ℝ => Real.log x) ρHat.mat)).re +
            Real.log w * w) -
          (w *
              (Matrix.trace (ρHat.mat * cfc (fun x : ℝ => Real.log x) σHat.mat)).re +
            Real.log v *
              (w *
                (Matrix.trace
                  (ρHat.mat *
                    cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) σHat.mat)).re)) := by
          -- Rewrite each trace term using the per-block identities.
          rw [hSelf, hCross]
    _ =
        w *
            ((Matrix.trace (ρHat.mat * cfc (fun x : ℝ => Real.log x) ρHat.mat)).re -
              (Matrix.trace (ρHat.mat * cfc (fun x : ℝ => Real.log x) σHat.mat)).re) +
          Real.log w * w -
            Real.log v *
              (w *
                (Matrix.trace
                  (ρHat.mat *
                    cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) σHat.mat)).re) := by
          ring
    _ =
        w * qRelEnt ρHat σHat +
          w * Real.log w -
            Real.log v *
              (w *
                (Matrix.trace
                  (ρHat.mat *
                    cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) σHat.mat)).re) := by
          -- Replace the trace difference with `qRelEnt`.
          simp [hqRel, mul_left_comm, mul_comm, sub_eq_add_neg, add_assoc]
    _ =
        rhsSummand l := by
          simp [rhsSummand, w, v, ρHat, σHat, mul_left_comm, mul_comm]

lemma qRelEnt_pinchAncilla_decompose_pinch_weighted_le
    (ρ σ : Density (m * k))
    (hv : ∀ l : Fin k, 0 < ancillaWeight (m:=m) (k:=k) σ l) :
    qRelEnt
        (pinchAncillaDensity (m:=m) (k:=k) ρ)
        (pinchAncillaDensity (m:=m) (k:=k) σ) ≤
      ∑ l : Fin k,
        (ancillaWeight (m:=m) (k:=k) ρ l *
              qRelEnt (ancillaBlockDensity (m:=m) (k:=k) ρ l)
                      (ancillaBlockDensity (m:=m) (k:=k) σ l) +
            ancillaWeight (m:=m) (k:=k) ρ l *
                Real.log (ancillaWeight (m:=m) (k:=k) ρ l) -
              ancillaWeight (m:=m) (k:=k) ρ l *
                Real.log (ancillaWeight (m:=m) (k:=k) σ l)) := by
  classical
  -- Start from the exact weighted-support decomposition.
  have hEq :=
    qRelEnt_pinchAncilla_decompose_pinch_weighted_support (m:=m) (k:=k) (ρ := ρ) (σ := σ) hv
  rw [hEq]
  -- Bound the support-indicator trace factor by `1`, using `log v ≤ 0` for each block weight `v`.
  refine Finset.sum_le_sum ?_
  intro l _
  set w : ℝ := ancillaWeight (m:=m) (k:=k) ρ l
  set v : ℝ := ancillaWeight (m:=m) (k:=k) σ l
  set ρHat : Density m := ancillaBlockDensity (m:=m) (k:=k) ρ l
  set σHat : Density m := ancillaBlockDensity (m:=m) (k:=k) σ l
  set t : ℝ :=
    (Matrix.trace
        (ρHat.mat *
          cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) σHat.mat)).re
  have hw_nonneg : 0 ≤ w := by
    simpa [w] using ancillaWeight_nonneg (m:=m) (k:=k) ρ l
  have hv_pos : 0 < v := by
    simpa [v] using hv l
  have hv_le_one : v ≤ 1 := by
    have hmem : l ∈ (Finset.univ : Finset (Fin k)) := by simp
    have hle :
        ancillaWeight (m:=m) (k:=k) σ l ≤
          ∑ j : Fin k, ancillaWeight (m:=m) (k:=k) σ j :=
      Finset.single_le_sum
        (fun j _ => ancillaWeight_nonneg (m:=m) (k:=k) σ j)
        hmem
    simpa [v] using hle.trans_eq (ancillaWeight_sum_eq_one (m:=m) (k:=k) σ)
  have hlogv_nonpos : Real.log v ≤ 0 := by
    have hlog := Real.log_le_log hv_pos hv_le_one
    simpa [Real.log_one] using hlog
  have hneglogv_nonneg : 0 ≤ -Real.log v := by
    simpa [neg_nonneg] using hlogv_nonpos
  have ht_le_one : t ≤ 1 := by
    have ht :=
      trace_mul_cfc_supportIndicator_re_le_trace (n := m) (ρ := ρHat.mat) (A := σHat.mat)
        ρHat.posSemidef σHat.mat_isHermitian
    simpa [t, ρHat.traceOne] using ht
  have hwt_le : w * t ≤ w := by
    have :=
      mul_le_mul_of_nonneg_left ht_le_one hw_nonneg
    simpa using this
  have hscaled :
      (-Real.log v) * (w * t) ≤ (-Real.log v) * w := by
    exact mul_le_mul_of_nonneg_left hwt_le hneglogv_nonneg
  -- Add back the shared terms.
  have hterm :
      w * qRelEnt ρHat σHat + w * Real.log w - Real.log v * (w * t) ≤
        w * qRelEnt ρHat σHat + w * Real.log w - Real.log v * w := by
    have h1 :
        w * Real.log w + (-Real.log v) * (w * t) ≤
          w * Real.log w + (-Real.log v) * w :=
      add_le_add_left hscaled (w * Real.log w)
    have h2 :
        w * qRelEnt ρHat σHat + (w * Real.log w + (-Real.log v) * (w * t)) ≤
          w * qRelEnt ρHat σHat + (w * Real.log w + (-Real.log v) * w) :=
      add_le_add_left h1 (w * qRelEnt ρHat σHat)
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]
      using h2
  -- Unfold shorthands.
  simpa [w, v, ρHat, σHat, t, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm,
    add_comm, sub_eq_add_neg] using hterm

end ActiveInference

lemma matrixLogDensity_diagDensity {d : Fin n → ℝ} (hd_nonneg : ∀ i, 0 ≤ d i)
    (hd_sum : ∑ i, d i = 1) :
    matrixLogDensity (Density.diagDensity d hd_nonneg hd_sum) =
      Matrix.diagonal fun i => (Real.log (d i) : ℂ) := by
  classical
  ext i j
  let ρ := Density.diagDensity d hd_nonneg hd_sum
  let e :=
      Pi.single (M := fun _ : Fin n => ℂ) j (1 : ℂ)
  have hv :
      ρ.mat.mulVec e =
        (d j : ℂ) • e := by
    ext k
    by_cases hk : k = j
    · subst hk
      simp [ρ, Density.diagDensity, e, Matrix.mulVec_diagonal]
    · simp [ρ, Density.diagDensity, e, Matrix.mulVec_diagonal, hk]
  have hlog :
      (matrixLogDensity ρ).mulVec e =
        (Real.log (d j) : ℂ) • e :=
    matrixLogDensity_mulVec_eigenvector (ρ := ρ)
      (v := e)
      (μ := d j) hv
  have hdiag :
      (Matrix.diagonal fun i => (Real.log (d i) : ℂ)).mulVec e =
        (Real.log (d j) : ℂ) • e := by
    ext k
    by_cases hk : k = j
    · subst hk
      simp [Matrix.mulVec_diagonal, e]
    · simp [Matrix.mulVec_diagonal, e, hk]
  have hcolEq :
      (matrixLogDensity ρ).mulVec e =
        (Matrix.diagonal fun i => (Real.log (d i) : ℂ)).mulVec e :=
    hlog.trans hdiag.symm
  have hcol :
      (matrixLogDensity ρ).col j =
        (Matrix.diagonal fun i => (Real.log (d i) : ℂ)).col j :=
    (Matrix.mulVec_single_one (matrixLogDensity ρ) j).symm.trans
      (hcolEq.trans
        (Matrix.mulVec_single_one
          (Matrix.diagonal fun i => (Real.log (d i) : ℂ)) j))
  have := congrArg (fun v : Fin n → ℂ => v i) hcol
  simpa [Matrix.col] using this

lemma qRelEnt_diagDensity_eq_sum {d s : Fin n → ℝ}
    (hd_nonneg : ∀ i, 0 ≤ d i) (hd_sum : ∑ i, d i = 1)
    (hs_nonneg : ∀ i, 0 ≤ s i) (hs_sum : ∑ i, s i = 1) :
    qRelEnt (Density.diagDensity d hd_nonneg hd_sum)
        (Density.diagDensity s hs_nonneg hs_sum) =
      ∑ i, d i * (Real.log (d i) - Real.log (s i)) := by
  classical
  have hρ :
      (Density.diagDensity d hd_nonneg hd_sum).mat =
        Matrix.diagonal fun i => (d i : ℂ) := rfl
  have hσ :
      (Density.diagDensity s hs_nonneg hs_sum).mat =
        Matrix.diagonal fun i => (s i : ℂ) := rfl
  have hlogρ :
      matrixLogDensity (Density.diagDensity d hd_nonneg hd_sum) =
        Matrix.diagonal fun i => (Real.log (d i) : ℂ) :=
    matrixLogDensity_diagDensity hd_nonneg hd_sum
  have hlogσ :
      matrixLogDensity (Density.diagDensity s hs_nonneg hs_sum) =
        Matrix.diagonal fun i => (Real.log (s i) : ℂ) :=
    matrixLogDensity_diagDensity hs_nonneg hs_sum
  have hdiff :
      matrixLogDensity (Density.diagDensity d hd_nonneg hd_sum) -
          matrixLogDensity (Density.diagDensity s hs_nonneg hs_sum) =
        Matrix.diagonal fun i =>
          (Real.log (d i) : ℂ) - (Real.log (s i) : ℂ) := by
    simp [hlogρ, hlogσ, Matrix.diagonal_sub]
  have hprod :
      (Density.diagDensity d hd_nonneg hd_sum).mat *
          (matrixLogDensity (Density.diagDensity d hd_nonneg hd_sum) -
            matrixLogDensity (Density.diagDensity s hs_nonneg hs_sum)) =
        Matrix.diagonal fun i =>
          (d i : ℂ) * ((Real.log (d i) : ℂ) - (Real.log (s i) : ℂ)) := by
    simp [hρ, hdiff]
  have htrace :
      Matrix.trace
          ((Density.diagDensity d hd_nonneg hd_sum).mat *
            (matrixLogDensity (Density.diagDensity d hd_nonneg hd_sum) -
              matrixLogDensity (Density.diagDensity s hs_nonneg hs_sum))) =
        ∑ i, (d i : ℂ) *
          ((Real.log (d i) : ℂ) - (Real.log (s i) : ℂ)) := by
    simp [hprod, Matrix.trace_diagonal]
  have hterm :
      ∀ i,
        (d i : ℂ) * ((Real.log (d i) : ℂ) - (Real.log (s i) : ℂ)) =
          Complex.ofReal (d i * (Real.log (d i) - Real.log (s i))) := by
    intro i
    simp [Complex.ofReal_mul, sub_eq_add_neg, Complex.ofReal_add,
      Complex.ofReal_neg]
  have hsum :
      ∑ i, (d i : ℂ) * ((Real.log (d i) : ℂ) - (Real.log (s i) : ℂ)) =
        Complex.ofReal (∑ i, d i * (Real.log (d i) - Real.log (s i))) := by
    have hsum₁ :
        ∑ i, (d i : ℂ) * ((Real.log (d i) : ℂ) - (Real.log (s i) : ℂ)) =
          ∑ i, Complex.ofReal (d i * (Real.log (d i) - Real.log (s i))) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      exact hterm i
    have hsum₂ :
        ∑ i, Complex.ofReal (d i * (Real.log (d i) - Real.log (s i))) =
          Complex.ofReal (∑ i, d i * (Real.log (d i) - Real.log (s i))) := by
      simp
    exact hsum₁.trans hsum₂
  have htraceReal :
      Matrix.trace
          ((Density.diagDensity d hd_nonneg hd_sum).mat *
            (matrixLogDensity (Density.diagDensity d hd_nonneg hd_sum) -
              matrixLogDensity (Density.diagDensity s hs_nonneg hs_sum))) =
        Complex.ofReal (∑ i, d i * (Real.log (d i) - Real.log (s i))) :=
    htrace.trans hsum
  have hreal := congrArg Complex.re htraceReal
  change
      ((Matrix.trace
          ((Density.diagDensity d hd_nonneg hd_sum).mat *
            (matrixLogDensity (Density.diagDensity d hd_nonneg hd_sum) -
              matrixLogDensity (Density.diagDensity s hs_nonneg hs_sum)))).re) =
        _
  exact hreal

end MatrixLogDensity

end

end Quantum
end HeytingLean
