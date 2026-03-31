/-
The spectral/cohomological surface in this module is intentionally built on the
canonical `Orientation.sortedOrientation K`. This is the theorem surface used by
the current PSL library and by the MENTAT BVF tool.

Arbitrary-orientation invariance is mathematically expected but not yet
formalized here; it is tracked separately as follow-on conjecture
`psl_orientation_independence_20260316`.
-/

import HeytingLean.PersistentSheafLaplacian.Laplacian.SheafLaplacian
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

namespace HeytingLean
namespace PersistentSheafLaplacian

open SimplicialComplex

namespace Laplacian

open Cochain

variable {V : Type*} [DecidableEq V] [LinearOrder V] {K : SimplicialComplex V}

/-- Sorted-orientation cocycles in degree `q`. -/
noncomputable def sheafCocycles (F : CellularSheaf K) (q : Nat) :
    Submodule ℝ (CochainGroup F q) :=
  LinearMap.ker (coboundary F (Orientation.sortedOrientation K) q)

/-- Sorted-orientation coboundaries in degree `q`.
    Degree `0` has no incoming coboundary, so its boundary space is `⊥`. -/
noncomputable def sheafCoboundaries (F : CellularSheaf K) :
    (q : Nat) → Submodule ℝ (CochainGroup F q)
  | 0 => ⊥
  | q + 1 => LinearMap.range (coboundary F (Orientation.sortedOrientation K) q)

/-- Boundaries lie in cocycles because the sorted-orientation coboundary squares to zero. -/
theorem sheafCoboundaries_le_sheafCocycles (F : CellularSheaf K) :
    ∀ q, sheafCoboundaries (K := K) F q ≤ sheafCocycles (K := K) F q
  | 0 => by
      intro x hx
      rw [sheafCoboundaries] at hx
      rw [Submodule.mem_bot] at hx
      subst x
      simp [sheafCocycles]
  | q + 1 => by
      intro x hx
      rcases hx with ⟨y, rfl⟩
      show coboundary F (Orientation.sortedOrientation K) (q + 1)
          (coboundary F (Orientation.sortedOrientation K) q y) = 0
      simpa using LinearMap.congr_fun (coboundary_comp_eq_zero_sorted F q) y

/-- Coboundaries regarded as a submodule of cocycles. -/
noncomputable def sheafCoboundariesInCocycles (F : CellularSheaf K) (q : Nat) :
    Submodule ℝ (sheafCocycles (K := K) F q) :=
  Submodule.comap (sheafCocycles (K := K) F q).subtype (sheafCoboundaries (K := K) F q)

/-- Sorted-orientation sheaf cohomology `H^q(K;F) = Z^q / B^q`.
    This packages the genuine quotient surface needed for the eventual Hodge theorem. -/
abbrev sheafCohomology (F : CellularSheaf K) (q : Nat) : Type _ :=
  sheafCocycles (K := K) F q ⧸ sheafCoboundariesInCocycles (K := K) F q

/-- Cohomological Betti number on the current sorted-orientation theorem surface. -/
noncomputable def cohomologicalSheafBetti (F : CellularSheaf K) (q : Nat) : Nat :=
  Module.finrank ℝ (sheafCohomology (K := K) F q)

/-- Coboundaries viewed inside cocycles are linearly equivalent to the original coboundary space. -/
noncomputable def sheafCoboundariesInCocyclesEquiv (F : CellularSheaf K) (q : Nat) :
    sheafCoboundariesInCocycles (K := K) F q ≃ₗ[ℝ] sheafCoboundaries (K := K) F q :=
  Submodule.comapSubtypeEquivOfLe (sheafCoboundaries_le_sheafCocycles (K := K) F q)

/-- The embedded coboundary space has the same dimension as the original coboundary space. -/
theorem finrank_sheafCoboundariesInCocycles (F : CellularSheaf K) (q : Nat) :
    Module.finrank ℝ (sheafCoboundariesInCocycles (K := K) F q) =
      Module.finrank ℝ (sheafCoboundaries (K := K) F q) := by
  simpa using
    (LinearEquiv.finrank_eq
      (sheafCoboundariesInCocyclesEquiv (K := K) F q))

/-- Cohomological Betti numbers are the cocycle dimension minus the coboundary dimension whenever
    the `q`-cochain group is finite-dimensional, as witnessed by a finite stalk basis family. -/
theorem cohomologicalSheafBetti_eq_finrank_cocycles_sub_finrank_coboundaries
    (F : CellularSheaf K) (q : Nat)
    (ιq : StalkIndexFamily (K := K) q)
    [∀ σ, Fintype (ιq σ)] [∀ σ, DecidableEq (ιq σ)]
    (bq : StalkBasisFamily F q ιq) :
    cohomologicalSheafBetti (K := K) F q =
      Module.finrank ℝ (sheafCocycles (K := K) F q) -
        Module.finrank ℝ (sheafCoboundaries (K := K) F q) := by
  letI : FiniteDimensional ℝ (CochainGroup F q) :=
    FiniteDimensional.of_fintype_basis (Cochain.cochainBasis F q ιq bq)
  unfold cohomologicalSheafBetti
  change Module.finrank ℝ
      (sheafCocycles (K := K) F q ⧸ sheafCoboundariesInCocycles (K := K) F q) =
    Module.finrank ℝ (sheafCocycles (K := K) F q) -
      Module.finrank ℝ (sheafCoboundaries (K := K) F q)
  rw [Submodule.finrank_quotient, finrank_sheafCoboundariesInCocycles]

private theorem map_sheafCocycles_to_matrix_ker
    (F : CellularSheaf K) (q : Nat)
    (ιq : StalkIndexFamily (K := K) q)
    (ιq1 : StalkIndexFamily (K := K) (q + 1))
    [∀ σ, Fintype (ιq σ)] [∀ τ, Fintype (ιq1 τ)]
    [∀ σ, DecidableEq (ιq σ)] [∀ τ, DecidableEq (ιq1 τ)]
    (bq : StalkBasisFamily F q ιq) (bq1 : StalkBasisFamily F (q + 1) ιq1) :
    Submodule.map ((cochainBasis F q ιq bq).equivFun : _ ≃ₗ[ℝ] _).toLinearMap
        (sheafCocycles (K := K) F q) =
      LinearMap.ker
        (Matrix.toLin'
          (coboundaryMatrix F (Orientation.sortedOrientation K) q ιq ιq1 bq bq1)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change coboundary F (Orientation.sortedOrientation K) q x = 0 at hx
    change Matrix.toLin'
        (coboundaryMatrix F (Orientation.sortedOrientation K) q ιq ιq1 bq bq1)
        ((cochainBasis F q ιq bq).equivFun x) = 0
    have hrepr :=
      LinearMap.toMatrix_mulVec_repr
        (v₁ := cochainBasis F q ιq bq)
        (v₂ := cochainBasis F (q + 1) ιq1 bq1)
        (f := coboundary F (Orientation.sortedOrientation K) q) x
    have hcoord :
        Matrix.toLin'
            (coboundaryMatrix F (Orientation.sortedOrientation K) q ιq ιq1 bq bq1)
            ((cochainBasis F q ιq bq).equivFun x) =
          (cochainBasis F (q + 1) ιq1 bq1).equivFun
            ((coboundary F (Orientation.sortedOrientation K) q) x) := by
      simpa [Matrix.toLin'_apply, Module.Basis.equivFun_apply, coboundaryMatrix] using hrepr
    simpa [hx] using hcoord
  · intro hy
    refine ⟨(cochainBasis F q ιq bq).equivFun.symm y, ?_,
      (cochainBasis F q ιq bq).equivFun.apply_symm_apply y⟩
    change coboundary F (Orientation.sortedOrientation K) q
        ((cochainBasis F q ιq bq).equivFun.symm y) = 0
    apply (cochainBasis F (q + 1) ιq1 bq1).equivFun.injective
    have hy' : Matrix.toLin'
        (coboundaryMatrix F (Orientation.sortedOrientation K) q ιq ιq1 bq bq1) y = 0 := by
      simpa [LinearMap.mem_ker] using hy
    have hrepr :=
      LinearMap.toMatrix_mulVec_repr
        (v₁ := cochainBasis F q ιq bq)
        (v₂ := cochainBasis F (q + 1) ιq1 bq1)
        (f := coboundary F (Orientation.sortedOrientation K) q)
        ((cochainBasis F q ιq bq).equivFun.symm y)
    rw [Module.Basis.equivFun_symm_apply] at hrepr
    rw [(cochainBasis F q ιq bq).repr_sum_self] at hrepr
    have hcoord :
        Matrix.toLin'
            (coboundaryMatrix F (Orientation.sortedOrientation K) q ιq ιq1 bq bq1) y =
          (cochainBasis F (q + 1) ιq1 bq1).repr
            ((coboundary F (Orientation.sortedOrientation K) q)
              ((cochainBasis F q ιq bq).equivFun.symm y)) := by
      simpa [Matrix.toLin'_apply, Module.Basis.equivFun_apply, coboundaryMatrix] using hrepr
    ext i
    have hi := congrArg (fun f => f i) hcoord.symm
    simpa [hy'] using hi

private theorem map_sheafCoboundaries_succ_to_matrix_range
    (F : CellularSheaf K) (q : Nat)
    (ιq : StalkIndexFamily (K := K) q)
    (ιq1 : StalkIndexFamily (K := K) (q + 1))
    [∀ σ, Fintype (ιq σ)] [∀ τ, Fintype (ιq1 τ)]
    [∀ σ, DecidableEq (ιq σ)] [∀ τ, DecidableEq (ιq1 τ)]
    (bq : StalkBasisFamily F q ιq) (bq1 : StalkBasisFamily F (q + 1) ιq1) :
    Submodule.map ((cochainBasis F (q + 1) ιq1 bq1).equivFun : _ ≃ₗ[ℝ] _).toLinearMap
        (sheafCoboundaries (K := K) F (q + 1)) =
      LinearMap.range
        (Matrix.toLin'
          (coboundaryMatrix F (Orientation.sortedOrientation K) q ιq ιq1 bq bq1)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨z, rfl⟩
    refine ⟨(cochainBasis F q ιq bq).equivFun z, ?_⟩
    have hrepr :=
      LinearMap.toMatrix_mulVec_repr
        (v₁ := cochainBasis F q ιq bq)
        (v₂ := cochainBasis F (q + 1) ιq1 bq1)
        (f := coboundary F (Orientation.sortedOrientation K) q) z
    have hcoord :
        Matrix.toLin'
            (coboundaryMatrix F (Orientation.sortedOrientation K) q ιq ιq1 bq bq1)
            ((cochainBasis F q ιq bq).equivFun z) =
          (cochainBasis F (q + 1) ιq1 bq1).equivFun
            ((coboundary F (Orientation.sortedOrientation K) q) z) := by
      simpa [Matrix.toLin'_apply, Module.Basis.equivFun_apply, coboundaryMatrix] using hrepr
    simpa using hcoord
  · rintro ⟨x, rfl⟩
    refine ⟨(cochainBasis F (q + 1) ιq1 bq1).equivFun.symm
        (Matrix.toLin'
          (coboundaryMatrix F (Orientation.sortedOrientation K) q ιq ιq1 bq bq1) x), ?_, ?_⟩
    · refine ⟨(cochainBasis F q ιq bq).equivFun.symm x, ?_⟩
      apply (cochainBasis F (q + 1) ιq1 bq1).equivFun.injective
      have hrepr :=
        LinearMap.toMatrix_mulVec_repr
          (v₁ := cochainBasis F q ιq bq)
          (v₂ := cochainBasis F (q + 1) ιq1 bq1)
          (f := coboundary F (Orientation.sortedOrientation K) q)
          ((cochainBasis F q ιq bq).equivFun.symm x)
      rw [Module.Basis.equivFun_symm_apply] at hrepr
      rw [(cochainBasis F q ιq bq).repr_sum_self] at hrepr
      have hcoord :
          Matrix.toLin'
              (coboundaryMatrix F (Orientation.sortedOrientation K) q ιq ιq1 bq bq1) x =
            (cochainBasis F (q + 1) ιq1 bq1).equivFun
              ((coboundary F (Orientation.sortedOrientation K) q)
                ((cochainBasis F q ιq bq).equivFun.symm x)) := by
        simpa [Matrix.toLin'_apply, Module.Basis.equivFun_apply, coboundaryMatrix] using hrepr
      exact hcoord.symm.trans
        ((cochainBasis F (q + 1) ιq1 bq1).equivFun.apply_symm_apply _).symm
    · exact (cochainBasis F (q + 1) ιq1 bq1).equivFun.apply_symm_apply _

section MatrixHodge

omit V K in
private theorem mem_orthogonal_range_iff_mem_ker_adjoint
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (T : E →ₗ[ℝ] F) (x : F) :
    x ∈ (LinearMap.range T)ᗮ ↔ x ∈ LinearMap.ker T.adjoint := by
  rw [Submodule.mem_orthogonal, LinearMap.mem_ker]
  constructor
  · intro hx
    apply ext_inner_left ℝ
    intro y
    have hy0 : inner ℝ (T y) x = inner ℝ y 0 := by
      simpa using hx (T y) ⟨y, rfl⟩
    exact (LinearMap.adjoint_inner_right (A := T) y x).trans hy0
  · intro hx y hy
    rcases hy with ⟨z, rfl⟩
    exact (LinearMap.adjoint_inner_right (A := T) z x).symm.trans (by simp [hx])

omit V K in
private theorem ker_hodge_proto
    {E F G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    (A : E →ₗ[ℝ] F) (B : G →ₗ[ℝ] E) :
    LinearMap.ker (A.adjoint ∘ₗ A + B ∘ₗ B.adjoint) =
      LinearMap.ker A ⊓ (LinearMap.range B)ᗮ := by
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_ker] at hx
    rw [Submodule.mem_inf, LinearMap.mem_ker, Submodule.mem_orthogonal]
    have hinner := congrArg (fun y => inner ℝ x y) hx
    have h1 : inner ℝ x ((A.adjoint ∘ₗ A) x) = ‖A x‖ ^ 2 := by
      simpa [LinearMap.comp_apply, inner_self_eq_norm_sq_to_K] using
        (LinearMap.adjoint_inner_right (A := A) x (A x))
    have h2 : inner ℝ x ((B ∘ₗ B.adjoint) x) = ‖B.adjoint x‖ ^ 2 := by
      simpa [LinearMap.comp_apply, inner_self_eq_norm_sq_to_K] using
        (LinearMap.adjoint_inner_right (A := B.adjoint) x (B.adjoint x))
    have hsum : inner ℝ x ((A.adjoint ∘ₗ A) x) + inner ℝ x ((B ∘ₗ B.adjoint) x) = 0 := by
      simpa [LinearMap.add_apply, inner_add_right] using hinner
    rw [h1, h2] at hsum
    constructor
    · have hAx2 : ‖A x‖ ^ 2 = 0 := by
        nlinarith [sq_nonneg ‖A x‖, sq_nonneg ‖B.adjoint x‖]
      exact norm_eq_zero.mp <| sq_eq_zero_iff.mp hAx2
    · intro y hy
      rcases hy with ⟨z, rfl⟩
      have hBx2 : ‖B.adjoint x‖ ^ 2 = 0 := by
        nlinarith [sq_nonneg ‖A x‖, sq_nonneg ‖B.adjoint x‖]
      have hBx : B.adjoint x = 0 := norm_eq_zero.mp <| sq_eq_zero_iff.mp hBx2
      exact (LinearMap.adjoint_inner_right (A := B) z x).symm.trans (by simp [hBx])
  · intro hx
    rw [Submodule.mem_inf, LinearMap.mem_ker, Submodule.mem_orthogonal] at hx
    have hBx : B.adjoint x = 0 := by
      apply ext_inner_left ℝ
      intro z
      have hz0 : inner ℝ (B z) x = inner ℝ z 0 := by
        simpa using hx.2 (B z) ⟨z, rfl⟩
      exact (LinearMap.adjoint_inner_right (A := B) z x).trans hz0
    rw [LinearMap.mem_ker]
    simp [LinearMap.comp_apply, hx.1, hBx]

omit V K in
private theorem toEuclideanLin_mul
    {l m n : Type*}
    [Fintype l] [Fintype m] [Fintype n]
    [DecidableEq l] [DecidableEq m] [DecidableEq n]
    (M : Matrix l m ℝ) (N : Matrix m n ℝ) :
    Matrix.toEuclideanLin (M * N) = Matrix.toEuclideanLin M ∘ₗ Matrix.toEuclideanLin N := by
  apply LinearMap.ext
  intro x
  apply (WithLp.linearEquiv 2 ℝ (l → ℝ)).injective
  simp [Matrix.toLin'_mul, LinearMap.comp_apply]

omit V K in
private theorem map_ker_toEuclideanLin
    {m n : Type*}
    [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (M : Matrix m n ℝ) :
    Submodule.map (WithLp.linearEquiv 2 ℝ (n → ℝ)) (LinearMap.ker (Matrix.toEuclideanLin M)) =
      LinearMap.ker (Matrix.toLin' M) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : Matrix.toEuclideanLin M x = 0 := by
      simpa [LinearMap.mem_ker] using hx
    show Matrix.toLin' M ((WithLp.linearEquiv 2 ℝ (n → ℝ)) x) = 0
    simpa using congrArg WithLp.ofLp hx'
  · intro hy
    refine ⟨WithLp.toLp 2 y, ?_, by simp⟩
    have hy' : Matrix.toLin' M y = 0 := by
      simpa [LinearMap.mem_ker] using hy
    show Matrix.toEuclideanLin M (WithLp.toLp 2 y) = 0
    apply WithLp.ofLp_injective
    simpa using hy'

omit V K in
private theorem finrank_ker_toEuclideanLin_eq_finrank_ker_toLin'
    {m n : Type*}
    [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (M : Matrix m n ℝ) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toEuclideanLin M)) =
      Module.finrank ℝ (LinearMap.ker (Matrix.toLin' M)) := by
  have hfin :=
    LinearEquiv.finrank_eq
      ((WithLp.linearEquiv 2 ℝ (n → ℝ)).submoduleMap (LinearMap.ker (Matrix.toEuclideanLin M)))
  calc
    Module.finrank ℝ (LinearMap.ker (Matrix.toEuclideanLin M)) =
        Module.finrank ℝ
          (Submodule.map (WithLp.linearEquiv 2 ℝ (n → ℝ))
            (LinearMap.ker (Matrix.toEuclideanLin M))) := hfin
    _ = Module.finrank ℝ (LinearMap.ker (Matrix.toLin' M)) := by
      rw [map_ker_toEuclideanLin]

omit V K in
private theorem map_range_toEuclideanLin
    {m n : Type*}
    [Fintype m] [Fintype n]
    [DecidableEq n]
    (M : Matrix m n ℝ) :
    Submodule.map (WithLp.linearEquiv 2 ℝ (m → ℝ)) (LinearMap.range (Matrix.toEuclideanLin M)) =
      LinearMap.range (Matrix.toLin' M) := by
  ext y
  constructor
  · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
    exact ⟨WithLp.ofLp z, by simp⟩
  · rintro ⟨x, rfl⟩
    refine ⟨Matrix.toEuclideanLin M (WithLp.toLp 2 x), ?_, ?_⟩
    · exact ⟨WithLp.toLp 2 x, rfl⟩
    · simp

omit V K in
private theorem finrank_range_toEuclideanLin_eq_finrank_range_toLin'
    {m n : Type*}
    [Fintype m] [Fintype n]
    [DecidableEq n]
    (M : Matrix m n ℝ) :
    Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin M)) =
      Module.finrank ℝ (LinearMap.range (Matrix.toLin' M)) := by
  have hfin :=
    LinearEquiv.finrank_eq
      ((WithLp.linearEquiv 2 ℝ (m → ℝ)).submoduleMap (LinearMap.range (Matrix.toEuclideanLin M)))
  calc
    Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin M)) =
        Module.finrank ℝ
          (Submodule.map (WithLp.linearEquiv 2 ℝ (m → ℝ))
            (LinearMap.range (Matrix.toEuclideanLin M))) := hfin
    _ = Module.finrank ℝ (LinearMap.range (Matrix.toLin' M)) := by
      rw [map_range_toEuclideanLin]

omit V K in
private theorem toEuclideanLin_hodgeLaplacianMatrix
    {ιPrev ι ιNext : Type*}
    [Fintype ιPrev] [Fintype ι] [Fintype ιNext]
    [DecidableEq ιPrev] [DecidableEq ι] [DecidableEq ιNext]
    (dPrev : Matrix ι ιPrev ℝ) (dNext : Matrix ιNext ι ℝ) :
    Matrix.toEuclideanLin (hodgeLaplacianMatrix dPrev dNext) =
      (Matrix.toEuclideanLin dNext).adjoint ∘ₗ Matrix.toEuclideanLin dNext +
        Matrix.toEuclideanLin dPrev ∘ₗ (Matrix.toEuclideanLin dPrev).adjoint := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  apply LinearMap.ext
  intro x
  apply (WithLp.linearEquiv 2 ℝ (ι → ℝ)).injective
  simp [hodgeLaplacianMatrix, Matrix.toLin'_mul, LinearMap.comp_apply, add_comm]

omit V K in
private theorem finrank_ker_toEuclideanLin_hodge_eq
    {ιPrev ι ιNext : Type*}
    [Fintype ιPrev] [Fintype ι] [Fintype ιNext]
    [DecidableEq ιPrev] [DecidableEq ι] [DecidableEq ιNext]
    (dPrev : Matrix ι ιPrev ℝ) (dNext : Matrix ιNext ι ℝ)
    (hcomp : dNext * dPrev = 0) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toEuclideanLin (hodgeLaplacianMatrix dPrev dNext))) =
      Module.finrank ℝ (LinearMap.ker (Matrix.toEuclideanLin dNext)) -
        Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin dPrev)) := by
  have hcompLin : Matrix.toEuclideanLin dNext ∘ₗ Matrix.toEuclideanLin dPrev = 0 := by
    rw [← toEuclideanLin_mul]
    simpa using congrArg Matrix.toEuclideanLin hcomp
  have hker := ker_hodge_proto (A := Matrix.toEuclideanLin dNext) (B := Matrix.toEuclideanLin dPrev)
  have hrange : LinearMap.range (Matrix.toEuclideanLin dPrev) ≤
      LinearMap.ker (Matrix.toEuclideanLin dNext) := by
    rw [LinearMap.range_le_ker_iff]
    exact hcompLin
  have hdim : Module.finrank ℝ ↥(LinearMap.range (Matrix.toEuclideanLin dPrev)) +
      Module.finrank ℝ ↥((LinearMap.ker (Matrix.toEuclideanLin dNext)) ⊓
        (LinearMap.range (Matrix.toEuclideanLin dPrev))ᗮ) =
        Module.finrank ℝ ↥(LinearMap.ker (Matrix.toEuclideanLin dNext)) := by
    have hdim0 := Submodule.finrank_add_inf_finrank_orthogonal hrange
    rw [inf_comm] at hdim0
    exact hdim0
  rw [toEuclideanLin_hodgeLaplacianMatrix, hker]
  omega

end MatrixHodge

private theorem coboundaryMatrix_mul_coboundaryMatrix_eq_zero_sorted
    (F : CellularSheaf K) (q : Nat)
    (ιq : StalkIndexFamily (K := K) q)
    (ιq1 : StalkIndexFamily (K := K) (q + 1))
    (ιq2 : StalkIndexFamily (K := K) (q + 2))
    [∀ σ, Fintype (ιq σ)] [∀ σ, Fintype (ιq1 σ)] [∀ σ, Fintype (ιq2 σ)]
    [∀ σ, DecidableEq (ιq σ)] [∀ σ, DecidableEq (ιq1 σ)] [∀ σ, DecidableEq (ιq2 σ)]
    (bq : StalkBasisFamily F q ιq)
    (bq1 : StalkBasisFamily F (q + 1) ιq1)
    (bq2 : StalkBasisFamily F (q + 2) ιq2) :
    coboundaryMatrix F (Orientation.sortedOrientation K) (q + 1) ιq1 ιq2 bq1 bq2 *
      coboundaryMatrix F (Orientation.sortedOrientation K) q ιq ιq1 bq bq1 = 0 := by
  rw [coboundaryMatrix, coboundaryMatrix,
    ← LinearMap.toMatrix_comp (cochainBasis F q ιq bq)
      (cochainBasis F (q + 1) ιq1 bq1) (cochainBasis F (q + 2) ιq2 bq2)]
  simp [coboundary_comp_eq_zero_sorted]

/-- Harmonic nullity of the canonical sheaf Laplacian matrix on degree `q + 1` cochains in chosen
    coordinates. The parameter `q` names the lower adjacent coboundary degree in the Hodge formula
    `D_qᵀ D_q + D_{q+1}ᵀ D_{q+1}`. -/
noncomputable def harmonicSheafNullity (F : CellularSheaf K) (q : Nat)
    (ιq : StalkIndexFamily (K := K) q)
    (ιq1 : StalkIndexFamily (K := K) (q + 1))
    (ιq2 : StalkIndexFamily (K := K) (q + 2))
    [∀ σ, Fintype (ιq σ)] [∀ σ, Fintype (ιq1 σ)] [∀ σ, Fintype (ιq2 σ)]
    [∀ σ, DecidableEq (ιq σ)] [∀ σ, DecidableEq (ιq1 σ)] [∀ σ, DecidableEq (ιq2 σ)]
    (bq : StalkBasisFamily F q ιq)
    (bq1 : StalkBasisFamily F (q + 1) ιq1)
    (bq2 : StalkBasisFamily F (q + 2) ιq2) : Nat :=
  Module.finrank ℝ <|
    LinearMap.ker <|
      Matrix.toLin' (sheafLaplacianMatrix F (Orientation.sortedOrientation K) q
        ιq ιq1 ιq2 bq bq1 bq2)

/-- On the current sorted-orientation surface, the harmonic nullity of the sheaf Laplacian is
    already the nullity of the upper coboundary matrix minus the rank of the lower coboundary
    matrix. This is the matrix-side Hodge identity that reduces the remaining theorem work to
    bridging matrix kernels/ranges back to the abstract cocycle/coboundary quotient. -/
theorem harmonicSheafNullity_eq_finrank_ker_sub_finrank_range
    (F : CellularSheaf K) (q : Nat)
    (ιq : StalkIndexFamily (K := K) q)
    (ιq1 : StalkIndexFamily (K := K) (q + 1))
    (ιq2 : StalkIndexFamily (K := K) (q + 2))
    [∀ σ, Fintype (ιq σ)] [∀ σ, Fintype (ιq1 σ)] [∀ σ, Fintype (ιq2 σ)]
    [∀ σ, DecidableEq (ιq σ)] [∀ σ, DecidableEq (ιq1 σ)] [∀ σ, DecidableEq (ιq2 σ)]
    (bq : StalkBasisFamily F q ιq)
    (bq1 : StalkBasisFamily F (q + 1) ιq1)
    (bq2 : StalkBasisFamily F (q + 2) ιq2) :
    harmonicSheafNullity (K := K) F q ιq ιq1 ιq2 bq bq1 bq2 =
      Module.finrank ℝ
          (LinearMap.ker
            (Matrix.toLin'
              (coboundaryMatrix F (Orientation.sortedOrientation K) (q + 1) ιq1 ιq2 bq1 bq2))) -
        Module.finrank ℝ
          (LinearMap.range
            (Matrix.toLin'
              (coboundaryMatrix F (Orientation.sortedOrientation K) q ιq ιq1 bq bq1))) := by
  let dPrev := coboundaryMatrix F (Orientation.sortedOrientation K) q ιq ιq1 bq bq1
  let dNext := coboundaryMatrix F (Orientation.sortedOrientation K) (q + 1) ιq1 ιq2 bq1 bq2
  unfold harmonicSheafNullity
  rw [← finrank_ker_toEuclideanLin_eq_finrank_ker_toLin'
      (M := sheafLaplacianMatrix F (Orientation.sortedOrientation K) q ιq ιq1 ιq2 bq bq1 bq2)]
  have h := finrank_ker_toEuclideanLin_hodge_eq dPrev dNext
    (coboundaryMatrix_mul_coboundaryMatrix_eq_zero_sorted F q ιq ιq1 ιq2 bq bq1 bq2)
  rw [finrank_ker_toEuclideanLin_eq_finrank_ker_toLin' (M := dNext),
    finrank_range_toEuclideanLin_eq_finrank_range_toLin' (M := dPrev)] at h
  simpa [dPrev, dNext, sheafLaplacianMatrix] using h

theorem finrank_sheafCocycles_eq_finrank_matrix_ker
    (F : CellularSheaf K) (q : Nat)
    (ιq : StalkIndexFamily (K := K) q)
    (ιq1 : StalkIndexFamily (K := K) (q + 1))
    [∀ σ, Fintype (ιq σ)] [∀ τ, Fintype (ιq1 τ)]
    [∀ σ, DecidableEq (ιq σ)] [∀ τ, DecidableEq (ιq1 τ)]
    (bq : StalkBasisFamily F q ιq) (bq1 : StalkBasisFamily F (q + 1) ιq1) :
    Module.finrank ℝ (sheafCocycles (K := K) F q) =
      Module.finrank ℝ
        (LinearMap.ker
          (Matrix.toLin'
            (coboundaryMatrix F (Orientation.sortedOrientation K) q ιq ιq1 bq bq1))) := by
  calc
    Module.finrank ℝ (sheafCocycles (K := K) F q) =
        Module.finrank ℝ
          (Submodule.map ((cochainBasis F q ιq bq).equivFun : _ ≃ₗ[ℝ] _).toLinearMap
            (sheafCocycles (K := K) F q)) := by
          symm
          simpa using
            LinearEquiv.finrank_map_eq
              ((cochainBasis F q ιq bq).equivFun)
              (sheafCocycles (K := K) F q)
    _ = Module.finrank ℝ
          (LinearMap.ker
            (Matrix.toLin'
              (coboundaryMatrix F (Orientation.sortedOrientation K) q ιq ιq1 bq bq1))) := by
          rw [map_sheafCocycles_to_matrix_ker F q ιq ιq1 bq bq1]

theorem finrank_sheafCoboundaries_succ_eq_finrank_matrix_range
    (F : CellularSheaf K) (q : Nat)
    (ιq : StalkIndexFamily (K := K) q)
    (ιq1 : StalkIndexFamily (K := K) (q + 1))
    [∀ σ, Fintype (ιq σ)] [∀ τ, Fintype (ιq1 τ)]
    [∀ σ, DecidableEq (ιq σ)] [∀ τ, DecidableEq (ιq1 τ)]
    (bq : StalkBasisFamily F q ιq) (bq1 : StalkBasisFamily F (q + 1) ιq1) :
    Module.finrank ℝ (sheafCoboundaries (K := K) F (q + 1)) =
      Module.finrank ℝ
        (LinearMap.range
          (Matrix.toLin'
            (coboundaryMatrix F (Orientation.sortedOrientation K) q ιq ιq1 bq bq1))) := by
  calc
    Module.finrank ℝ (sheafCoboundaries (K := K) F (q + 1)) =
        Module.finrank ℝ
          (Submodule.map ((cochainBasis F (q + 1) ιq1 bq1).equivFun : _ ≃ₗ[ℝ] _).toLinearMap
            (sheafCoboundaries (K := K) F (q + 1))) := by
          symm
          simpa using
            LinearEquiv.finrank_map_eq
              ((cochainBasis F (q + 1) ιq1 bq1).equivFun)
              (sheafCoboundaries (K := K) F (q + 1))
    _ = Module.finrank ℝ
          (LinearMap.range
            (Matrix.toLin'
              (coboundaryMatrix F (Orientation.sortedOrientation K) q ιq ιq1 bq bq1))) := by
          rw [map_sheafCoboundaries_succ_to_matrix_range F q ιq ιq1 bq bq1]

/-- Sorted-orientation Hodge theorem on the current finite-basis surface:
    the harmonic nullity of the canonical sheaf Laplacian in degree `q + 1`
    equals the sorted-orientation sheaf cohomology Betti number in degree `q + 1`. -/
theorem hodge_sheaf (F : CellularSheaf K) (q : Nat)
    (ιq : StalkIndexFamily (K := K) q)
    (ιq1 : StalkIndexFamily (K := K) (q + 1))
    (ιq2 : StalkIndexFamily (K := K) (q + 2))
    [∀ σ, Fintype (ιq σ)] [∀ σ, Fintype (ιq1 σ)] [∀ σ, Fintype (ιq2 σ)]
    [∀ σ, DecidableEq (ιq σ)] [∀ σ, DecidableEq (ιq1 σ)] [∀ σ, DecidableEq (ιq2 σ)]
    (bq : StalkBasisFamily F q ιq)
    (bq1 : StalkBasisFamily F (q + 1) ιq1)
    (bq2 : StalkBasisFamily F (q + 2) ιq2) :
    harmonicSheafNullity (K := K) F q ιq ιq1 ιq2 bq bq1 bq2 =
      cohomologicalSheafBetti (K := K) F (q + 1) := by
  rw [harmonicSheafNullity_eq_finrank_ker_sub_finrank_range F q ιq ιq1 ιq2 bq bq1 bq2,
    cohomologicalSheafBetti_eq_finrank_cocycles_sub_finrank_coboundaries F (q + 1) ιq1 bq1,
    ← finrank_sheafCocycles_eq_finrank_matrix_ker F (q + 1) ιq1 ιq2 bq1 bq2,
    ← finrank_sheafCoboundaries_succ_eq_finrank_matrix_range F q ιq ιq1 bq bq1]

/-- Spectrum of the canonical sorted-orientation sheaf Laplacian on degree `q + 1` cochains. -/
noncomputable def sheafLaplacianSpectrum (F : CellularSheaf K) (q : Nat)
    (ιq : StalkIndexFamily (K := K) q)
    (ιq1 : StalkIndexFamily (K := K) (q + 1))
    (ιq2 : StalkIndexFamily (K := K) (q + 2))
    [∀ σ, Fintype (ιq σ)] [∀ σ, Fintype (ιq1 σ)] [∀ σ, Fintype (ιq2 σ)]
    [∀ σ, DecidableEq (ιq σ)] [∀ σ, DecidableEq (ιq1 σ)] [∀ σ, DecidableEq (ιq2 σ)]
    (bq : StalkBasisFamily F q ιq)
    (bq1 : StalkBasisFamily F (q + 1) ιq1)
    (bq2 : StalkBasisFamily F (q + 2) ιq2) : Set ℝ :=
  spectrum ℝ <|
    Matrix.toLin' (sheafLaplacianMatrix F (Orientation.sortedOrientation K) q
      ιq ιq1 ιq2 bq bq1 bq2)

end Laplacian

end PersistentSheafLaplacian
end HeytingLean
