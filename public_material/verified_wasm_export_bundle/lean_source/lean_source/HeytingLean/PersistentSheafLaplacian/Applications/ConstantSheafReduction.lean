import HeytingLean.PersistentSheafLaplacian.Laplacian.SheafLaplacian
import Mathlib.LinearAlgebra.Basis.Basic

namespace HeytingLean
namespace PersistentSheafLaplacian

open SimplicialComplex

namespace Applications
namespace ConstantSheafReduction

open Cochain
open Laplacian

variable {V : Type*} [DecidableEq V] {K : SimplicialComplex V}

/-- The canonical one-dimensional stalk index family for scalar constant sheaves. -/
abbrev scalarIndexFamily (q : Nat) : StalkIndexFamily (K := K) q := fun _ => Unit

/-- The canonical scalar stalk basis, sending the unique index to `1 : ℝ`. -/
noncomputable def scalarBasisFamily (q : Nat) :
    StalkBasisFamily (CellularSheaf.constantSheaf K ℝ) q (scalarIndexFamily (K := K) q) :=
  fun _ => Module.Basis.singleton Unit ℝ

/-- Coordinate indices for scalar constant-sheaf matrices. -/
abbrev ScalarCoord (q : Nat) := Laplacian.CochainCoord (K := K) q (scalarIndexFamily (K := K) q)

/-- The standard scalar coboundary on simplicial cochains: signed incidence with no nontrivial
restriction maps. -/
noncomputable def standardCoboundary (o : Orientation K) (q : Nat) :
    (K.qSimplices q → ℝ) →ₗ[ℝ] (K.qSimplices (q + 1) → ℝ) where
  toFun := fun f τ =>
    ∑ σ ∈ (K.qSimplices q).attach,
      if hface : σ.1 ≤ τ.1 then
        (((Orientation.signedIncidence o hface : ℤ) : ℝ) * f σ)
      else
        0
  map_add' f g := by
    classical
    ext τ
    calc
      (∑ σ ∈ (K.qSimplices q).attach,
          if hface : σ.1 ≤ τ.1 then
            (((Orientation.signedIncidence o hface : ℤ) : ℝ) * (f σ + g σ))
          else
            0)
        =
          ∑ σ ∈ (K.qSimplices q).attach,
            ((if hface : σ.1 ≤ τ.1 then
                (((Orientation.signedIncidence o hface : ℤ) : ℝ) * f σ)
              else
                0) +
              (if hface : σ.1 ≤ τ.1 then
                (((Orientation.signedIncidence o hface : ℤ) : ℝ) * g σ)
              else
                0)) := by
          apply Finset.sum_congr rfl
          intro σ hσ
          by_cases hface : σ.1 ≤ τ.1 <;> simp [hface, mul_add]
      _ =
          (∑ σ ∈ (K.qSimplices q).attach,
            if hface : σ.1 ≤ τ.1 then
              (((Orientation.signedIncidence o hface : ℤ) : ℝ) * f σ)
            else
              0) +
          ∑ σ ∈ (K.qSimplices q).attach,
            if hface : σ.1 ≤ τ.1 then
              (((Orientation.signedIncidence o hface : ℤ) : ℝ) * g σ)
            else
              0 := by
          rw [Finset.sum_add_distrib]
  map_smul' a f := by
    classical
    ext τ
    calc
      (∑ σ ∈ (K.qSimplices q).attach,
          if hface : σ.1 ≤ τ.1 then
            (((Orientation.signedIncidence o hface : ℤ) : ℝ) * ((a • f) σ))
          else
            0)
        =
          (∑ σ ∈ (K.qSimplices q).attach,
            a *
              (if hface : σ.1 ≤ τ.1 then
                (((Orientation.signedIncidence o hface : ℤ) : ℝ) * f σ)
              else
                0)) := by
          apply Finset.sum_congr rfl
          intro σ hσ
          by_cases hface : σ.1 ≤ τ.1 <;> simp [hface, mul_left_comm]
      _ = (a *
          ∑ σ ∈ (K.qSimplices q).attach,
            if hface : σ.1 ≤ τ.1 then
              (((Orientation.signedIncidence o hface : ℤ) : ℝ) * f σ)
            else
              0) := by
          rw [Finset.mul_sum]

theorem constantSheaf_coboundary_eq_standardCoboundary
    (o : Orientation K) (q : Nat) :
    Cochain.coboundary (CellularSheaf.constantSheaf K ℝ) o q =
      standardCoboundary (K := K) o q := by
  ext f τ
  simp [Cochain.coboundary, Cochain.faceTerm, standardCoboundary, CellularSheaf.constantSheaf]

/-- The independently defined standard signed-incidence matrix on scalar cochains. -/
noncomputable def standardCoboundaryMatrix (o : Orientation K) (q : Nat) :
    Matrix (ScalarCoord (K := K) (q + 1)) (ScalarCoord (K := K) q) ℝ :=
  LinearMap.toMatrix
    (cochainBasis (CellularSheaf.constantSheaf K ℝ) q
      (scalarIndexFamily (K := K) q) (scalarBasisFamily (K := K) q))
    (cochainBasis (CellularSheaf.constantSheaf K ℝ) (q + 1)
      (scalarIndexFamily (K := K) (q + 1)) (scalarBasisFamily (K := K) (q + 1)))
    (standardCoboundary (K := K) o q)

theorem constantSheaf_coboundaryMatrix_eq_standardCoboundaryMatrix
    (o : Orientation K) (q : Nat) :
    coboundaryMatrix (CellularSheaf.constantSheaf K ℝ) o q
        (scalarIndexFamily (K := K) q) (scalarIndexFamily (K := K) (q + 1))
        (scalarBasisFamily (K := K) q) (scalarBasisFamily (K := K) (q + 1)) =
      standardCoboundaryMatrix (K := K) o q := by
  unfold standardCoboundaryMatrix Cochain.coboundaryMatrix
  rw [constantSheaf_coboundary_eq_standardCoboundary]

/-- The standard scalar Hodge Laplacian built from the independently defined signed-incidence
matrices. -/
noncomputable def standardLaplacianMatrix (o : Orientation K) (q : Nat) :
    Matrix (ScalarCoord (K := K) (q + 1)) (ScalarCoord (K := K) (q + 1)) ℝ :=
  @hodgeLaplacianMatrix
    (ScalarCoord (K := K) q)
    (ScalarCoord (K := K) (q + 1))
    (ScalarCoord (K := K) (q + 2))
    (by infer_instance)
    (by infer_instance)
    (by infer_instance)
    (by infer_instance)
    (by infer_instance)
    (by infer_instance)
    (standardCoboundaryMatrix (K := K) o q)
    (standardCoboundaryMatrix (K := K) o (q + 1))

theorem constantSheaf_sheafLaplacianMatrix_eq_standardLaplacianMatrix
    (o : Orientation K) (q : Nat) :
    sheafLaplacianMatrix (CellularSheaf.constantSheaf K ℝ) o q
        (scalarIndexFamily (K := K) q)
        (scalarIndexFamily (K := K) (q + 1))
        (scalarIndexFamily (K := K) (q + 2))
        (scalarBasisFamily (K := K) q)
        (scalarBasisFamily (K := K) (q + 1))
        (scalarBasisFamily (K := K) (q + 2)) =
      standardLaplacianMatrix (K := K) o q := by
  simp [standardLaplacianMatrix, sheafLaplacianMatrix,
    constantSheaf_coboundaryMatrix_eq_standardCoboundaryMatrix]

end ConstantSheafReduction
end Applications

end PersistentSheafLaplacian
end HeytingLean
