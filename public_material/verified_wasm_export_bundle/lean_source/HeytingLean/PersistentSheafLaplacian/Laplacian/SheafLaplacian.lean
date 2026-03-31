import HeytingLean.PersistentSheafLaplacian.Cochain.CochainMatrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace HeytingLean
namespace PersistentSheafLaplacian

open SimplicialComplex

namespace Laplacian

open Cochain

variable {V : Type*} [DecidableEq V] {K : SimplicialComplex V}

/-- The coordinate index type for the `q`-cochain group induced by a stalk index family. -/
abbrev CochainCoord (q : Nat) (ι : StalkIndexFamily (K := K) q) :=
  Σ σ : K.qSimplices q, ι σ

/-- Generic Hodge-Laplacian matrix `D_qᵀ D_q + D_{q-1} D_{q-1}ᵀ`. -/
noncomputable def hodgeLaplacianMatrix {ιPrev ι ιNext : Type*}
    [Fintype ιPrev] [Fintype ι] [Fintype ιNext]
    [DecidableEq ιPrev] [DecidableEq ι] [DecidableEq ιNext]
    (dPrev : Matrix ι ιPrev ℝ) (dNext : Matrix ιNext ι ℝ) : Matrix ι ι ℝ :=
  Matrix.transpose dNext * dNext + dPrev * Matrix.transpose dPrev

/-- The Hodge-Laplacian matrix is positive semidefinite. -/
theorem hodgeLaplacianMatrix_posSemidef {ιPrev ι ιNext : Type*}
    [Fintype ιPrev] [Fintype ι] [Fintype ιNext]
    [DecidableEq ιPrev] [DecidableEq ι] [DecidableEq ιNext]
    (dPrev : Matrix ι ιPrev ℝ) (dNext : Matrix ιNext ι ℝ) :
    (hodgeLaplacianMatrix dPrev dNext).PosSemidef := by
  have hUpper : (Matrix.transpose dNext * dNext).PosSemidef := by
    simpa [Matrix.conjTranspose, mul_assoc] using
      (Matrix.PosSemidef.conjTranspose_mul_mul_same (A := (1 : Matrix _ _ ℝ))
        Matrix.PosSemidef.one dNext)
  have hLower : (dPrev * Matrix.transpose dPrev).PosSemidef := by
    simpa [Matrix.conjTranspose, mul_assoc] using
      (Matrix.PosSemidef.mul_mul_conjTranspose_same (A := (1 : Matrix _ _ ℝ))
        Matrix.PosSemidef.one dPrev)
  simpa [hodgeLaplacianMatrix] using hUpper.add hLower

/-- Canonical sheaf Laplacian matrix at degree `q + 1`, using the actual adjacent coboundary
    matrices on both sides. -/
noncomputable def sheafLaplacianMatrix (F : CellularSheaf K) (o : Orientation K) (q : Nat)
    (ιq : StalkIndexFamily (K := K) q)
    (ιq1 : StalkIndexFamily (K := K) (q + 1))
    (ιq2 : StalkIndexFamily (K := K) (q + 2))
    [∀ σ, Fintype (ιq σ)] [∀ σ, Fintype (ιq1 σ)] [∀ σ, Fintype (ιq2 σ)]
    [∀ σ, DecidableEq (ιq σ)] [∀ σ, DecidableEq (ιq1 σ)] [∀ σ, DecidableEq (ιq2 σ)]
    (bq : StalkBasisFamily F q ιq)
    (bq1 : StalkBasisFamily F (q + 1) ιq1)
    (bq2 : StalkBasisFamily F (q + 2) ιq2) :
    Matrix (CochainCoord (K := K) (q + 1) ιq1) (CochainCoord (K := K) (q + 1) ιq1) ℝ :=
  hodgeLaplacianMatrix
    (coboundaryMatrix F o q ιq ιq1 bq bq1)
    (coboundaryMatrix F o (q + 1) ιq1 ιq2 bq1 bq2)

/-- Positivity of the canonical sheaf Laplacian matrix built from the actual adjacent
    coboundary matrices. -/
theorem sheafLaplacianMatrix_posSemidef (F : CellularSheaf K) (o : Orientation K) (q : Nat)
    (ιq : StalkIndexFamily (K := K) q)
    (ιq1 : StalkIndexFamily (K := K) (q + 1))
    (ιq2 : StalkIndexFamily (K := K) (q + 2))
    [∀ σ, Fintype (ιq σ)] [∀ σ, Fintype (ιq1 σ)] [∀ σ, Fintype (ιq2 σ)]
    [∀ σ, DecidableEq (ιq σ)] [∀ σ, DecidableEq (ιq1 σ)] [∀ σ, DecidableEq (ιq2 σ)]
    (bq : StalkBasisFamily F q ιq)
    (bq1 : StalkBasisFamily F (q + 1) ιq1)
    (bq2 : StalkBasisFamily F (q + 2) ιq2) :
    (sheafLaplacianMatrix F o q ιq ιq1 ιq2 bq bq1 bq2).PosSemidef := by
  simpa [sheafLaplacianMatrix] using
    hodgeLaplacianMatrix_posSemidef
      (coboundaryMatrix F o q ιq ιq1 bq bq1)
      (coboundaryMatrix F o (q + 1) ιq1 ιq2 bq1 bq2)

end Laplacian

end PersistentSheafLaplacian
end HeytingLean
