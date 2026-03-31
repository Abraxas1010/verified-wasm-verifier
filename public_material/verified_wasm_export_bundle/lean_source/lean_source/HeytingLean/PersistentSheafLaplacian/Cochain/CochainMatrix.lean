import HeytingLean.PersistentSheafLaplacian.Cochain.CochainComplex
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace HeytingLean
namespace PersistentSheafLaplacian

open SimplicialComplex

namespace Cochain

variable {V : Type*} [DecidableEq V] {K : SimplicialComplex V}

/-- A family of coordinate index types for the stalks over the `q`-simplices. -/
abbrev StalkIndexFamily {K : SimplicialComplex V} (q : Nat) :=
  K.qSimplices q → Type*

/-- A family of bases for the stalks over the `q`-simplices. -/
abbrev StalkBasisFamily (F : CellularSheaf K) (q : Nat) (ι : StalkIndexFamily (K := K) q) :=
  ∀ σ : K.qSimplices q, Module.Basis (ι σ) ℝ (F.stalkType σ.1)

/-- The induced basis on the `q`-cochain group from the chosen stalk bases. -/
noncomputable def cochainBasis (F : CellularSheaf K) (q : Nat)
    (ι : StalkIndexFamily (K := K) q)
    [∀ σ, Fintype (ι σ)] (b : StalkBasisFamily F q ι) :
    Module.Basis (Σ σ : K.qSimplices q, ι σ) ℝ (CochainGroup F q) :=
  Pi.basis fun σ => b σ

/-- Matrix representation of the sheaf coboundary operator in the chosen stalk bases.
    The index family is dependent because different simplices may carry different stalk dimensions. -/
noncomputable def coboundaryMatrix (F : CellularSheaf K) (o : Orientation K) (q : Nat)
    (ιq : StalkIndexFamily (K := K) q) (ιq1 : StalkIndexFamily (K := K) (q + 1))
    [∀ σ, Fintype (ιq σ)] [∀ τ, Fintype (ιq1 τ)]
    [∀ σ, DecidableEq (ιq σ)] [∀ τ, DecidableEq (ιq1 τ)]
    (bq : StalkBasisFamily F q ιq) (bq1 : StalkBasisFamily F (q + 1) ιq1) :
    Matrix (Σ τ : K.qSimplices (q + 1), ιq1 τ) (Σ σ : K.qSimplices q, ιq σ) ℝ :=
  LinearMap.toMatrix (cochainBasis F q ιq bq) (cochainBasis F (q + 1) ιq1 bq1)
    (coboundary F o q)

/-- The abstract coboundary operator is recovered from its chosen matrix representation. -/
theorem toLin_coboundaryMatrix (F : CellularSheaf K) (o : Orientation K) (q : Nat)
    (ιq : StalkIndexFamily (K := K) q) (ιq1 : StalkIndexFamily (K := K) (q + 1))
    [∀ σ, Fintype (ιq σ)] [∀ τ, Fintype (ιq1 τ)]
    [∀ σ, DecidableEq (ιq σ)] [∀ τ, DecidableEq (ιq1 τ)]
    (bq : StalkBasisFamily F q ιq) (bq1 : StalkBasisFamily F (q + 1) ιq1) :
    Matrix.toLin (cochainBasis F q ιq bq) (cochainBasis F (q + 1) ιq1 bq1)
        (coboundaryMatrix F o q ιq ιq1 bq bq1) =
      coboundary F o q := by
  simp [coboundaryMatrix]

/-- The matrix coordinates of the coboundary are definitionally the coordinates of the
    underlying linear map in the induced cochain bases. -/
theorem coboundaryMatrix_eq_toMatrix (F : CellularSheaf K) (o : Orientation K) (q : Nat)
    (ιq : StalkIndexFamily (K := K) q) (ιq1 : StalkIndexFamily (K := K) (q + 1))
    [∀ σ, Fintype (ιq σ)] [∀ τ, Fintype (ιq1 τ)]
    [∀ σ, DecidableEq (ιq σ)] [∀ τ, DecidableEq (ιq1 τ)]
    (bq : StalkBasisFamily F q ιq) (bq1 : StalkBasisFamily F (q + 1) ιq1) :
    coboundaryMatrix F o q ιq ιq1 bq bq1 =
      LinearMap.toMatrix (cochainBasis F q ιq bq) (cochainBasis F (q + 1) ιq1 bq1)
        (coboundary F o q) :=
  rfl

end Cochain

end PersistentSheafLaplacian
end HeytingLean
