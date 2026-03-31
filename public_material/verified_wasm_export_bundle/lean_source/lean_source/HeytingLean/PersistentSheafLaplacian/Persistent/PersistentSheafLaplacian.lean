import HeytingLean.PersistentSheafLaplacian.Persistent.PersistentCoboundary
import HeytingLean.PersistentSheafLaplacian.Cochain.CochainMatrix
import HeytingLean.PersistentSheafLaplacian.Laplacian.SheafLaplacian

namespace HeytingLean
namespace PersistentSheafLaplacian

open SimplicialComplex

namespace Persistent

open Cochain
open Laplacian

variable {V : Type*} [DecidableEq V]
variable {X Y : SimplicialComplex V} (P : PersistentSheafPair X Y)

/-- Matrix coordinates for the transported persistent coboundary. -/
noncomputable def persistentCoboundaryMatrix (q : Nat) (oY : Orientation Y)
    (ιq : StalkIndexFamily (K := X) q)
    (ιq1 : StalkIndexFamily (K := X) (q + 1))
    [∀ σ, Fintype (ιq σ)] [∀ σ, Fintype (ιq1 σ)]
    [∀ σ, DecidableEq (ιq σ)] [∀ σ, DecidableEq (ιq1 σ)]
    (bq : StalkBasisFamily P.F q ιq)
    (bq1 : StalkBasisFamily P.F (q + 1) ιq1) :
    Matrix (Laplacian.CochainCoord (K := X) (q + 1) ιq1)
      (Laplacian.CochainCoord (K := X) q ιq) ℝ :=
  LinearMap.toMatrix (cochainBasis P.F q ιq bq) (cochainBasis P.F (q + 1) ιq1 bq1)
    (P.persistentCoboundary q oY)

/-- Matrix-level persistent Laplacian built from adjacent transported coboundaries. -/
noncomputable def persistentSheafLaplacianMatrix (q : Nat) (oY : Orientation Y)
    (ιq : StalkIndexFamily (K := X) q)
    (ιq1 : StalkIndexFamily (K := X) (q + 1))
    (ιq2 : StalkIndexFamily (K := X) (q + 2))
    [∀ σ, Fintype (ιq σ)] [∀ σ, Fintype (ιq1 σ)] [∀ σ, Fintype (ιq2 σ)]
    [∀ σ, DecidableEq (ιq σ)] [∀ σ, DecidableEq (ιq1 σ)] [∀ σ, DecidableEq (ιq2 σ)]
    (bq : StalkBasisFamily P.F q ιq)
    (bq1 : StalkBasisFamily P.F (q + 1) ιq1)
    (bq2 : StalkBasisFamily P.F (q + 2) ιq2) :
    Matrix (Laplacian.CochainCoord (K := X) (q + 1) ιq1)
      (Laplacian.CochainCoord (K := X) (q + 1) ιq1) ℝ :=
  hodgeLaplacianMatrix
    (persistentCoboundaryMatrix P q oY ιq ιq1 bq bq1)
    (persistentCoboundaryMatrix P (q + 1) oY ιq1 ιq2 bq1 bq2)

/-- Positive semidefiniteness of the transported persistent Laplacian matrix. -/
theorem persistentSheafLaplacianMatrix_posSemidef (q : Nat) (oY : Orientation Y)
    (ιq : StalkIndexFamily (K := X) q)
    (ιq1 : StalkIndexFamily (K := X) (q + 1))
    (ιq2 : StalkIndexFamily (K := X) (q + 2))
    [∀ σ, Fintype (ιq σ)] [∀ σ, Fintype (ιq1 σ)] [∀ σ, Fintype (ιq2 σ)]
    [∀ σ, DecidableEq (ιq σ)] [∀ σ, DecidableEq (ιq1 σ)] [∀ σ, DecidableEq (ιq2 σ)]
    (bq : StalkBasisFamily P.F q ιq)
    (bq1 : StalkBasisFamily P.F (q + 1) ιq1)
    (bq2 : StalkBasisFamily P.F (q + 2) ιq2) :
    (persistentSheafLaplacianMatrix P q oY ιq ιq1 ιq2 bq bq1 bq2).PosSemidef := by
  simpa [persistentSheafLaplacianMatrix] using
    hodgeLaplacianMatrix_posSemidef
      (persistentCoboundaryMatrix P q oY ιq ιq1 bq bq1)
      (persistentCoboundaryMatrix P (q + 1) oY ιq1 ιq2 bq1 bq2)

section SortedReduction

variable [LinearOrder V]

theorem persistentCoboundaryMatrix_eq_coboundaryMatrix_sorted
    (q : Nat) (ιq : StalkIndexFamily (K := X) q)
    (ιq1 : StalkIndexFamily (K := X) (q + 1))
    [∀ σ, Fintype (ιq σ)] [∀ σ, Fintype (ιq1 σ)]
    [∀ σ, DecidableEq (ιq σ)] [∀ σ, DecidableEq (ιq1 σ)]
    (bq : StalkBasisFamily P.F q ιq)
    (bq1 : StalkBasisFamily P.F (q + 1) ιq1) :
    persistentCoboundaryMatrix P q (Orientation.sortedOrientation Y) ιq ιq1 bq bq1 =
      coboundaryMatrix P.F (Orientation.sortedOrientation X) q ιq ιq1 bq bq1 := by
  unfold persistentCoboundaryMatrix Cochain.coboundaryMatrix
  rw [P.persistentCoboundary_eq_coboundary_sorted]

theorem persistentSheafLaplacianMatrix_eq_sheafLaplacianMatrix_sorted
    (q : Nat)
    (ιq : StalkIndexFamily (K := X) q)
    (ιq1 : StalkIndexFamily (K := X) (q + 1))
    (ιq2 : StalkIndexFamily (K := X) (q + 2))
    [∀ σ, Fintype (ιq σ)] [∀ σ, Fintype (ιq1 σ)] [∀ σ, Fintype (ιq2 σ)]
    [∀ σ, DecidableEq (ιq σ)] [∀ σ, DecidableEq (ιq1 σ)] [∀ σ, DecidableEq (ιq2 σ)]
    (bq : StalkBasisFamily P.F q ιq)
    (bq1 : StalkBasisFamily P.F (q + 1) ιq1)
    (bq2 : StalkBasisFamily P.F (q + 2) ιq2) :
    persistentSheafLaplacianMatrix P q (Orientation.sortedOrientation Y) ιq ιq1 ιq2 bq bq1 bq2 =
      sheafLaplacianMatrix P.F (Orientation.sortedOrientation X) q ιq ιq1 ιq2 bq bq1 bq2 := by
  simp [persistentSheafLaplacianMatrix, sheafLaplacianMatrix,
    persistentCoboundaryMatrix_eq_coboundaryMatrix_sorted]

end SortedReduction

end Persistent

end PersistentSheafLaplacian
end HeytingLean
