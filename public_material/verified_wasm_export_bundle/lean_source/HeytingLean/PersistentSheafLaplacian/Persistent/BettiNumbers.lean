import HeytingLean.PersistentSheafLaplacian.Persistent.PersistentSheafLaplacian
import HeytingLean.PersistentSheafLaplacian.Laplacian.Spectrum

namespace HeytingLean
namespace PersistentSheafLaplacian

open SimplicialComplex

namespace Persistent

variable {V : Type*} [DecidableEq V]
variable {X Y : SimplicialComplex V} (P : PersistentSheafPair X Y)

/-- Harmonic nullity of the current persistent Laplacian matrix surface. -/
noncomputable def persistentHarmonicNullity (q : Nat) (oY : Orientation Y)
    (ιq : Cochain.StalkIndexFamily (K := X) q)
    (ιq1 : Cochain.StalkIndexFamily (K := X) (q + 1))
    (ιq2 : Cochain.StalkIndexFamily (K := X) (q + 2))
    [∀ σ, Fintype (ιq σ)] [∀ σ, Fintype (ιq1 σ)] [∀ σ, Fintype (ιq2 σ)]
    [∀ σ, DecidableEq (ιq σ)] [∀ σ, DecidableEq (ιq1 σ)] [∀ σ, DecidableEq (ιq2 σ)]
    (bq : Cochain.StalkBasisFamily P.F q ιq)
    (bq1 : Cochain.StalkBasisFamily P.F (q + 1) ιq1)
    (bq2 : Cochain.StalkBasisFamily P.F (q + 2) ιq2) : Nat :=
  Module.finrank ℝ <|
    LinearMap.ker <|
      Matrix.toLin' (Persistent.persistentSheafLaplacianMatrix P q oY ιq ιq1 ιq2 bq bq1 bq2)

section SortedReduction

variable [LinearOrder V]

/-- On the current theorem surface, the persistent cohomological Betti number is the ordinary
sorted-orientation sheaf cohomology rank on the pullback sheaf over `X`. -/
noncomputable def persistentCohomologicalBetti (q : Nat) : Nat :=
  Laplacian.cohomologicalSheafBetti (K := X) P.F (q + 1)

theorem persistentHarmonicNullity_eq_harmonicSheafNullity_sorted
    (q : Nat)
    (ιq : Cochain.StalkIndexFamily (K := X) q)
    (ιq1 : Cochain.StalkIndexFamily (K := X) (q + 1))
    (ιq2 : Cochain.StalkIndexFamily (K := X) (q + 2))
    [∀ σ, Fintype (ιq σ)] [∀ σ, Fintype (ιq1 σ)] [∀ σ, Fintype (ιq2 σ)]
    [∀ σ, DecidableEq (ιq σ)] [∀ σ, DecidableEq (ιq1 σ)] [∀ σ, DecidableEq (ιq2 σ)]
    (bq : Cochain.StalkBasisFamily P.F q ιq)
    (bq1 : Cochain.StalkBasisFamily P.F (q + 1) ιq1)
    (bq2 : Cochain.StalkBasisFamily P.F (q + 2) ιq2) :
    persistentHarmonicNullity P q (Orientation.sortedOrientation Y) ιq ιq1 ιq2 bq bq1 bq2 =
      Laplacian.harmonicSheafNullity (K := X) P.F q ιq ιq1 ιq2 bq bq1 bq2 := by
  unfold persistentHarmonicNullity Laplacian.harmonicSheafNullity
  rw [Persistent.persistentSheafLaplacianMatrix_eq_sheafLaplacianMatrix_sorted
    (P := P) (q := q) (ιq := ιq) (ιq1 := ιq1) (ιq2 := ιq2) (bq := bq) (bq1 := bq1)
    (bq2 := bq2)]

/-- Persistent Betti/nullity theorem on the current sorted-orientation surface. Because the
transported persistent coboundary collapses to the base coboundary on the pullback sheaf, the
persistent Laplacian kernel dimension agrees with the ordinary sheaf cohomology Betti number on
`X`. -/
theorem persistent_betti_eq_nullity (q : Nat)
    (ιq : Cochain.StalkIndexFamily (K := X) q)
    (ιq1 : Cochain.StalkIndexFamily (K := X) (q + 1))
    (ιq2 : Cochain.StalkIndexFamily (K := X) (q + 2))
    [∀ σ, Fintype (ιq σ)] [∀ σ, Fintype (ιq1 σ)] [∀ σ, Fintype (ιq2 σ)]
    [∀ σ, DecidableEq (ιq σ)] [∀ σ, DecidableEq (ιq1 σ)] [∀ σ, DecidableEq (ιq2 σ)]
    (bq : Cochain.StalkBasisFamily P.F q ιq)
    (bq1 : Cochain.StalkBasisFamily P.F (q + 1) ιq1)
    (bq2 : Cochain.StalkBasisFamily P.F (q + 2) ιq2) :
    persistentHarmonicNullity P q (Orientation.sortedOrientation Y) ιq ιq1 ιq2 bq bq1 bq2 =
      persistentCohomologicalBetti P q := by
  rw [persistentHarmonicNullity_eq_harmonicSheafNullity_sorted]
  exact Laplacian.hodge_sheaf (K := X) P.F q ιq ιq1 ιq2 bq bq1 bq2

end SortedReduction

end Persistent

end PersistentSheafLaplacian
end HeytingLean
