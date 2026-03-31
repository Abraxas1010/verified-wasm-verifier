import HeytingLean.PersistentSheafLaplacian.Laplacian.Spectrum
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

namespace HeytingLean
namespace PersistentSheafLaplacian

open SimplicialComplex

namespace Laplacian

open Cochain

variable {V : Type*} [DecidableEq V] {K : SimplicialComplex V}

noncomputable def orientationCoordSign (o₁ o₂ : Orientation K) (q : Nat)
    (ι : StalkIndexFamily (K := K) q) (i : CochainCoord (K := K) q ι) : ℝ :=
  (Orientation.orientationSimplexSign o₁ o₂ i.1.1 : ℝ)

noncomputable def orientationSignMatrix (o₁ o₂ : Orientation K) (q : Nat)
    (ι : StalkIndexFamily (K := K) q) [∀ σ, DecidableEq (ι σ)] :
    Matrix (CochainCoord (K := K) q ι) (CochainCoord (K := K) q ι) ℝ :=
  Matrix.diagonal (orientationCoordSign (K := K) o₁ o₂ q ι)

private theorem orientationCoordSign_mul_self (o₁ o₂ : Orientation K) (q : Nat)
    (ι : StalkIndexFamily (K := K) q) (i : CochainCoord (K := K) q ι) :
    orientationCoordSign (K := K) o₁ o₂ q ι i *
      orientationCoordSign (K := K) o₁ o₂ q ι i = 1 := by
  unfold orientationCoordSign
  have hInt :
      (((Orientation.orientationSimplexSignUnit o₁ o₂ i.1.1 : ℤˣ) : ℤ) *
          ((Orientation.orientationSimplexSignUnit o₁ o₂ i.1.1 : ℤˣ) : ℤ)) = 1 := by
    change (((Orientation.orientationSimplexSignUnit o₁ o₂ i.1.1 : ℤˣ) *
        Orientation.orientationSimplexSignUnit o₁ o₂ i.1.1 : ℤˣ) : ℤ) = 1
    rw [Int.units_mul_self]
    simp
  exact_mod_cast hInt

theorem orientationSignMatrix_mul_self (o₁ o₂ : Orientation K) (q : Nat)
    (ι : StalkIndexFamily (K := K) q)
    [∀ σ, Fintype (ι σ)] [∀ σ, DecidableEq (ι σ)] :
    orientationSignMatrix (K := K) o₁ o₂ q ι *
      orientationSignMatrix (K := K) o₁ o₂ q ι = 1 := by
  classical
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [orientationSignMatrix, Matrix.diagonal_mul_diagonal]
    simp [orientationCoordSign_mul_self]
  · simp [orientationSignMatrix, hij]

theorem orientationSignMatrix_transpose (o₁ o₂ : Orientation K) (q : Nat)
    (ι : StalkIndexFamily (K := K) q) [∀ σ, DecidableEq (ι σ)] :
    Matrix.transpose (orientationSignMatrix (K := K) o₁ o₂ q ι) =
      orientationSignMatrix (K := K) o₁ o₂ q ι := by
  classical
  simp [orientationSignMatrix]

noncomputable def orientationSignMatrixUnit (o₁ o₂ : Orientation K) (q : Nat)
    (ι : StalkIndexFamily (K := K) q)
    [∀ σ, Fintype (ι σ)] [∀ σ, DecidableEq (ι σ)] :
    (Matrix (CochainCoord (K := K) q ι) (CochainCoord (K := K) q ι) ℝ)ˣ where
  val := orientationSignMatrix (K := K) o₁ o₂ q ι
  inv := orientationSignMatrix (K := K) o₁ o₂ q ι
  val_inv := orientationSignMatrix_mul_self (K := K) o₁ o₂ q ι
  inv_val := orientationSignMatrix_mul_self (K := K) o₁ o₂ q ι

noncomputable def orientationSignLinearEquiv (o₁ o₂ : Orientation K) (q : Nat)
    (ι : StalkIndexFamily (K := K) q)
    [∀ σ, Fintype (ι σ)] [∀ σ, DecidableEq (ι σ)] :
    ((CochainCoord (K := K) q ι) → ℝ) ≃ₗ[ℝ] (CochainCoord (K := K) q ι) → ℝ :=
  Matrix.toLin'OfInv
    (orientationSignMatrix_mul_self (K := K) o₁ o₂ q ι)
    (orientationSignMatrix_mul_self (K := K) o₁ o₂ q ι)

@[simp] theorem orientationSignLinearEquiv_apply (o₁ o₂ : Orientation K) (q : Nat)
    (ι : StalkIndexFamily (K := K) q)
    [∀ σ, Fintype (ι σ)] [∀ σ, DecidableEq (ι σ)]
    (x : (CochainCoord (K := K) q ι) → ℝ) :
    orientationSignLinearEquiv (K := K) o₁ o₂ q ι x =
      Matrix.toLin' (orientationSignMatrix (K := K) o₁ o₂ q ι) x := rfl

@[simp] theorem orientationSignLinearEquiv_symm_apply (o₁ o₂ : Orientation K) (q : Nat)
    (ι : StalkIndexFamily (K := K) q)
    [∀ σ, Fintype (ι σ)] [∀ σ, DecidableEq (ι σ)]
    (x : (CochainCoord (K := K) q ι) → ℝ) :
    (orientationSignLinearEquiv (K := K) o₁ o₂ q ι).symm x =
      Matrix.toLin' (orientationSignMatrix (K := K) o₁ o₂ q ι) x := rfl

theorem coboundaryMatrix_orientationSign_conj
    (F : CellularSheaf K) (o₁ o₂ : Orientation K) (q : Nat)
    (ιq : StalkIndexFamily (K := K) q)
    (ιq1 : StalkIndexFamily (K := K) (q + 1))
    [∀ σ, Fintype (ιq σ)] [∀ τ, Fintype (ιq1 τ)]
    [∀ σ, DecidableEq (ιq σ)] [∀ τ, DecidableEq (ιq1 τ)]
    (bq : StalkBasisFamily F q ιq) (bq1 : StalkBasisFamily F (q + 1) ιq1) :
    coboundaryMatrix F o₁ q ιq ιq1 bq bq1 =
      orientationSignMatrix (K := K) o₁ o₂ (q + 1) ιq1 *
        coboundaryMatrix F o₂ q ιq ιq1 bq bq1 *
        orientationSignMatrix (K := K) o₁ o₂ q ιq := by
  classical
  ext r c
  by_cases hface : c.1.1 ≤ r.1.1
  · have hdiag :
        (orientationSignMatrix (K := K) o₁ o₂ (q + 1) ιq1 *
            coboundaryMatrix F o₂ q ιq ιq1 bq bq1 *
            orientationSignMatrix (K := K) o₁ o₂ q ιq) r c =
          orientationCoordSign (K := K) o₁ o₂ (q + 1) ιq1 r *
            (coboundaryMatrix F o₂ q ιq ιq1 bq bq1) r c *
            orientationCoordSign (K := K) o₁ o₂ q ιq c := by
      simp [orientationSignMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_assoc]
    rw [hdiag]
    rw [coboundaryMatrix_eq_toMatrix, LinearMap.toMatrix_apply,
      coboundaryMatrix_eq_toMatrix, LinearMap.toMatrix_apply]
    have hs0 :
        (((Orientation.signedIncidence o₁ hface : ℤ) : ℝ)) =
          orientationCoordSign (K := K) o₁ o₂ (q + 1) ιq1 r *
            orientationCoordSign (K := K) o₁ o₂ q ιq c *
            (((Orientation.signedIncidence o₂ hface : ℤ) : ℝ)) := by
      have hs0' := congrArg (fun z : ℤ => (z : ℝ))
        (Orientation.signedIncidence_eq_orientationSimplexSign_mul_of_qface
          (K := K) (o₁ := o₁) (o₂ := o₂) (hστ := hface))
      simpa [orientationCoordSign, mul_assoc] using hs0'
    have hs :
        (((Orientation.signedIncidence o₁ hface : ℤ) : ℝ)) =
          orientationCoordSign (K := K) o₁ o₂ (q + 1) ιq1 r *
            (((Orientation.signedIncidence o₂ hface : ℤ) : ℝ)) *
            orientationCoordSign (K := K) o₁ o₂ q ιq c := by
      calc
        (((Orientation.signedIncidence o₁ hface : ℤ) : ℝ)) =
            orientationCoordSign (K := K) o₁ o₂ (q + 1) ιq1 r *
              orientationCoordSign (K := K) o₁ o₂ q ιq c *
              (((Orientation.signedIncidence o₂ hface : ℤ) : ℝ)) := hs0
        _ = orientationCoordSign (K := K) o₁ o₂ (q + 1) ιq1 r *
              (((Orientation.signedIncidence o₂ hface : ℤ) : ℝ)) *
              orientationCoordSign (K := K) o₁ o₂ q ιq c := by ring
    simpa [cochainBasis, coboundary_piSingle, hface, hs, smul_smul,
      mul_assoc, mul_left_comm, mul_comm]
  · have hdiag :
        (orientationSignMatrix (K := K) o₁ o₂ (q + 1) ιq1 *
            coboundaryMatrix F o₂ q ιq ιq1 bq bq1 *
            orientationSignMatrix (K := K) o₁ o₂ q ιq) r c =
          orientationCoordSign (K := K) o₁ o₂ (q + 1) ιq1 r *
            (coboundaryMatrix F o₂ q ιq ιq1 bq bq1) r c *
            orientationCoordSign (K := K) o₁ o₂ q ιq c := by
      simp [orientationSignMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_assoc]
    rw [hdiag]
    rw [coboundaryMatrix_eq_toMatrix, LinearMap.toMatrix_apply,
      coboundaryMatrix_eq_toMatrix, LinearMap.toMatrix_apply]
    simp [cochainBasis, coboundary_piSingle, hface]

private theorem hodgeLaplacianMatrix_conj {ιPrev ι ιNext : Type*}
    [Fintype ιPrev] [Fintype ι] [Fintype ιNext]
    [DecidableEq ιPrev] [DecidableEq ι] [DecidableEq ιNext]
    (Sprev : Matrix ιPrev ιPrev ℝ) (S : Matrix ι ι ℝ) (Snext : Matrix ιNext ιNext ℝ)
    (hSprevT : Matrix.transpose Sprev = Sprev)
    (hST : Matrix.transpose S = S)
    (hSnextT : Matrix.transpose Snext = Snext)
    (hSprev : Sprev * Sprev = 1)
    (hSnext : Snext * Snext = 1)
    (dPrev : Matrix ι ιPrev ℝ) (dNext : Matrix ιNext ι ℝ) :
    hodgeLaplacianMatrix (S * dPrev * Sprev) (Snext * dNext * S) =
      S * hodgeLaplacianMatrix dPrev dNext * S := by
  unfold hodgeLaplacianMatrix
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hST, hSnextT]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hSprevT, hST]
  calc
    S * (dNext.transpose * Snext) * (Snext * dNext * S) +
        S * dPrev * Sprev * (Sprev * (dPrev.transpose * S)) =
      S * (dNext.transpose * (Snext * Snext) * dNext * S) +
        S * dPrev * (Sprev * Sprev) * (dPrev.transpose * S) := by
          simp [Matrix.mul_assoc]
    _ = S * (dNext.transpose * dNext * S) + S * dPrev * dPrev.transpose * S := by
          rw [hSnext, hSprev]
          simp [Matrix.mul_assoc]
    _ = S * (dNext.transpose * dNext + dPrev * dPrev.transpose) * S := by
          simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

theorem sheafLaplacianMatrix_orientationSign_conj
    (F : CellularSheaf K) (o₁ o₂ : Orientation K) (q : Nat)
    (ιq : StalkIndexFamily (K := K) q)
    (ιq1 : StalkIndexFamily (K := K) (q + 1))
    (ιq2 : StalkIndexFamily (K := K) (q + 2))
    [∀ σ, Fintype (ιq σ)] [∀ σ, Fintype (ιq1 σ)] [∀ σ, Fintype (ιq2 σ)]
    [∀ σ, DecidableEq (ιq σ)] [∀ σ, DecidableEq (ιq1 σ)] [∀ σ, DecidableEq (ιq2 σ)]
    (bq : StalkBasisFamily F q ιq)
    (bq1 : StalkBasisFamily F (q + 1) ιq1)
    (bq2 : StalkBasisFamily F (q + 2) ιq2) :
    sheafLaplacianMatrix F o₁ q ιq ιq1 ιq2 bq bq1 bq2 =
      orientationSignMatrix (K := K) o₁ o₂ (q + 1) ιq1 *
        sheafLaplacianMatrix F o₂ q ιq ιq1 ιq2 bq bq1 bq2 *
        orientationSignMatrix (K := K) o₁ o₂ (q + 1) ιq1 := by
  let S0 := orientationSignMatrix (K := K) o₁ o₂ q ιq
  let S1 := orientationSignMatrix (K := K) o₁ o₂ (q + 1) ιq1
  let S2 := orientationSignMatrix (K := K) o₁ o₂ (q + 2) ιq2
  let d0 := coboundaryMatrix F o₂ q ιq ιq1 bq bq1
  let d1 := coboundaryMatrix F o₂ (q + 1) ιq1 ιq2 bq1 bq2
  rw [sheafLaplacianMatrix, sheafLaplacianMatrix]
  rw [coboundaryMatrix_orientationSign_conj (K := K) F o₁ o₂ q ιq ιq1 bq bq1]
  rw [coboundaryMatrix_orientationSign_conj (K := K) F o₁ o₂ (q + 1) ιq1 ιq2 bq1 bq2]
  simpa [S0, S1, S2, d0, d1, sheafLaplacianMatrix] using
    hodgeLaplacianMatrix_conj
      (Sprev := S0) (S := S1) (Snext := S2)
      (hSprevT := orientationSignMatrix_transpose (K := K) o₁ o₂ q ιq)
      (hST := orientationSignMatrix_transpose (K := K) o₁ o₂ (q + 1) ιq1)
      (hSnextT := orientationSignMatrix_transpose (K := K) o₁ o₂ (q + 2) ιq2)
      (hSprev := orientationSignMatrix_mul_self (K := K) o₁ o₂ q ιq)
      (hSnext := orientationSignMatrix_mul_self (K := K) o₁ o₂ (q + 2) ιq2)
      d0 d1

private theorem sheafLaplacianMatrix_comm_right
    (F : CellularSheaf K) (o₁ o₂ : Orientation K) (q : Nat)
    (ιq : StalkIndexFamily (K := K) q)
    (ιq1 : StalkIndexFamily (K := K) (q + 1))
    (ιq2 : StalkIndexFamily (K := K) (q + 2))
    [∀ σ, Fintype (ιq σ)] [∀ σ, Fintype (ιq1 σ)] [∀ σ, Fintype (ιq2 σ)]
    [∀ σ, DecidableEq (ιq σ)] [∀ σ, DecidableEq (ιq1 σ)] [∀ σ, DecidableEq (ιq2 σ)]
    (bq : StalkBasisFamily F q ιq)
    (bq1 : StalkBasisFamily F (q + 1) ιq1)
    (bq2 : StalkBasisFamily F (q + 2) ιq2) :
    sheafLaplacianMatrix F o₂ q ιq ιq1 ιq2 bq bq1 bq2 *
        orientationSignMatrix (K := K) o₁ o₂ (q + 1) ιq1 =
      orientationSignMatrix (K := K) o₁ o₂ (q + 1) ιq1 *
        sheafLaplacianMatrix F o₁ q ιq ιq1 ιq2 bq bq1 bq2 := by
  calc
    sheafLaplacianMatrix F o₂ q ιq ιq1 ιq2 bq bq1 bq2 *
        orientationSignMatrix (K := K) o₁ o₂ (q + 1) ιq1 =
      (1 : Matrix (CochainCoord (K := K) (q + 1) ιq1)
          (CochainCoord (K := K) (q + 1) ιq1) ℝ) *
        (sheafLaplacianMatrix F o₂ q ιq ιq1 ιq2 bq bq1 bq2 *
          orientationSignMatrix (K := K) o₁ o₂ (q + 1) ιq1) := by simp
    _ =
      (orientationSignMatrix (K := K) o₁ o₂ (q + 1) ιq1 *
          orientationSignMatrix (K := K) o₁ o₂ (q + 1) ιq1) *
        (sheafLaplacianMatrix F o₂ q ιq ιq1 ιq2 bq bq1 bq2 *
          orientationSignMatrix (K := K) o₁ o₂ (q + 1) ιq1) := by
            rw [orientationSignMatrix_mul_self (K := K) o₁ o₂ (q + 1) ιq1]
    _ =
      orientationSignMatrix (K := K) o₁ o₂ (q + 1) ιq1 *
        (orientationSignMatrix (K := K) o₁ o₂ (q + 1) ιq1 *
          sheafLaplacianMatrix F o₂ q ιq ιq1 ιq2 bq bq1 bq2 *
          orientationSignMatrix (K := K) o₁ o₂ (q + 1) ιq1) := by
            simp [Matrix.mul_assoc]
    _ =
      orientationSignMatrix (K := K) o₁ o₂ (q + 1) ιq1 *
        sheafLaplacianMatrix F o₁ q ιq ιq1 ιq2 bq bq1 bq2 := by
            rw [← sheafLaplacianMatrix_orientationSign_conj (K := K) F o₁ o₂ q
              ιq ιq1 ιq2 bq bq1 bq2]

private theorem sheafLaplacianMatrix_comm_left
    (F : CellularSheaf K) (o₁ o₂ : Orientation K) (q : Nat)
    (ιq : StalkIndexFamily (K := K) q)
    (ιq1 : StalkIndexFamily (K := K) (q + 1))
    (ιq2 : StalkIndexFamily (K := K) (q + 2))
    [∀ σ, Fintype (ιq σ)] [∀ σ, Fintype (ιq1 σ)] [∀ σ, Fintype (ιq2 σ)]
    [∀ σ, DecidableEq (ιq σ)] [∀ σ, DecidableEq (ιq1 σ)] [∀ σ, DecidableEq (ιq2 σ)]
    (bq : StalkBasisFamily F q ιq)
    (bq1 : StalkBasisFamily F (q + 1) ιq1)
    (bq2 : StalkBasisFamily F (q + 2) ιq2) :
    sheafLaplacianMatrix F o₁ q ιq ιq1 ιq2 bq bq1 bq2 *
        orientationSignMatrix (K := K) o₁ o₂ (q + 1) ιq1 =
      orientationSignMatrix (K := K) o₁ o₂ (q + 1) ιq1 *
        sheafLaplacianMatrix F o₂ q ιq ιq1 ιq2 bq bq1 bq2 := by
  calc
    sheafLaplacianMatrix F o₁ q ιq ιq1 ιq2 bq bq1 bq2 *
        orientationSignMatrix (K := K) o₁ o₂ (q + 1) ιq1 =
      (orientationSignMatrix (K := K) o₁ o₂ (q + 1) ιq1 *
          sheafLaplacianMatrix F o₂ q ιq ιq1 ιq2 bq bq1 bq2 *
          orientationSignMatrix (K := K) o₁ o₂ (q + 1) ιq1) *
        orientationSignMatrix (K := K) o₁ o₂ (q + 1) ιq1 := by
            rw [sheafLaplacianMatrix_orientationSign_conj (K := K) F o₁ o₂ q
              ιq ιq1 ιq2 bq bq1 bq2]
    _ =
      orientationSignMatrix (K := K) o₁ o₂ (q + 1) ιq1 *
        sheafLaplacianMatrix F o₂ q ιq ιq1 ιq2 bq bq1 bq2 *
        (orientationSignMatrix (K := K) o₁ o₂ (q + 1) ιq1 *
          orientationSignMatrix (K := K) o₁ o₂ (q + 1) ιq1) := by
            simp [Matrix.mul_assoc]
    _ =
      orientationSignMatrix (K := K) o₁ o₂ (q + 1) ιq1 *
        sheafLaplacianMatrix F o₂ q ιq ιq1 ιq2 bq bq1 bq2 := by
            rw [orientationSignMatrix_mul_self (K := K) o₁ o₂ (q + 1) ιq1]
            simp [Matrix.mul_assoc]

private theorem sheafLaplacian_apply_orientationSign
    (F : CellularSheaf K) (o₁ o₂ : Orientation K) (q : Nat)
    (ιq : StalkIndexFamily (K := K) q)
    (ιq1 : StalkIndexFamily (K := K) (q + 1))
    (ιq2 : StalkIndexFamily (K := K) (q + 2))
    [∀ σ, Fintype (ιq σ)] [∀ σ, Fintype (ιq1 σ)] [∀ σ, Fintype (ιq2 σ)]
    [∀ σ, DecidableEq (ιq σ)] [∀ σ, DecidableEq (ιq1 σ)] [∀ σ, DecidableEq (ιq2 σ)]
    (bq : StalkBasisFamily F q ιq)
    (bq1 : StalkBasisFamily F (q + 1) ιq1)
    (bq2 : StalkBasisFamily F (q + 2) ιq2)
    (x : (CochainCoord (K := K) (q + 1) ιq1) → ℝ) :
    Matrix.toLin' (sheafLaplacianMatrix F o₂ q ιq ιq1 ιq2 bq bq1 bq2)
        (orientationSignLinearEquiv (K := K) o₁ o₂ (q + 1) ιq1 x) =
      orientationSignLinearEquiv (K := K) o₁ o₂ (q + 1) ιq1
        (Matrix.toLin' (sheafLaplacianMatrix F o₁ q ιq ιq1 ιq2 bq bq1 bq2) x) := by
  rw [orientationSignLinearEquiv_apply, ← Matrix.toLin'_mul_apply,
    sheafLaplacianMatrix_comm_right (K := K) F o₁ o₂ q ιq ιq1 ιq2 bq bq1 bq2,
    Matrix.toLin'_mul_apply, orientationSignLinearEquiv_apply]

private theorem sheafLaplacian_apply_orientationSign_symm
    (F : CellularSheaf K) (o₁ o₂ : Orientation K) (q : Nat)
    (ιq : StalkIndexFamily (K := K) q)
    (ιq1 : StalkIndexFamily (K := K) (q + 1))
    (ιq2 : StalkIndexFamily (K := K) (q + 2))
    [∀ σ, Fintype (ιq σ)] [∀ σ, Fintype (ιq1 σ)] [∀ σ, Fintype (ιq2 σ)]
    [∀ σ, DecidableEq (ιq σ)] [∀ σ, DecidableEq (ιq1 σ)] [∀ σ, DecidableEq (ιq2 σ)]
    (bq : StalkBasisFamily F q ιq)
    (bq1 : StalkBasisFamily F (q + 1) ιq1)
    (bq2 : StalkBasisFamily F (q + 2) ιq2)
    (x : (CochainCoord (K := K) (q + 1) ιq1) → ℝ) :
    Matrix.toLin' (sheafLaplacianMatrix F o₁ q ιq ιq1 ιq2 bq bq1 bq2)
        (orientationSignLinearEquiv (K := K) o₁ o₂ (q + 1) ιq1 x) =
      orientationSignLinearEquiv (K := K) o₁ o₂ (q + 1) ιq1
        (Matrix.toLin' (sheafLaplacianMatrix F o₂ q ιq ιq1 ιq2 bq bq1 bq2) x) := by
  rw [orientationSignLinearEquiv_apply, ← Matrix.toLin'_mul_apply,
    sheafLaplacianMatrix_comm_left (K := K) F o₁ o₂ q ιq ιq1 ιq2 bq bq1 bq2,
    Matrix.toLin'_mul_apply, orientationSignLinearEquiv_apply]

noncomputable def sheafLaplacianKerEquiv
    (F : CellularSheaf K) (o₁ o₂ : Orientation K) (q : Nat)
    (ιq : StalkIndexFamily (K := K) q)
    (ιq1 : StalkIndexFamily (K := K) (q + 1))
    (ιq2 : StalkIndexFamily (K := K) (q + 2))
    [∀ σ, Fintype (ιq σ)] [∀ σ, Fintype (ιq1 σ)] [∀ σ, Fintype (ιq2 σ)]
    [∀ σ, DecidableEq (ιq σ)] [∀ σ, DecidableEq (ιq1 σ)] [∀ σ, DecidableEq (ιq2 σ)]
    (bq : StalkBasisFamily F q ιq)
    (bq1 : StalkBasisFamily F (q + 1) ιq1)
    (bq2 : StalkBasisFamily F (q + 2) ιq2) :
    LinearMap.ker (Matrix.toLin' (sheafLaplacianMatrix F o₁ q ιq ιq1 ιq2 bq bq1 bq2)) ≃ₗ[ℝ]
      LinearMap.ker (Matrix.toLin' (sheafLaplacianMatrix F o₂ q ιq ιq1 ιq2 bq bq1 bq2)) where
  toFun x := by
    refine ⟨orientationSignLinearEquiv (K := K) o₁ o₂ (q + 1) ιq1 x.1, ?_⟩
    change Matrix.toLin' (sheafLaplacianMatrix F o₂ q ιq ιq1 ιq2 bq bq1 bq2)
        (orientationSignLinearEquiv (K := K) o₁ o₂ (q + 1) ιq1 x.1) = 0
    rw [sheafLaplacian_apply_orientationSign (K := K) F o₁ o₂ q ιq ιq1 ιq2 bq bq1 bq2]
    simpa using congrArg
      (orientationSignLinearEquiv (K := K) o₁ o₂ (q + 1) ιq1) x.2
  invFun x := by
    refine ⟨orientationSignLinearEquiv (K := K) o₁ o₂ (q + 1) ιq1 x.1, ?_⟩
    change Matrix.toLin' (sheafLaplacianMatrix F o₁ q ιq ιq1 ιq2 bq bq1 bq2)
        (orientationSignLinearEquiv (K := K) o₁ o₂ (q + 1) ιq1 x.1) = 0
    rw [sheafLaplacian_apply_orientationSign_symm (K := K) F o₁ o₂ q ιq ιq1 ιq2 bq bq1 bq2]
    simpa using congrArg
      (orientationSignLinearEquiv (K := K) o₁ o₂ (q + 1) ιq1) x.2
  left_inv x := by
    apply Subtype.ext
    exact (orientationSignLinearEquiv (K := K) o₁ o₂ (q + 1) ιq1).left_inv x.1
  right_inv x := by
    apply Subtype.ext
    exact (orientationSignLinearEquiv (K := K) o₁ o₂ (q + 1) ιq1).right_inv x.1
  map_add' x y := by
    apply Subtype.ext
    exact (orientationSignLinearEquiv (K := K) o₁ o₂ (q + 1) ιq1).map_add x.1 y.1
  map_smul' a x := by
    apply Subtype.ext
    exact (orientationSignLinearEquiv (K := K) o₁ o₂ (q + 1) ιq1).map_smul a x.1

theorem finrank_ker_sheafLaplacianMatrix_eq
    (F : CellularSheaf K) (o₁ o₂ : Orientation K) (q : Nat)
    (ιq : StalkIndexFamily (K := K) q)
    (ιq1 : StalkIndexFamily (K := K) (q + 1))
    (ιq2 : StalkIndexFamily (K := K) (q + 2))
    [∀ σ, Fintype (ιq σ)] [∀ σ, Fintype (ιq1 σ)] [∀ σ, Fintype (ιq2 σ)]
    [∀ σ, DecidableEq (ιq σ)] [∀ σ, DecidableEq (ιq1 σ)] [∀ σ, DecidableEq (ιq2 σ)]
    (bq : StalkBasisFamily F q ιq)
    (bq1 : StalkBasisFamily F (q + 1) ιq1)
    (bq2 : StalkBasisFamily F (q + 2) ιq2) :
    Module.finrank ℝ
        (LinearMap.ker (Matrix.toLin' (sheafLaplacianMatrix F o₁ q ιq ιq1 ιq2 bq bq1 bq2))) =
      Module.finrank ℝ
        (LinearMap.ker (Matrix.toLin' (sheafLaplacianMatrix F o₂ q ιq ιq1 ιq2 bq bq1 bq2))) := by
  simpa using
    LinearEquiv.finrank_eq
      (sheafLaplacianKerEquiv (K := K) F o₁ o₂ q ιq ιq1 ιq2 bq bq1 bq2)

theorem sheafLaplacianMatrix_charpoly_eq
    (F : CellularSheaf K) (o₁ o₂ : Orientation K) (q : Nat)
    (ιq : StalkIndexFamily (K := K) q)
    (ιq1 : StalkIndexFamily (K := K) (q + 1))
    (ιq2 : StalkIndexFamily (K := K) (q + 2))
    [∀ σ, Fintype (ιq σ)] [∀ σ, Fintype (ιq1 σ)] [∀ σ, Fintype (ιq2 σ)]
    [∀ σ, DecidableEq (ιq σ)] [∀ σ, DecidableEq (ιq1 σ)] [∀ σ, DecidableEq (ιq2 σ)]
    (bq : StalkBasisFamily F q ιq)
    (bq1 : StalkBasisFamily F (q + 1) ιq1)
    (bq2 : StalkBasisFamily F (q + 2) ιq2) :
    (sheafLaplacianMatrix F o₁ q ιq ιq1 ιq2 bq bq1 bq2).charpoly =
      (sheafLaplacianMatrix F o₂ q ιq ιq1 ιq2 bq bq1 bq2).charpoly := by
  let S := orientationSignMatrixUnit (K := K) o₁ o₂ (q + 1) ιq1
  rw [sheafLaplacianMatrix_orientationSign_conj (K := K) F o₁ o₂ q ιq ιq1 ιq2 bq bq1 bq2]
  simpa [S, orientationSignMatrixUnit] using
    (Matrix.charpoly_units_conj S
      (sheafLaplacianMatrix F o₂ q ιq ιq1 ιq2 bq bq1 bq2))

theorem sheafLaplacianMatrix_spectrum_eq
    (F : CellularSheaf K) (o₁ o₂ : Orientation K) (q : Nat)
    (ιq : StalkIndexFamily (K := K) q)
    (ιq1 : StalkIndexFamily (K := K) (q + 1))
    (ιq2 : StalkIndexFamily (K := K) (q + 2))
    [∀ σ, Fintype (ιq σ)] [∀ σ, Fintype (ιq1 σ)] [∀ σ, Fintype (ιq2 σ)]
    [∀ σ, DecidableEq (ιq σ)] [∀ σ, DecidableEq (ιq1 σ)] [∀ σ, DecidableEq (ιq2 σ)]
    (bq : StalkBasisFamily F q ιq)
    (bq1 : StalkBasisFamily F (q + 1) ιq1)
    (bq2 : StalkBasisFamily F (q + 2) ιq2) :
    spectrum ℝ (sheafLaplacianMatrix F o₁ q ιq ιq1 ιq2 bq bq1 bq2) =
      spectrum ℝ (sheafLaplacianMatrix F o₂ q ιq ιq1 ιq2 bq bq1 bq2) := by
  let S := orientationSignMatrixUnit (K := K) o₁ o₂ (q + 1) ιq1
  rw [sheafLaplacianMatrix_orientationSign_conj (K := K) F o₁ o₂ q ιq ιq1 ιq2 bq bq1 bq2]
  simpa [S, orientationSignMatrixUnit] using
    (spectrum.units_conjugate (R := ℝ)
      (a := sheafLaplacianMatrix F o₂ q ιq ιq1 ιq2 bq bq1 bq2) (u := S))

theorem finrank_ker_sheafLaplacianMatrix_eq_harmonicSheafNullity
    [LinearOrder V]
    (F : CellularSheaf K) (o : Orientation K) (q : Nat)
    (ιq : StalkIndexFamily (K := K) q)
    (ιq1 : StalkIndexFamily (K := K) (q + 1))
    (ιq2 : StalkIndexFamily (K := K) (q + 2))
    [∀ σ, Fintype (ιq σ)] [∀ σ, Fintype (ιq1 σ)] [∀ σ, Fintype (ιq2 σ)]
    [∀ σ, DecidableEq (ιq σ)] [∀ σ, DecidableEq (ιq1 σ)] [∀ σ, DecidableEq (ιq2 σ)]
    (bq : StalkBasisFamily F q ιq)
    (bq1 : StalkBasisFamily F (q + 1) ιq1)
    (bq2 : StalkBasisFamily F (q + 2) ιq2) :
    Module.finrank ℝ
        (LinearMap.ker (Matrix.toLin' (sheafLaplacianMatrix F o q ιq ιq1 ιq2 bq bq1 bq2))) =
      harmonicSheafNullity (K := K) F q ιq ιq1 ιq2 bq bq1 bq2 := by
  unfold harmonicSheafNullity
  simpa using
    finrank_ker_sheafLaplacianMatrix_eq (K := K) F o (Orientation.sortedOrientation K)
      q ιq ιq1 ιq2 bq bq1 bq2

theorem sheafLaplacianMatrix_spectrum_eq_sorted
    [LinearOrder V]
    (F : CellularSheaf K) (o : Orientation K) (q : Nat)
    (ιq : StalkIndexFamily (K := K) q)
    (ιq1 : StalkIndexFamily (K := K) (q + 1))
    (ιq2 : StalkIndexFamily (K := K) (q + 2))
    [∀ σ, Fintype (ιq σ)] [∀ σ, Fintype (ιq1 σ)] [∀ σ, Fintype (ιq2 σ)]
    [∀ σ, DecidableEq (ιq σ)] [∀ σ, DecidableEq (ιq1 σ)] [∀ σ, DecidableEq (ιq2 σ)]
    (bq : StalkBasisFamily F q ιq)
    (bq1 : StalkBasisFamily F (q + 1) ιq1)
    (bq2 : StalkBasisFamily F (q + 2) ιq2) :
    spectrum ℝ (sheafLaplacianMatrix F o q ιq ιq1 ιq2 bq bq1 bq2) =
      sheafLaplacianSpectrum (K := K) F q ιq ιq1 ιq2 bq bq1 bq2 := by
  rw [sheafLaplacianSpectrum, Matrix.spectrum_toLin']
  exact sheafLaplacianMatrix_spectrum_eq (K := K) F o (Orientation.sortedOrientation K)
    q ιq ιq1 ιq2 bq bq1 bq2

end Laplacian

end PersistentSheafLaplacian
end HeytingLean
