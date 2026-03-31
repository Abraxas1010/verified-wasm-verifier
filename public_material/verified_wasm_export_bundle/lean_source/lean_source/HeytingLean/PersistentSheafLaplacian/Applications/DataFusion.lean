import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic
import HeytingLean.PersistentSheafLaplacian.Basic.CellularSheaf
import HeytingLean.PersistentSheafLaplacian.Laplacian.SheafLaplacian
import Mathlib.LinearAlgebra.Basis.Basic

namespace HeytingLean
namespace PersistentSheafLaplacian

open SimplicialComplex

namespace Applications
namespace DataFusion

open Cochain
open Laplacian

def edgeComplex : SimplicialComplex (Fin 2) where
  simplices := ((Finset.univ : Finset (Fin 2)).powerset).filter Finset.Nonempty
  nonempty_of_mem := by
    intro σ hσ
    simpa [Finset.mem_filter, Finset.mem_powerset] using hσ
  down_closed := by
    intro σ hσ τ hτ hτne
    simpa [Finset.mem_filter, Finset.mem_powerset] using
      And.intro (Finset.subset_univ τ) hτne

def v0Simplex : edgeComplex.Simplex := ⟨{0}, by decide⟩
def v1Simplex : edgeComplex.Simplex := ⟨{1}, by decide⟩
def eSimplex : edgeComplex.Simplex := ⟨Finset.univ, by decide⟩

def edgeWeight (σ : edgeComplex.Simplex) : ℝ :=
  if σ.1.card = 1 ∧ (0 : Fin 2) ∈ σ.1 then 1 else 2

theorem edgeWeight_ne_zero (σ : edgeComplex.Simplex) : edgeWeight σ ≠ 0 := by
  unfold edgeWeight
  split_ifs <;> norm_num

theorem edgeWeight_v0 : edgeWeight v0Simplex = 1 := by
  norm_num [edgeWeight, v0Simplex]

theorem edgeWeight_v1 : edgeWeight v1Simplex = 2 := by
  norm_num [edgeWeight, v1Simplex]

theorem edgeWeight_e : edgeWeight eSimplex = 2 := by
  norm_num [edgeWeight, eSimplex]

noncomputable def weightedSheaf : CellularSheaf edgeComplex where
  stalkType := fun _ => ℝ
  addCommGroup := fun _ => inferInstance
  module := fun _ => inferInstance
  finiteDimensional := fun _ => inferInstance
  restriction := fun {σ τ} _ => (edgeWeight τ / edgeWeight σ) • LinearMap.id
  comp_law := by
    intro σ τ ρ hστ hτρ
    ext
    have hσ : edgeWeight σ ≠ 0 := edgeWeight_ne_zero σ
    have hτ : edgeWeight τ ≠ 0 := edgeWeight_ne_zero τ
    have hcoeff :
        (edgeWeight ρ / edgeWeight τ) * (edgeWeight τ / edgeWeight σ) =
          edgeWeight ρ / edgeWeight σ := by
      field_simp [hσ, hτ]
    simp [LinearMap.comp_apply, hcoeff]

theorem h_v0e : v0Simplex ≤ eSimplex := by
  decide

theorem h_v1e : v1Simplex ≤ eSimplex := by
  decide

theorem weighted_restriction_v0e (x : ℝ) :
    weightedSheaf.restriction h_v0e x = 2 * x := by
  change (edgeWeight eSimplex / edgeWeight v0Simplex : ℝ) * x = 2 * x
  rw [edgeWeight_e, edgeWeight_v0]
  norm_num

theorem weighted_restriction_v1e (x : ℝ) :
    weightedSheaf.restriction h_v1e x = x := by
  change (edgeWeight eSimplex / edgeWeight v1Simplex : ℝ) * x = x
  rw [edgeWeight_e, edgeWeight_v1]
  ring

theorem constant_restriction_v0e (x : ℝ) :
    (CellularSheaf.constantSheaf edgeComplex ℝ).restriction h_v0e x = x := by
  simp [CellularSheaf.constantSheaf]

theorem constant_restriction_v1e (x : ℝ) :
    (CellularSheaf.constantSheaf edgeComplex ℝ).restriction h_v1e x = x := by
  simp [CellularSheaf.constantSheaf]

/-- A concrete non-constant sheaf witness on the one-edge complex: the left vertex-to-edge
restriction is scaled by `2`, whereas the constant sheaf restriction is the identity. This is the
explicit application-level datum that the eventual PSL discrimination theorem should detect. -/
theorem oneEdge_weightedRestriction_ne_constant :
    weightedSheaf.restriction h_v0e ≠
      (CellularSheaf.constantSheaf edgeComplex ℝ).restriction h_v0e := by
  intro hEq
  have hval := congrArg (fun f => f (1 : ℝ)) hEq
  have hval' :
      weightedSheaf.restriction h_v0e (1 : ℝ) =
        (CellularSheaf.constantSheaf edgeComplex ℝ).restriction h_v0e (1 : ℝ) := by
    simpa using hval
  rw [weighted_restriction_v0e, constant_restriction_v0e] at hval'
  norm_num at hval'

/-- Scalar coordinates for the explicit one-edge sheaf computations. -/
abbrev scalarIndexFamily (q : Nat) : StalkIndexFamily (K := edgeComplex) q := fun _ => Unit

noncomputable def weightedBasisFamily (q : Nat) :
    StalkBasisFamily weightedSheaf q (scalarIndexFamily q) :=
  fun _ => Module.Basis.singleton Unit ℝ

noncomputable def constantBasisFamily (q : Nat) :
    StalkBasisFamily (CellularSheaf.constantSheaf edgeComplex ℝ) q (scalarIndexFamily q) :=
  fun _ => Module.Basis.singleton Unit ℝ

abbrev ScalarCoord (q : Nat) := Laplacian.CochainCoord (K := edgeComplex) q (scalarIndexFamily q)

def v0q : edgeComplex.qSimplices 0 := ⟨v0Simplex, by decide⟩
def v1q : edgeComplex.qSimplices 0 := ⟨v1Simplex, by decide⟩
def eq1 : edgeComplex.qSimplices 1 := ⟨eSimplex, by decide⟩

def v0Coord : ScalarCoord 0 := ⟨v0q, ()⟩
def v1Coord : ScalarCoord 0 := ⟨v1q, ()⟩
def eCoord : ScalarCoord 1 := ⟨eq1, ()⟩

theorem scalarCoord0_univ :
    (Finset.univ : Finset (ScalarCoord 0)) = {v0Coord, v1Coord} := by
  decide

theorem scalarCoord2_univ :
    (Finset.univ : Finset (ScalarCoord 2)) = ∅ := by
  decide

theorem sorted_signedIncidence_v0e :
    Orientation.signedIncidence (Orientation.sortedOrientation edgeComplex) h_v0e = -1 := by
  have hdiff : eSimplex.1 \ v0Simplex.1 = ({1} : Finset (Fin 2)) := by
    ext i
    fin_cases i <;> simp [eSimplex, v0Simplex]
  have hv : (eSimplex.1 \ v0Simplex.1).toList = [1] := by
    rw [hdiff]
    simp
  have hsort : eSimplex.1.sort (· ≤ ·) = [0, 1] := by
    native_decide
  rw [Orientation.sortedOrientation_signedIncidence_mul_one h_v0e hv]
  rw [hsort]
  norm_num [Orientation.alternatingSign]

theorem sorted_signedIncidence_v1e :
    Orientation.signedIncidence (Orientation.sortedOrientation edgeComplex) h_v1e = 1 := by
  have hdiff : eSimplex.1 \ v1Simplex.1 = ({0} : Finset (Fin 2)) := by
    ext i
    fin_cases i <;> simp [eSimplex, v1Simplex]
  have hv : (eSimplex.1 \ v1Simplex.1).toList = [0] := by
    rw [hdiff]
    simp
  have hsort : eSimplex.1.sort (· ≤ ·) = [0, 1] := by
    native_decide
  rw [Orientation.sortedOrientation_signedIncidence_mul_one h_v1e hv]
  rw [hsort]
  norm_num [Orientation.alternatingSign]

theorem weighted_coboundaryMatrix_e_v0 :
    coboundaryMatrix weightedSheaf (Orientation.sortedOrientation edgeComplex) 0
        (scalarIndexFamily 0) (scalarIndexFamily 1)
        (weightedBasisFamily 0) (weightedBasisFamily 1) eCoord v0Coord = -2 := by
  rw [coboundaryMatrix_eq_toMatrix, LinearMap.toMatrix_apply]
  simp [cochainBasis, weightedBasisFamily, eCoord, v0Coord, v0q, eq1, coboundary_piSingle,
    h_v0e, weighted_restriction_v0e, sorted_signedIncidence_v0e]
  calc
    ((Module.Basis.singleton Unit ℝ).repr (2 * (Module.Basis.singleton Unit ℝ) ())) () =
        2 * (Module.Basis.singleton Unit ℝ) () := by
          simpa using
            (Module.Basis.singleton_repr Unit ℝ
              (2 * (Module.Basis.singleton Unit ℝ) ()) ())
    _ = 2 := by simp [Module.Basis.singleton_apply]

theorem weighted_coboundaryMatrix_e_v1 :
    coboundaryMatrix weightedSheaf (Orientation.sortedOrientation edgeComplex) 0
        (scalarIndexFamily 0) (scalarIndexFamily 1)
        (weightedBasisFamily 0) (weightedBasisFamily 1) eCoord v1Coord = 1 := by
  rw [coboundaryMatrix_eq_toMatrix, LinearMap.toMatrix_apply]
  simp [cochainBasis, weightedBasisFamily, eCoord, v1Coord, v1q, eq1, coboundary_piSingle,
    h_v1e, weighted_restriction_v1e, sorted_signedIncidence_v1e]
  calc
    ((Module.Basis.singleton Unit ℝ).repr ((Module.Basis.singleton Unit ℝ) ())) () =
        (Module.Basis.singleton Unit ℝ) () := by
          simpa using
            (Module.Basis.singleton_repr Unit ℝ
              ((Module.Basis.singleton Unit ℝ) ()) ())
    _ = 1 := by simp [Module.Basis.singleton_apply]

theorem constant_coboundaryMatrix_e_v0 :
    coboundaryMatrix (CellularSheaf.constantSheaf edgeComplex ℝ)
        (Orientation.sortedOrientation edgeComplex) 0
        (scalarIndexFamily 0) (scalarIndexFamily 1)
        (constantBasisFamily 0) (constantBasisFamily 1) eCoord v0Coord = -1 := by
  rw [coboundaryMatrix_eq_toMatrix, LinearMap.toMatrix_apply]
  simp [cochainBasis, constantBasisFamily, eCoord, v0Coord, v0q, eq1, coboundary_piSingle,
    h_v0e, constant_restriction_v0e, sorted_signedIncidence_v0e]
  calc
    ((Module.Basis.singleton Unit ℝ).repr ((Module.Basis.singleton Unit ℝ) ())) () =
        (Module.Basis.singleton Unit ℝ) () := by
          simpa using
            (Module.Basis.singleton_repr Unit ℝ
              ((Module.Basis.singleton Unit ℝ) ()) ())
    _ = 1 := by simp [Module.Basis.singleton_apply]

theorem constant_coboundaryMatrix_e_v1 :
    coboundaryMatrix (CellularSheaf.constantSheaf edgeComplex ℝ)
        (Orientation.sortedOrientation edgeComplex) 0
        (scalarIndexFamily 0) (scalarIndexFamily 1)
        (constantBasisFamily 0) (constantBasisFamily 1) eCoord v1Coord = 1 := by
  rw [coboundaryMatrix_eq_toMatrix, LinearMap.toMatrix_apply]
  simp [cochainBasis, constantBasisFamily, eCoord, v1Coord, v1q, eq1, coboundary_piSingle,
    h_v1e, constant_restriction_v1e, sorted_signedIncidence_v1e]
  calc
    ((Module.Basis.singleton Unit ℝ).repr ((Module.Basis.singleton Unit ℝ) ())) () =
        (Module.Basis.singleton Unit ℝ) () := by
          simpa using
            (Module.Basis.singleton_repr Unit ℝ
              ((Module.Basis.singleton Unit ℝ) ()) ())
    _ = 1 := by simp [Module.Basis.singleton_apply]

theorem weighted_sheafLaplacianMatrix_entry :
    sheafLaplacianMatrix weightedSheaf (Orientation.sortedOrientation edgeComplex) 0
        (scalarIndexFamily 0) (scalarIndexFamily 1) (scalarIndexFamily 2)
        (weightedBasisFamily 0) (weightedBasisFamily 1) (weightedBasisFamily 2)
        eCoord eCoord = 5 := by
  simp [sheafLaplacianMatrix, hodgeLaplacianMatrix, Matrix.add_apply, Matrix.mul_apply,
    Matrix.transpose_apply, scalarCoord2_univ, scalarCoord0_univ,
    weighted_coboundaryMatrix_e_v0, weighted_coboundaryMatrix_e_v1]
  rw [show ({v0Coord, v1Coord} : Finset (ScalarCoord 0)) = insert v0Coord {v1Coord} by simp]
  rw [Finset.sum_insert]
  · simp [weighted_coboundaryMatrix_e_v0, weighted_coboundaryMatrix_e_v1]
    norm_num
  · simp
    decide

theorem constant_sheafLaplacianMatrix_entry :
    sheafLaplacianMatrix (CellularSheaf.constantSheaf edgeComplex ℝ)
        (Orientation.sortedOrientation edgeComplex) 0
        (scalarIndexFamily 0) (scalarIndexFamily 1) (scalarIndexFamily 2)
        (constantBasisFamily 0) (constantBasisFamily 1) (constantBasisFamily 2)
        eCoord eCoord = 2 := by
  simp [sheafLaplacianMatrix, hodgeLaplacianMatrix, Matrix.add_apply, Matrix.mul_apply,
    Matrix.transpose_apply, scalarCoord2_univ, scalarCoord0_univ,
    constant_coboundaryMatrix_e_v0, constant_coboundaryMatrix_e_v1]
  rw [show ({v0Coord, v1Coord} : Finset (ScalarCoord 0)) = insert v0Coord {v1Coord} by simp]
  rw [Finset.sum_insert]
  · simp [constant_coboundaryMatrix_e_v0, constant_coboundaryMatrix_e_v1]
    norm_num
  · simp
    decide

/-- The one-edge weighted sheaf already differs from the constant sheaf at the Laplacian-matrix
level: on the unique degree-1 edge coordinate, the weighted Laplacian entry is `5`, while the
constant sheaf gives `2`. This is the concrete PSL-level discrimination witness on disk. -/
theorem oneEdge_weightedLaplacian_ne_constant :
    sheafLaplacianMatrix weightedSheaf (Orientation.sortedOrientation edgeComplex) 0
        (scalarIndexFamily 0) (scalarIndexFamily 1) (scalarIndexFamily 2)
        (weightedBasisFamily 0) (weightedBasisFamily 1) (weightedBasisFamily 2) ≠
      sheafLaplacianMatrix (CellularSheaf.constantSheaf edgeComplex ℝ)
        (Orientation.sortedOrientation edgeComplex) 0
        (scalarIndexFamily 0) (scalarIndexFamily 1) (scalarIndexFamily 2)
        (constantBasisFamily 0) (constantBasisFamily 1) (constantBasisFamily 2) := by
  intro hEq
  have hentry :
      sheafLaplacianMatrix weightedSheaf (Orientation.sortedOrientation edgeComplex) 0
          (scalarIndexFamily 0) (scalarIndexFamily 1) (scalarIndexFamily 2)
          (weightedBasisFamily 0) (weightedBasisFamily 1) (weightedBasisFamily 2)
          eCoord eCoord =
        sheafLaplacianMatrix (CellularSheaf.constantSheaf edgeComplex ℝ)
          (Orientation.sortedOrientation edgeComplex) 0
          (scalarIndexFamily 0) (scalarIndexFamily 1) (scalarIndexFamily 2)
          (constantBasisFamily 0) (constantBasisFamily 1) (constantBasisFamily 2)
          eCoord eCoord := by
    simpa using congrArg (fun M => M eCoord eCoord) hEq
  rw [weighted_sheafLaplacianMatrix_entry, constant_sheafLaplacianMatrix_entry] at hentry
  norm_num at hentry

end DataFusion
end Applications

end PersistentSheafLaplacian
end HeytingLean
