import HeytingLean.Noneism.Contextuality.Examples.KochenSpeckerDeep.Requirements
import Mathlib

/- This file defines the necessary data types and helper lemmas to prove the Kochen-Specker Paradox -/

namespace HeytingLean
namespace Noneism
namespace Contextuality
namespace KochenSpeckerDeep

/- Binary outcomes for a spin measurement -/
inductive SpinMeasurement : Type
| zero
| one

open SpinMeasurement
open scoped Matrix

instance : DecidableEq SpinMeasurement :=
  fun x y => match x, y with
    | zero, zero => isTrue rfl
    | one, one => isTrue rfl
    | zero, one => isFalse (by simp)
    | one, zero => isFalse (by simp)

/-- Measurement direction definitions and properties -/

@[simp]
def SquaredNorm (v : Fin 3 → ℝ) : ℝ :=
  v ⬝ᵥ v

/-- A measurement direction is a unit vector in 3D space -/
def MeasurementDirection : Type :=
  {v : Fin 3 → ℝ // SquaredNorm v = 1}

@[simp]
def MeasurementDirection.index (d : MeasurementDirection) (i : Fin 3) : ℝ :=
  d.val i

/- "d[i]" gives the ith element in a MeasurementDirection -/
notation d "[" i "]" => MeasurementDirection.index d i

theorem MeasurementDirection.norm_def (v : MeasurementDirection) :
  v[0] ^ 2 + v[1] ^ 2 + v[2] ^ 2 = 1 :=
by
  have hnorm : v.1 ⬝ᵥ v.1 = 1 := by exact v.2
  rw [dotProduct] at hnorm
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ] at hnorm
  simp at hnorm
  repeat rw [MeasurementDirection.index]
  calc
    v.val 0 ^ 2 + v.val 1 ^ 2 + v.val 2 ^ 2 = v.val 0 * v.val 0 + (v.val 1 * v.val 1 + v.val 2 * v.val 2) := by ring
    _ = 1 := by exact hnorm

/-- Perpendicularity definitions for measurement directions -/

def IsPerpendicular (d1 d2 : MeasurementDirection) : Prop :=
  d1.val ⬝ᵥ d2.val = 0

def IsMutuallyPerpendicular(d1 d2 d3 : MeasurementDirection) : Prop :=
  IsPerpendicular d1 d2 ∧ IsPerpendicular d2 d3 ∧ IsPerpendicular d1 d3

/-- Valid measurement outcomes for mutually perpendicular directions (see: SPIN axoim) -/

def ValidThriples : List (List SpinMeasurement) :=
  [[zero, one, one], [one, zero, one], [one, one, zero]]

/-- One-Zero-One functions. The Kochen-Specker paradox states that the `OneZeroOneFunc` Type is empty -/

def IsOneZeroOneFunc (f : MeasurementDirection → SpinMeasurement) : Prop :=
  ∀ d1 d2 d3 : MeasurementDirection, IsMutuallyPerpendicular d1 d2 d3 → [f d1, f d2, f d3] ∈ ValidThriples

def OneZeroOneFunc : Type :=
  {f : (MeasurementDirection → SpinMeasurement) // IsOneZeroOneFunc f}

def apply (f : OneZeroOneFunc) (a : MeasurementDirection) : SpinMeasurement :=
  f.val a

/-- O3 (orthogonal group) definitions and properties -/

structure O3 where
  matrix : Matrix (Fin 3) (Fin 3) ℝ
  is_orth : matrix ∈ Matrix.orthogonalGroup (Fin 3) ℝ

instance : Coe O3 (Matrix (Fin 3) (Fin 3) ℝ) :=
 {coe := fun m => m.matrix}

/- Transformation under O3 preserves the dot product between vectors -/

theorem O3.dot_product_preservation (v1 v2 : Fin 3 → ℝ) (m : O3) :
  (m.matrix *ᵥ v1) ⬝ᵥ (m *ᵥ v2) = v1 ⬝ᵥ v2 :=
by
  have horth : mᵀ * m.matrix = 1 :=
    by apply (Iff.mp (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ)) m.is_orth
  calc
    m *ᵥ v1 ⬝ᵥ m *ᵥ v2  = (m *ᵥ v1) ᵥ* m ⬝ᵥ v2 := by exact Matrix.dotProduct_mulVec (m *ᵥ v1) m.matrix v2
    _ = v1 ᵥ* (mᵀ * m.matrix) ⬝ᵥ v2 := by rw [Matrix.vecMul_mulVec]
    _ = v1 ⬝ᵥ v2 := by simp [horth]

/- Transformation under 03 preserves vector norms -/

theorem O3.norm_preservation (v : Fin 3 → ℝ) (m : O3) :
  SquaredNorm (m *ᵥ v) = SquaredNorm v :=
by
  simpa [SquaredNorm] using O3.dot_product_preservation v v m

def O3.function (o : O3) : MeasurementDirection → MeasurementDirection :=
  fun d => ⟨o *ᵥ d.val, by rw [O3.norm_preservation] ; exact d.2⟩

/- Transforming the input of a 101-function using an O3-matrix produces a new 101-function.
This result is key in shortening the proof of kochen-specker since it lets us make "WLOG"
arguments by exploiting symmetries -/

theorem O3.OneZeroOneFunc_invariance (f : MeasurementDirection → SpinMeasurement)  (m : O3) :
  IsOneZeroOneFunc f → IsOneZeroOneFunc (f ∘ m.function) :=
by
  intro hf d1 d2 d3 hperp
  have h12 : IsPerpendicular (m.function d1) (m.function d2) := by
    unfold IsPerpendicular O3.function
    exact (O3.dot_product_preservation d1.val d2.val m).trans hperp.1
  have h23 : IsPerpendicular (m.function d2) (m.function d3) := by
    unfold IsPerpendicular O3.function
    exact (O3.dot_product_preservation d2.val d3.val m).trans hperp.2.1
  have h13 : IsPerpendicular (m.function d1) (m.function d3) := by
    unfold IsPerpendicular O3.function
    exact (O3.dot_product_preservation d1.val d3.val m).trans hperp.2.2
  exact hf _ _ _ ⟨h12, h23, h13⟩

def O3.compose_OneZeroOneFunc (f : OneZeroOneFunc) (m : O3) : OneZeroOneFunc :=
  ⟨f.val ∘ m.function, by exact O3.OneZeroOneFunc_invariance f.val m f.property⟩

/-- Cross product definition, along with a proof that it preserves norm when acting on perpendicular unit vectors.
(surprisingly, I was not able to find an equivalent lemma in Mathlib)
This is used in `perp_zero_implies_one` to "complete the basis" given two orthonormal vectors -/

def CrossProduct (d1 d2 : MeasurementDirection) (hperp : IsPerpendicular d1 d2): MeasurementDirection :=
  ⟨d1.val ⨯₃ d2.val,
   by
    have hnorm1 : d1.val ⬝ᵥ d1.val = 1 := d1.2
    have hnorm2 : d2.val ⬝ᵥ d2.val = 1 := d2.2
    have hperp' : d1.val ⬝ᵥ d2.val = 0 := hperp
    calc
      (d1.val ⨯₃ d2.val) ⬝ᵥ (d1.val ⨯₃ d2.val)
          = (d1.val ⬝ᵥ d1.val) * (d2.val ⬝ᵥ d2.val) -
              (d1.val ⬝ᵥ d2.val) * (d2.val ⬝ᵥ d1.val) := by
            simpa using (cross_dot_cross d1.val d2.val d1.val d2.val)
      _ = (d1.val ⬝ᵥ d1.val) * (d2.val ⬝ᵥ d2.val) -
            (d1.val ⬝ᵥ d2.val) * (d1.val ⬝ᵥ d2.val) := by
          rw [dotProduct_comm d2.val d1.val]
      _ = 1 := by simp [hnorm1, hnorm2, hperp']⟩

/-- Helper lemmas based on properties of One-Zero-One functions -/

/- Any direction perpendicular to one assgined `zero` must be assigned `one` -/

theorem perp_zero_implies_one (f : OneZeroOneFunc) (d1 d2 : MeasurementDirection) :
  apply f d1 = zero → IsPerpendicular d1 d2 → apply f d2 = one :=
by
  intro hd1z hperp12
  -- Construct the third perpendicular vector using `CrossProduct` so that we can exploit the `OneZeroOneFunc` definition
  have hperp13 : IsPerpendicular d1 (CrossProduct d1 d2 hperp12) := by
    unfold IsPerpendicular CrossProduct
    simp
  have hperp23 : IsPerpendicular d2 (CrossProduct d1 d2 hperp12) := by
    unfold IsPerpendicular CrossProduct
    simp
  have hmutualperp : IsMutuallyPerpendicular d1 d2 (CrossProduct d1 d2 hperp12) := by
    rw [IsMutuallyPerpendicular]
    apply And.intro hperp12 (And.intro hperp23 hperp13)
  have hvalidthrip : [apply f d1, apply f d2, apply f (CrossProduct d1 d2 hperp12)] ∈ ValidThriples :=
    f.2 d1 d2 (CrossProduct d1 d2 hperp12) hmutualperp
  rw [hd1z] at hvalidthrip
  rw [ValidThriples] at hvalidthrip ; simp at hvalidthrip
  exact hvalidthrip.left

/- Any direction mutually perpendicular to two assgined `one` must be assigned `zero` -/
theorem perp_one_one_implies_zero (f : OneZeroOneFunc) ( d1 d2 d3 : MeasurementDirection) :
  apply f d1 = one ∧ apply f d2 = one → IsMutuallyPerpendicular d1 d2 d3 → apply f d3 = zero :=
by
  intro hone hperp
  have hin : [apply f d1, apply f d2, apply f d3] ∈ ValidThriples := f.property d1 d2 d3 hperp
  rw [ValidThriples] at hin ; simp at hin
  cases hin with
  | inl heq =>
    rw [hone.left] at heq
    have hnonsense : one = zero := heq.left
    contradiction
  | inr heq => cases heq with
    | inl heq =>
      rw [hone.right] at heq
      have hnonsense : one = zero := heq.right.left
      contradiction
    | inr heq =>
      exact heq.right.right

end KochenSpeckerDeep
end Contextuality
end Noneism
end HeytingLean
