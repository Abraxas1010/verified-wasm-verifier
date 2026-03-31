import HeytingLean.Genesis.IterantComplex
import HeytingLean.Ontology.Primordial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Genesis.EulerBloch

First-attempt canonical Euler-angle <-> Bloch correspondence layer.
-/

noncomputable section

namespace HeytingLean.Genesis

open HeytingLean.Ontology
open HeytingLean.Quantum.Contextuality.Pauli

/-- Bloch-vector style state (real coordinates on the unit sphere). -/
structure BlochState where
  x : Real
  y : Real
  z : Real
  norm_one : x ^ 2 + y ^ 2 + z ^ 2 = 1

/-- Canonical Euler-angle triple (angles constrained to `[0, π]`). -/
structure EulerTriple where
  θx : Real
  θy : Real
  θz : Real
  θx_nonneg : 0 ≤ θx
  θx_le_pi : θx ≤ Real.pi
  θy_nonneg : 0 ≤ θy
  θy_le_pi : θy ≤ Real.pi
  θz_nonneg : 0 ≤ θz
  θz_le_pi : θz ≤ Real.pi
  consistency : (Real.cos θx) ^ 2 + (Real.cos θy) ^ 2 + (Real.cos θz) ^ 2 = 1

/-- Canonical Bloch projection of an Euler triple. -/
def toBloch (e : EulerTriple) : BlochState where
  x := Real.cos e.θx
  y := Real.cos e.θy
  z := Real.cos e.θz
  norm_one := e.consistency

lemma x_sq_le_one (b : BlochState) : b.x ^ 2 ≤ 1 := by
  nlinarith [sq_nonneg b.y, sq_nonneg b.z, b.norm_one]

lemma y_sq_le_one (b : BlochState) : b.y ^ 2 ≤ 1 := by
  nlinarith [sq_nonneg b.x, sq_nonneg b.z, b.norm_one]

lemma z_sq_le_one (b : BlochState) : b.z ^ 2 ≤ 1 := by
  nlinarith [sq_nonneg b.x, sq_nonneg b.y, b.norm_one]

lemma x_bounds (b : BlochState) : -1 ≤ b.x ∧ b.x ≤ 1 := by
  have hx2 : b.x ^ 2 ≤ 1 := x_sq_le_one b
  constructor
  · nlinarith
  · nlinarith

lemma y_bounds (b : BlochState) : -1 ≤ b.y ∧ b.y ≤ 1 := by
  have hy2 : b.y ^ 2 ≤ 1 := y_sq_le_one b
  constructor
  · nlinarith
  · nlinarith

lemma z_bounds (b : BlochState) : -1 ≤ b.z ∧ b.z ≤ 1 := by
  have hz2 : b.z ^ 2 ≤ 1 := z_sq_le_one b
  constructor
  · nlinarith
  · nlinarith

/-- Canonical Euler-angle lift from a Bloch state. -/
def fromBloch (b : BlochState) : EulerTriple where
  θx := Real.arccos b.x
  θy := Real.arccos b.y
  θz := Real.arccos b.z
  θx_nonneg := Real.arccos_nonneg b.x
  θx_le_pi := Real.arccos_le_pi b.x
  θy_nonneg := Real.arccos_nonneg b.y
  θy_le_pi := Real.arccos_le_pi b.y
  θz_nonneg := Real.arccos_nonneg b.z
  θz_le_pi := Real.arccos_le_pi b.z
  consistency := by
    have hx : Real.cos (Real.arccos b.x) = b.x :=
      Real.cos_arccos (x_bounds b).1 (x_bounds b).2
    have hy : Real.cos (Real.arccos b.y) = b.y :=
      Real.cos_arccos (y_bounds b).1 (y_bounds b).2
    have hz : Real.cos (Real.arccos b.z) = b.z :=
      Real.cos_arccos (z_bounds b).1 (z_bounds b).2
    calc
      (Real.cos (Real.arccos b.x)) ^ 2 +
          (Real.cos (Real.arccos b.y)) ^ 2 +
          (Real.cos (Real.arccos b.z)) ^ 2
          = b.x ^ 2 + b.y ^ 2 + b.z ^ 2 := by simp [hx, hy, hz]
      _ = 1 := b.norm_one

theorem toBloch_fromBloch (b : BlochState) : toBloch (fromBloch b) = b := by
  cases b with
  | mk x y z hnorm =>
      have hx2 : x ^ 2 ≤ 1 := by
        nlinarith [sq_nonneg y, sq_nonneg z, hnorm]
      have hy2 : y ^ 2 ≤ 1 := by
        nlinarith [sq_nonneg x, sq_nonneg z, hnorm]
      have hz2 : z ^ 2 ≤ 1 := by
        nlinarith [sq_nonneg x, sq_nonneg y, hnorm]
      have hx : -1 ≤ x ∧ x ≤ 1 := by
        constructor <;> nlinarith
      have hy : -1 ≤ y ∧ y ≤ 1 := by
        constructor <;> nlinarith
      have hz : -1 ≤ z ∧ z ≤ 1 := by
        constructor <;> nlinarith
      simp [toBloch, fromBloch, Real.cos_arccos, hx, hy, hz]

theorem fromBloch_toBloch (e : EulerTriple) : fromBloch (toBloch e) = e := by
  cases e with
  | mk θx θy θz hx0 hxpi hy0 hypi hz0 hzpi hcons =>
      simp [fromBloch, toBloch, Real.arccos_cos, hx0, hxpi, hy0, hypi, hz0, hzpi]

/-- Main first-attempt Euler/Bloch equivalence. -/
noncomputable def euler_bloch_equiv : EulerTriple ≃ BlochState where
  toFun := toBloch
  invFun := fromBloch
  left_inv := fromBloch_toBloch
  right_inv := toBloch_fromBloch

/-- Triple of Euler phases represented as primordial oscillations. -/
def eulerCirclePhases (e : EulerTriple) : Complex × Complex × Complex :=
  (primordialOscillation e.θx, primordialOscillation e.θy, primordialOscillation e.θz)

theorem euler_circle_phase_model (e : EulerTriple) :
    eulerCirclePhases e =
      (primordialOscillation e.θx, primordialOscillation e.θy, primordialOscillation e.θz) :=
  rfl

theorem euler_circle_antiphase_x (e : EulerTriple) :
    primordialOscillation (e.θx + Real.pi) = -primordialOscillation e.θx := by
  exact oscillation_antiphase e.θx

theorem euler_circle_antiphase_y (e : EulerTriple) :
    primordialOscillation (e.θy + Real.pi) = -primordialOscillation e.θy := by
  exact oscillation_antiphase e.θy

theorem euler_circle_antiphase_z (e : EulerTriple) :
    primordialOscillation (e.θz + Real.pi) = -primordialOscillation e.θz := by
  exact oscillation_antiphase e.θz

/-- Orthogonal-consistency projection law in Bloch coordinates. -/
theorem orthogonal_triple_consistency (e : EulerTriple) :
    (toBloch e).x ^ 2 + (toBloch e).y ^ 2 + (toBloch e).z ^ 2 = 1 :=
  e.consistency

/-- Pauli observable from Bloch coordinates. -/
def blochPauliObservable (b : BlochState) : Mat2 :=
  pauliObservable (b.x : Complex) (b.y : Complex) (b.z : Complex)

/-- Pauli observable induced by an Euler triple through its Bloch projection. -/
def eulerPauliObservable (e : EulerTriple) : Mat2 :=
  blochPauliObservable (toBloch e)

/-- Matrix transport identity from Euler side to Bloch side. -/
theorem iterant_matrix_to_bloch (e : EulerTriple) :
    eulerPauliObservable e = blochPauliObservable (toBloch e) :=
  rfl

/-- Nontrivial Bloch operator law: unit Bloch vectors give involutive Pauli observables. -/
theorem blochPauliObservable_sq_one (b : BlochState) :
    blochPauliObservable b * blochPauliObservable b = (1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j
  · unfold blochPauliObservable pauliObservable
    simp [σx, σy, σz, Matrix.mul_apply]
    calc
      (↑b.z * ↑b.z + (↑b.x + -(↑b.y * Complex.I)) * (↑b.x + ↑b.y * Complex.I) : Complex)
          = ((b.x ^ 2 + b.y ^ 2 + b.z ^ 2 : Real) : Complex) := by
            ring_nf
            simp [Complex.I_sq]
            ring
      _ = 1 := by
            exact_mod_cast b.norm_one
  · unfold blochPauliObservable pauliObservable
    simp [σx, σy, σz, Matrix.mul_apply]
    ring
  · unfold blochPauliObservable pauliObservable
    simp [σx, σy, σz, Matrix.mul_apply]
    ring
  · unfold blochPauliObservable pauliObservable
    simp [σx, σy, σz, Matrix.mul_apply]
    calc
      ((↑b.x + ↑b.y * Complex.I) * (↑b.x + -(↑b.y * Complex.I)) + ↑b.z * ↑b.z : Complex)
          = ((b.x ^ 2 + b.y ^ 2 + b.z ^ 2 : Real) : Complex) := by
            ring_nf
            simp [Complex.I_sq]
      _ = 1 := by
            exact_mod_cast b.norm_one

/-- Nontrivial Bloch operator law: Pauli observable of a Bloch state is traceless. -/
theorem blochPauliObservable_trace_zero (b : BlochState) :
    Matrix.trace (blochPauliObservable b) = 0 := by
  unfold blochPauliObservable pauliObservable
  simp [Matrix.trace, σx, σy, σz]

/-- Euler-induced Pauli observable is involutive at the canonical Bloch projection. -/
theorem eulerPauliObservable_sq_one (e : EulerTriple) :
    eulerPauliObservable e * eulerPauliObservable e = (1 : Mat2) := by
  simpa [eulerPauliObservable] using blochPauliObservable_sq_one (toBloch e)

/-- Euler-induced Pauli observable is traceless at the canonical Bloch projection. -/
theorem eulerPauliObservable_trace_zero (e : EulerTriple) :
    Matrix.trace (eulerPauliObservable e) = 0 := by
  simpa [eulerPauliObservable] using blochPauliObservable_trace_zero (toBloch e)

end HeytingLean.Genesis
