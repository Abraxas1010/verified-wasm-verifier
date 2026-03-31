import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic

/-!
# LoF ↔ Bloch (laptop-scale core)

This module is a lightweight, **purely algebraic** Bloch-sphere-style model intended for
"Quantum on a Laptop" development inside `HeytingLean`.

Conventions:
- A `LoFState` is a real triple `(j, k, mark)`.
- We interpret `(j, k, mark)` as the Bloch coordinates `(x, y, z)` respectively.
- `logicParameter s := |s.mark|` (classicality parameter λ).

Everything here is intentionally finite and proof-friendly: no differential calculus and no
stochastic analysis.
-/

namespace HeytingLean
namespace Quantum

/-! ## States -/

/-- A Bloch-style real triple packaged with LoF names. -/
structure LoFState where
  j : ℝ
  k : ℝ
  mark : ℝ

namespace LoFState

/-- Coordinate projection using the convention:
`0 ↦ j (x)`, `1 ↦ k (y)`, `2 ↦ mark (z)`. -/
def coord (s : LoFState) : Fin 3 → ℝ
  | 0 => s.j
  | 1 => s.k
  | _ => s.mark

@[simp] lemma coord_zero (s : LoFState) : s.coord 0 = s.j := rfl
@[simp] lemma coord_one (s : LoFState) : s.coord 1 = s.k := rfl
@[simp] lemma coord_two (s : LoFState) : s.coord 2 = s.mark := rfl

/-- Alias for interoperability with `Fin 3 → ℝ` APIs. -/
abbrev toVec (s : LoFState) : Fin 3 → ℝ := s.coord

/-! ### Canonical points -/

/-- "Void" (unmarked) is the north pole: `|0⟩`. -/
def void : LoFState := ⟨0, 0, 1⟩

/-- "Mark" is the south pole: `|1⟩`. -/
def markState : LoFState := ⟨0, 0, -1⟩

/-- "Re-entry" is the +X equator state: `|+⟩`. -/
def reentry : LoFState := ⟨1, 0, 0⟩

/-- +Y equator state: `|+i⟩`. -/
def kPlus : LoFState := ⟨0, 1, 0⟩

end LoFState

/-! ## Levi–Civita and su(2) Poisson bracket (finite) -/

/-- Levi–Civita symbol on `Fin 3` in the standard orientation `(0,1,2)`. -/
def epsilon (i j k : Fin 3) : ℝ :=
  match i, j, k with
  | 0, 1, 2 => 1
  | 1, 2, 0 => 1
  | 2, 0, 1 => 1
  | 1, 0, 2 => -1
  | 2, 1, 0 => -1
  | 0, 2, 1 => -1
  | _, _, _ => 0

/-- Coordinate-level Poisson bracket `{sᵢ, sⱼ} = ∑ₖ εᵢⱼₖ sₖ` specialized to `Fin 3`.

We keep this as an explicit 3-term "finite sum" to stay proof-friendly. -/
def poissonCoord (i j : Fin 3) (s : LoFState) : ℝ :=
  epsilon i j 0 * s.coord 0 +
  epsilon i j 1 * s.coord 1 +
  epsilon i j 2 * s.coord 2

@[simp] lemma poissonCoord_xy (s : LoFState) : poissonCoord 0 1 s = s.mark := by
  simp [poissonCoord, epsilon, LoFState.coord]

@[simp] lemma poissonCoord_yz (s : LoFState) : poissonCoord 1 2 s = s.j := by
  simp [poissonCoord, epsilon, LoFState.coord]

@[simp] lemma poissonCoord_zx (s : LoFState) : poissonCoord 2 0 s = s.k := by
  simp [poissonCoord, epsilon, LoFState.coord]

/-- Regression bundle: the coordinate bracket matches the `su(2)` structure constants. -/
theorem poisson_is_su2 (s : LoFState) :
    poissonCoord 0 1 s = s.mark ∧ poissonCoord 1 2 s = s.j ∧ poissonCoord 2 0 s = s.k := by
  simp

/-! ## Gates as Bloch rotations (small set) -/

/-! We model gates as their induced action on Bloch coordinates. -/

def gateX (s : LoFState) : LoFState := ⟨s.j, -s.k, -s.mark⟩
def gateY (s : LoFState) : LoFState := ⟨-s.j, s.k, -s.mark⟩
def gateZ (s : LoFState) : LoFState := ⟨-s.j, -s.k, s.mark⟩

/-- Hadamard acts on Bloch coordinates by `(x,y,z) ↦ (z, -y, x)`. -/
def gateH (s : LoFState) : LoFState := ⟨s.mark, -s.k, s.j⟩

@[simp] lemma gateX_involutive (s : LoFState) : gateX (gateX s) = s := by
  cases s with
  | mk j k mark =>
      simp [gateX]

@[simp] lemma gateY_involutive (s : LoFState) : gateY (gateY s) = s := by
  cases s with
  | mk j k mark =>
      simp [gateY]

@[simp] lemma gateZ_involutive (s : LoFState) : gateZ (gateZ s) = s := by
  cases s with
  | mk j k mark =>
      simp [gateZ]

@[simp] lemma gateH_involutive (s : LoFState) : gateH (gateH s) = s := by
  cases s with
  | mk j k mark =>
      simp [gateH]

/-! ## Logic-regime parameter λ -/

/-- Classicality / logic-regime parameter `λ = |z| = |mark|`. -/
def logicParameter (s : LoFState) : ℝ := |s.mark|

/-- A simple "nucleus strength" complement: `1 - λ`. -/
def nucleusStrength (lam : ℝ) : ℝ := 1 - lam

@[simp] lemma logicParameter_gateZ (s : LoFState) :
    logicParameter (gateZ s) = logicParameter s := by
  simp [logicParameter, gateZ]

@[simp] lemma logicParameter_gateX (s : LoFState) :
    logicParameter (gateX s) = logicParameter s := by
  simp [logicParameter, gateX, abs_neg]

@[simp] lemma logicParameter_gateY (s : LoFState) :
    logicParameter (gateY s) = logicParameter s := by
  simp [logicParameter, gateY, abs_neg]

/-!
## Compatibility re-exports

Some downstream code refers to `HeytingLean.Quantum.LoFBloch.LoFState` and friends.
We provide `LoFBloch` as a namespace-level shim so both `LoFState` and
`LoFBloch.LoFState` are available.
-/

namespace LoFBloch

abbrev LoFState := HeytingLean.Quantum.LoFState

def void : LoFState := HeytingLean.Quantum.LoFState.void
def mark : LoFState := HeytingLean.Quantum.LoFState.markState
def reentry : LoFState := HeytingLean.Quantum.LoFState.reentry
def reentryK : LoFState := HeytingLean.Quantum.LoFState.kPlus

end LoFBloch

end Quantum
end HeytingLean
