import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

import HeytingLean.Quantum.LoFBloch
import HeytingLean.Quantum.QState

/-!
# Truncated Wigner Approximation (TWA) — core scaffolding

This is the **Phase 1** "structures-first" layer for the "Quantum on a Laptop" plan.

Goals:
- provide proof-friendly real 3-vectors (`SpinVector`) and the key algebraic fact that Hamiltonian
  cross-product flows are tangent to the sphere (norm-preserving at the infinitesimal level),
- provide a minimal Lindblad/TWA input record (`LindbladSpec`) with a PSD rate matrix `Γ`,
  without attempting heavy analysis (Ito/Stratonovich calculus, semigroups, etc.).
-/

noncomputable section

namespace HeytingLean
namespace Quantum
namespace TWA

/-! ## Real 3-vectors -/

/-- A real 3-vector used for classical spins / Bloch vectors. -/
structure SpinVector where
  x : ℝ
  y : ℝ
  z : ℝ

namespace SpinVector

def ofLoFState (s : LoFState) : SpinVector := ⟨s.j, s.k, s.mark⟩
def toLoFState (v : SpinVector) : LoFState := ⟨v.x, v.y, v.z⟩

@[simp] lemma ofLoFState_toLoFState (v : SpinVector) : ofLoFState (toLoFState v) = v := by
  cases v with
  | mk x y z => rfl

@[simp] lemma toLoFState_ofLoFState (s : LoFState) : toLoFState (ofLoFState s) = s := by
  cases s with
  | mk j k mark => rfl

/-- Dot product on `SpinVector`. -/
def dot (a b : SpinVector) : ℝ :=
  a.x * b.x + a.y * b.y + a.z * b.z

/-- Squared Euclidean norm. -/
def normSq (v : SpinVector) : ℝ := dot v v

/-- Unit-spin predicate (Bloch-sphere constraint). -/
def IsUnit (v : SpinVector) : Prop := normSq v = 1

/-- A unit spin vector as a subtype (useful when you want to carry the constraint explicitly). -/
abbrev UnitSpin := {v : SpinVector // IsUnit v}

/-- Cross product (right-handed). -/
def cross (a b : SpinVector) : SpinVector :=
  ⟨a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x⟩

/-- A minimal Hamiltonian vector field model: `v ↦ b × v`. -/
def hamiltonianVF (b v : SpinVector) : SpinVector := cross b v

/-- Tangency predicate for the sphere: velocity is orthogonal to the current position. -/
def tangentToSphere (pos vel : SpinVector) : Prop := dot pos vel = 0

theorem dot_cross_right_self (b v : SpinVector) : dot v (cross b v) = 0 := by
  cases v with
  | mk vx vy vz =>
    cases b with
    | mk bx by_ bz =>
      simp [dot, cross]
      ring

theorem hamiltonianVF_tangent (b v : SpinVector) :
    tangentToSphere v (hamiltonianVF b v) := by
  simpa [tangentToSphere, hamiltonianVF] using dot_cross_right_self (b := b) (v := v)

end SpinVector

/-! ## Lindblad input spec (TWA-facing) -/

/-- Minimal symbolic jump-operator tags.

We keep this as a *name-level* scaffold; the concrete operator semantics live in later phases. -/
inductive JumpOperator (N : ℕ) where
  | sigmaMinus (i : Fin N)
  | sigmaPlus (i : Fin N)
  | sigmaZ (i : Fin N)
  | custom (name : String)
deriving DecidableEq

abbrev SpinConfig (N : ℕ) := Fin N → SpinVector

/-- A Lindblad/TWA specification: a Hamiltonian on spin configurations, a jump family, and a PSD
rate/correlation matrix `Γ` (indexed by jump labels). -/
structure LindbladSpec where
  N : ℕ
  nJumps : ℕ
  H : SpinConfig N → ℝ
  jumps : Fin nJumps → JumpOperator N
  Γ : Matrix (Fin nJumps) (Fin nJumps) ℂ
  Γ_psd : HeytingLean.Quantum.PosSemidef Γ

namespace LindbladSpec

/-- Phase-1 convenience: the classical state dimension for `N` spins. -/
def dim (S : LindbladSpec) : ℕ := 3 * S.N

end LindbladSpec

end TWA
end Quantum
end HeytingLean
