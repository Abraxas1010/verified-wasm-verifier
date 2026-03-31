import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

import HeytingLean.LambdaIR.SDE
import HeytingLean.Quantum.TWA.Core

/-!
# TWA → SDE translation (Phase 2)

We translate the *laptop-scale* TWA spin model into the generic SDE IR in `HeytingLean.LambdaIR.SDE`.

Important:
- We **do not** attempt to derive drift/diffusion from a general Hamiltonian `H` here (that would
  require differential calculus). Instead, Phase 2 exposes an explicit effective field
  `B : SpinConfig N → SpinConfig N` and an explicit diffusion matrix in the coordinate basis.
- This keeps the interface honest and allows later phases to plug in physics-level derivations
  without polluting the core IR with axioms.
-/

noncomputable section

namespace HeytingLean
namespace Quantum
namespace TWA

open HeytingLean.LambdaIR.SDE

/-! ## State indexing -/

/-- State coordinates for `N` spins: `(spin index) × (x/y/z coordinate)`. -/
abbrev StateIndex (N : ℕ) : Type := Fin N × Fin 3

abbrev StateVec (N : ℕ) : Type := StateIndex N → ℝ

theorem card_stateIndex (N : ℕ) : Fintype.card (StateIndex N) = 3 * N := by
  classical
  -- `card (Fin N × Fin 3) = N * 3`; rewrite to `3 * N`.
  simp [StateIndex, Nat.mul_comm]

/-! ## SpinConfig ↔ StateVec -/

def stateVecOfSpinConfig {N : ℕ} (s : SpinConfig N) : StateVec N
  | (i, 0) => (s i).x
  | (i, 1) => (s i).y
  | (i, _) => (s i).z

def spinConfigOfStateVec {N : ℕ} (v : StateVec N) : SpinConfig N :=
  fun i => ⟨v (i, 0), v (i, 1), v (i, 2)⟩

@[simp] lemma spinConfigOfStateVec_apply_x {N : ℕ} (v : StateVec N) (i : Fin N) :
    (spinConfigOfStateVec (N := N) v i).x = v (i, 0) := rfl

@[simp] lemma spinConfigOfStateVec_apply_y {N : ℕ} (v : StateVec N) (i : Fin N) :
    (spinConfigOfStateVec (N := N) v i).y = v (i, 1) := rfl

@[simp] lemma spinConfigOfStateVec_apply_z {N : ℕ} (v : StateVec N) (i : Fin N) :
    (spinConfigOfStateVec (N := N) v i).z = v (i, 2) := rfl

@[simp] lemma spinConfigOfStateVec_stateVecOfSpinConfig {N : ℕ} (s : SpinConfig N) :
    spinConfigOfStateVec (N := N) (stateVecOfSpinConfig (N := N) s) = s := by
  funext i
  cases h : s i with
  | mk x y z =>
      simp [spinConfigOfStateVec, stateVecOfSpinConfig, h]

@[simp] lemma stateVecOfSpinConfig_spinConfigOfStateVec {N : ℕ} (v : StateVec N) :
    stateVecOfSpinConfig (N := N) (spinConfigOfStateVec (N := N) v) = v := by
  funext p
  rcases p with ⟨i, c⟩
  fin_cases c <;> rfl

/-! ## Dynamics interface -/

/-- Extra dynamics data needed to produce an SDE from a Lindblad spec.

This is the point where "paper physics" typically enters: a concrete model must supply an
effective field `B` and a diffusion matrix in the chosen coordinate basis. -/
structure Dynamics (S : LindbladSpec) where
  /-- Effective Hamiltonian field `B(s)`; drift is `B(s) × s`. -/
  field : SpinConfig S.N → SpinConfig S.N
  /-- Diffusion matrix in coordinate basis (state-dependent allowed). -/
  diffusion : SpinConfig S.N → Matrix (StateIndex S.N) (Fin S.nJumps) ℝ

namespace Dynamics

variable {S : LindbladSpec} (D : Dynamics S)

/-- Drift vector field on `StateVec`: stack `bᵢ(s) × sᵢ`. -/
def driftVec : StateVec S.N → StateVec S.N :=
  fun x =>
    let s : SpinConfig S.N := spinConfigOfStateVec (N := S.N) x
    let b : SpinConfig S.N := D.field s
    stateVecOfSpinConfig (N := S.N) (fun i => SpinVector.hamiltonianVF (b i) (s i))

/-- Diffusion matrix in the coordinate basis, transported from `SpinConfig` input. -/
def diffusionMat : StateVec S.N → Matrix (StateIndex S.N) (Fin S.nJumps) ℝ :=
  fun x =>
    let s : SpinConfig S.N := spinConfigOfStateVec (N := S.N) x
    D.diffusion s

/-- The induced SDE system on coordinate vectors. -/
def toSDESystem : SDESystem (StateIndex S.N) (Fin S.nJumps) :=
  { drift := D.driftVec
    diffusion := D.diffusionMat }

theorem drift_tangent_eachSpin (x : StateVec S.N) (i : Fin S.N) :
    let s : SpinConfig S.N := spinConfigOfStateVec (N := S.N) x
    SpinVector.dot (s i) (SpinVector.hamiltonianVF (D.field s i) (s i)) = 0 := by
  intro s
  simpa [SpinVector.hamiltonianVF] using SpinVector.dot_cross_right_self (b := D.field s i) (v := s i)

end Dynamics

end TWA
end Quantum
end HeytingLean
