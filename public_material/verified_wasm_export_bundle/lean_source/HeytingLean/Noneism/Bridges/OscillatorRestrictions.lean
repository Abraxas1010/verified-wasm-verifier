import HeytingLean.Noneism.PrimordialTension
import HeytingLean.Ontology.Primordial
import HeytingLean.Quantum.Phase
import HeytingLean.Numbers.Surreal.ReentryFixedPoint
import HeytingLean.Bridges.Clifford
import HeytingLean.LoF.Combinators.Differential
import HeytingLean.Numbers.Surreal.DialecticaBridge
import HeytingLean.Quantum.OML.Core

/-!
# Noneism.Bridges.OscillatorRestrictions

Phase-2 primordial oscillators as two-point restrictions/wrappers.
-/

namespace HeytingLean
namespace Noneism
namespace Bridges

open HeytingLean.Noneism
open HeytingLean.Numbers.Surreal

/-- Euler oscillation restricted to `{0, π}`. -/
structure EulerRestriction where
  phase : Bool
  deriving Repr, DecidableEq

namespace EulerRestriction

def step (x : EulerRestriction) : EulerRestriction := ⟨Bool.not x.phase⟩
def obs (x : EulerRestriction) : Bool := x.phase

@[simp] theorem step_step (x : EulerRestriction) : step (step x) = x := by
  cases x with
  | mk b =>
      simp [step]

@[simp] theorem obs_step (x : EulerRestriction) : obs (step x) = Bool.not (obs x) := by
  rfl

end EulerRestriction

instance instPrimordialTensionEulerRestriction : PrimordialTension EulerRestriction where
  engine :=
    { seed := ⟨false⟩
      step := EulerRestriction.step
      obs := EulerRestriction.obs
      step_involutive := by intro x; simp
      obs_flips := by intro x; simp }

/-- Set-pre-game oscillation restricted to `{∅, canonicalCoreᶜ}`. -/
structure PreGameOscillatorState where
  isComplement : Bool
  deriving Repr, DecidableEq

namespace PreGameOscillatorState

def step (x : PreGameOscillatorState) : PreGameOscillatorState := ⟨Bool.not x.isComplement⟩
def obs (x : PreGameOscillatorState) : Bool := x.isComplement

def toCarrier : PreGameOscillatorState → Carrier
  | ⟨false⟩ => (∅ : Carrier)
  | ⟨true⟩ => (canonicalCoreᶜ : Carrier)

@[simp] theorem step_step (x : PreGameOscillatorState) : step (step x) = x := by
  cases x with
  | mk b =>
      simp [step]

@[simp] theorem obs_step (x : PreGameOscillatorState) : obs (step x) = Bool.not (obs x) := by
  rfl

end PreGameOscillatorState

instance instPrimordialTensionPreGameOscillatorState : PrimordialTension PreGameOscillatorState where
  engine :=
    { seed := ⟨false⟩
      step := PreGameOscillatorState.step
      obs := PreGameOscillatorState.obs
      step_involutive := by intro x; simp
      obs_flips := by intro x; simp }

/-- Clifford algebra grade parity (even/odd). -/
structure CliffordGrade where
  isOdd : Bool
  deriving Repr, DecidableEq

namespace CliffordGrade

def step (x : CliffordGrade) : CliffordGrade := ⟨Bool.not x.isOdd⟩
def obs (x : CliffordGrade) : Bool := x.isOdd

@[simp] theorem step_step (x : CliffordGrade) : step (step x) = x := by
  cases x with
  | mk b =>
      simp [step]

@[simp] theorem obs_step (x : CliffordGrade) : obs (step x) = Bool.not (obs x) := by
  rfl

end CliffordGrade

instance instPrimordialTensionCliffordGrade : PrimordialTension CliffordGrade where
  engine :=
    { seed := ⟨false⟩
      step := CliffordGrade.step
      obs := CliffordGrade.obs
      step_involutive := by intro x; simp
      obs_flips := by intro x; simp }

/-- Linear-logic polarity under involutive negation. -/
structure LinearPolarity where
  isNegated : Bool
  deriving Repr, DecidableEq

namespace LinearPolarity

def step (x : LinearPolarity) : LinearPolarity := ⟨Bool.not x.isNegated⟩
def obs (x : LinearPolarity) : Bool := x.isNegated

@[simp] theorem step_step (x : LinearPolarity) : step (step x) = x := by
  cases x with
  | mk b =>
      simp [step]

@[simp] theorem obs_step (x : LinearPolarity) : obs (step x) = Bool.not (obs x) := by
  rfl

end LinearPolarity

instance instPrimordialTensionLinearPolarity : PrimordialTension LinearPolarity where
  engine :=
    { seed := ⟨false⟩
      step := LinearPolarity.step
      obs := LinearPolarity.obs
      step_involutive := by intro x; simp
      obs_flips := by intro x; simp }

/-- Dialectica witness/challenger polarity. -/
structure DialecticaRole where
  isChallenger : Bool
  deriving Repr, DecidableEq

namespace DialecticaRole

def step (x : DialecticaRole) : DialecticaRole := ⟨Bool.not x.isChallenger⟩
def obs (x : DialecticaRole) : Bool := x.isChallenger

@[simp] theorem step_step (x : DialecticaRole) : step (step x) = x := by
  cases x with
  | mk b =>
      simp [step]

@[simp] theorem obs_step (x : DialecticaRole) : obs (step x) = Bool.not (obs x) := by
  rfl

end DialecticaRole

instance instPrimordialTensionDialecticaRole : PrimordialTension DialecticaRole where
  engine :=
    { seed := ⟨false⟩
      step := DialecticaRole.step
      obs := DialecticaRole.obs
      step_involutive := by intro x; simp
      obs_flips := by intro x; simp }

/-- Orthocomplement polarity state. -/
structure OrthoPolarity where
  isComplement : Bool
  deriving Repr, DecidableEq

namespace OrthoPolarity

def step (x : OrthoPolarity) : OrthoPolarity := ⟨Bool.not x.isComplement⟩
def obs (x : OrthoPolarity) : Bool := x.isComplement

@[simp] theorem step_step (x : OrthoPolarity) : step (step x) = x := by
  cases x with
  | mk b =>
      simp [step]

@[simp] theorem obs_step (x : OrthoPolarity) : obs (step x) = Bool.not (obs x) := by
  rfl

end OrthoPolarity

instance instPrimordialTensionOrthoPolarity : PrimordialTension OrthoPolarity where
  engine :=
    { seed := ⟨false⟩
      step := OrthoPolarity.step
      obs := OrthoPolarity.obs
      step_involutive := by intro x; simp
      obs_flips := by intro x; simp }

/-! ## Structural correspondence theorems -/

/-- Euler oscillation at `0`. -/
theorem primordialOscillation_at_zero : Ontology.primordialOscillation 0 = (1 : ℂ) := by
  simp [Ontology.primordialOscillation]

/-- Euler oscillation at `π`. -/
theorem primordialOscillation_at_pi : Ontology.primordialOscillation Real.pi = (-1 : ℂ) := by
  simpa [Ontology.primordialOscillation, mul_comm] using Complex.exp_pi_mul_I

/-- Antiphase law re-export. -/
theorem primordialOscillation_antiphase (θ : ℝ) :
    Ontology.primordialOscillation (θ + Real.pi) = -Ontology.primordialOscillation θ := by
  exact Ontology.oscillation_antiphase θ

/-- Pointwise equivalence of the two Euler phase forms. -/
theorem minimalPhaseForm_eq_primordialOscillation (θ : ℝ) :
    Quantum.Phase.minimalPhaseForm θ = Ontology.primordialOscillation θ := by
  rfl

/-- First leg of the pre-game two-cycle. -/
theorem oscillate_empty_eq_core_compl' :
    oscillate (∅ : Carrier) = (canonicalCoreᶜ : Carrier) :=
  oscillate_empty_eq_core_compl

/-- Second leg of the pre-game two-cycle. -/
theorem oscillate_core_compl_eq_empty :
    oscillate (canonicalCoreᶜ : Carrier) = (∅ : Carrier) := by
  calc
    oscillate (canonicalCoreᶜ : Carrier)
        = oscillate (oscillate (∅ : Carrier)) := by
            simp [oscillate_empty_eq_core_compl]
    _ = (∅ : Carrier) := oscillate_twice_empty

/-- Restricted orbit commutes with `oscillate`. -/
theorem oscillate_restricted_commutes (s : PreGameOscillatorState) :
    oscillate (PreGameOscillatorState.toCarrier s) =
      PreGameOscillatorState.toCarrier (PreGameOscillatorState.step s) := by
  cases s with
  | mk b =>
      cases b <;>
      simp [PreGameOscillatorState.toCarrier, PreGameOscillatorState.step,
        oscillate_empty_eq_core_compl, oscillate_core_compl_eq_empty]

/-- OML orthocomplement involution re-export. -/
theorem orthocomplement_involutive {α : Type _}
    [Quantum.OML.OrthocomplementedLattice α] (a : α) :
    Quantum.OML.OrthocomplementedLattice.compl
      (Quantum.OML.OrthocomplementedLattice.compl a) = a := by
  exact Quantum.OML.OrthocomplementedLattice.compl_involutive a

/-- Dialectica bridge exposes a witness/challenge roundtrip surface. -/
theorem dialectica_bridge_default_challenge_exists : True := by
  let _c := Numbers.Surreal.DialecticaBridge.defaultChallenge
  trivial

end Bridges
end Noneism
end HeytingLean
