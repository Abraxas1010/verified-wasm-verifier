import HeytingLean.Noneism.Bridges.Oscillators
import HeytingLean.Noneism.Bridges.OscillatorRestrictions

/-!
# Noneism.Bridges.OscillatorEquiv

`PrimordialTension`-preserving equivalences for oscillator carriers.
-/

namespace HeytingLean
namespace Noneism
namespace Bridges

open HeytingLean.Noneism
open HeytingLean.Information

/-- Structure-preserving oscillator equivalence. -/
structure OscillatorMorphism (α β : Type*) [PrimordialTension α] [PrimordialTension β] where
  toFun : α → β
  inv : β → α
  left_inv : ∀ x, inv (toFun x) = x
  right_inv : ∀ y, toFun (inv y) = y
  map_seed : toFun (PrimordialTension.seed (Nothing := α)) = PrimordialTension.seed (Nothing := β)
  map_step : ∀ x,
    toFun (PrimordialTension.step (Nothing := α) x) =
      PrimordialTension.step (Nothing := β) (toFun x)
  map_obs : ∀ x,
    PrimordialTension.obs (Nothing := β) (toFun x) = PrimordialTension.obs (Nothing := α) x

namespace OscillatorMorphism

variable {α β γ : Type*}
variable [PrimordialTension α] [PrimordialTension β] [PrimordialTension γ]

/-- Identity oscillator morphism. -/
def refl (α : Type*) [PrimordialTension α] : OscillatorMorphism α α where
  toFun := id
  inv := id
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  map_seed := rfl
  map_step := by intro x; rfl
  map_obs := by intro x; rfl

/-- Symmetry of oscillator morphisms. -/
def symm (m : OscillatorMorphism α β) : OscillatorMorphism β α where
  toFun := m.inv
  inv := m.toFun
  left_inv := m.right_inv
  right_inv := m.left_inv
  map_seed := by
    have h := congrArg m.inv m.map_seed
    simpa [m.left_inv, m.right_inv] using h.symm
  map_step := by
    intro y
    have h := congrArg m.inv (m.map_step (m.inv y))
    simpa [m.left_inv, m.right_inv] using h.symm
  map_obs := by
    intro y
    have h := m.map_obs (m.inv y)
    simpa [m.right_inv] using h.symm

/-- Composition of oscillator morphisms. -/
def trans (m₁ : OscillatorMorphism α β) (m₂ : OscillatorMorphism β γ) : OscillatorMorphism α γ where
  toFun := fun x => m₂.toFun (m₁.toFun x)
  inv := fun z => m₁.inv (m₂.inv z)
  left_inv := by
    intro x
    simp [m₁.left_inv, m₂.left_inv]
  right_inv := by
    intro z
    simp [m₁.right_inv, m₂.right_inv]
  map_seed := by
    calc
      m₂.toFun (m₁.toFun (PrimordialTension.seed (Nothing := α)))
          = m₂.toFun (PrimordialTension.seed (Nothing := β)) := by simp [m₁.map_seed]
      _ = PrimordialTension.seed (Nothing := γ) := m₂.map_seed
  map_step := by
    intro x
    calc
      m₂.toFun (m₁.toFun (PrimordialTension.step (Nothing := α) x))
          = m₂.toFun (PrimordialTension.step (Nothing := β) (m₁.toFun x)) := by
              simp [m₁.map_step]
      _ = PrimordialTension.step (Nothing := γ) (m₂.toFun (m₁.toFun x)) := by
              simp [m₂.map_step]
  map_obs := by
    intro x
    calc
      PrimordialTension.obs (Nothing := γ) (m₂.toFun (m₁.toFun x))
          = PrimordialTension.obs (Nothing := β) (m₁.toFun x) := by
              simp [m₂.map_obs]
      _ = PrimordialTension.obs (Nothing := α) x := by
              simp [m₁.map_obs]

end OscillatorMorphism

/-- Bool encoding of canonical iterant phases. -/
def iterantPhaseToBool (x : IterantPhase) : Bool := IterantPhase.obs x

/-- Canonical iterant phase from a bit (`false ↦ I`, `true ↦ J`). -/
def boolToIterantPhase : Bool → IterantPhase
  | false => IterantPhase.phaseIVal
  | true => IterantPhase.phaseJVal

/-- Bit encoding of information-state oscillator. -/
def infoStateToBool : InfoState → Bool := InfoStateOsc.obs

/-- Information state from a bit (`false ↦ primordial`, `true ↦ counter`). -/
def boolToInfoState : Bool → InfoState
  | false => .primordial
  | true => .counter

/-- Bit encoding of side oscillator (`false ↦ inside`, `true ↦ outside`). -/
def sideToBool : Side → Bool := SideOsc.obs

/-- Side state from a bit. -/
def boolToSide : Bool → Side
  | false => .inside
  | true => .outside

/-- Bit encoding of genesis polarity. -/
def gamePolarityToBool : GamePolarity → Bool := GamePolarity.obs

/-- Genesis polarity from a bit. -/
def boolToGamePolarity : Bool → GamePolarity
  | false => .void
  | true => .life

/-- Bit encoding of `ZeroSphere`. -/
def zeroSphereToBool : ZeroSphere → Bool := ZeroSphere.obs

/-- `ZeroSphere` value from a bit. -/
def boolToZeroSphere : Bool → ZeroSphere
  | false => .north
  | true => .south

/-- Bit encoding of `StarPlayer`. -/
def starPlayerToBool : StarPlayer → Bool := StarPlayer.obs

/-- `StarPlayer` value from a bit. -/
def boolToStarPlayer : Bool → StarPlayer
  | false => .left
  | true => .right

/-- Bit encoding of Euler restriction. -/
def eulerRestrictionToBool (x : EulerRestriction) : Bool := x.phase

/-- Euler restriction from a bit. -/
def boolToEulerRestriction (b : Bool) : EulerRestriction := ⟨b⟩

/-- Bit encoding of pre-game restriction. -/
def preGameOscillatorToBool (x : PreGameOscillatorState) : Bool := x.isComplement

/-- Pre-game restriction from a bit. -/
def boolToPreGameOscillator (b : Bool) : PreGameOscillatorState := ⟨b⟩

/-- Bit encoding of Clifford grade restriction. -/
def cliffordGradeToBool (x : CliffordGrade) : Bool := x.isOdd

/-- Clifford grade restriction from a bit. -/
def boolToCliffordGrade (b : Bool) : CliffordGrade := ⟨b⟩

/-- Bit encoding of linear polarity restriction. -/
def linearPolarityToBool (x : LinearPolarity) : Bool := x.isNegated

/-- Linear polarity restriction from a bit. -/
def boolToLinearPolarity (b : Bool) : LinearPolarity := ⟨b⟩

/-- Bit encoding of dialectica role restriction. -/
def dialecticaRoleToBool (x : DialecticaRole) : Bool := x.isChallenger

/-- Dialectica role restriction from a bit. -/
def boolToDialecticaRole (b : Bool) : DialecticaRole := ⟨b⟩

/-- Bit encoding of orthocomplement restriction. -/
def orthoPolarityToBool (x : OrthoPolarity) : Bool := x.isComplement

/-- Orthocomplement restriction from a bit. -/
def boolToOrthoPolarity (b : Bool) : OrthoPolarity := ⟨b⟩

/-- `Bool ≃ₒ IterantPhase`. -/
def morphism_bool_iterant : OscillatorMorphism Bool IterantPhase where
  toFun := boolToIterantPhase
  inv := iterantPhaseToBool
  left_inv := by intro b; cases b <;> rfl
  right_inv := by
    intro x
    rcases IterantPhase.eq_phaseIVal_or_eq_phaseJVal x with hI | hJ
    · rw [hI]
      rfl
    · rw [hJ]
      rfl
  map_seed := by rfl
  map_step := by intro b; cases b <;> rfl
  map_obs := by intro b; cases b <;> rfl

/-- `Bool ≃ₒ InfoState`. -/
def morphism_bool_infostate : OscillatorMorphism Bool InfoState where
  toFun := boolToInfoState
  inv := infoStateToBool
  left_inv := by intro b; cases b <;> rfl
  right_inv := by intro s; cases s <;> rfl
  map_seed := by rfl
  map_step := by intro b; cases b <;> rfl
  map_obs := by intro b; cases b <;> rfl

/-- `Bool ≃ₒ Side`. -/
def morphism_bool_side : OscillatorMorphism Bool Side where
  toFun := boolToSide
  inv := sideToBool
  left_inv := by intro b; cases b <;> rfl
  right_inv := by intro s; cases s <;> rfl
  map_seed := by rfl
  map_step := by intro b; cases b <;> rfl
  map_obs := by intro b; cases b <;> rfl

/-- `Bool ≃ₒ GamePolarity`. -/
def morphism_bool_genesis : OscillatorMorphism Bool GamePolarity where
  toFun := boolToGamePolarity
  inv := gamePolarityToBool
  left_inv := by intro b; cases b <;> rfl
  right_inv := by intro g; cases g <;> rfl
  map_seed := by rfl
  map_step := by intro b; cases b <;> rfl
  map_obs := by intro b; cases b <;> rfl

/-- `Bool ≃ₒ ZeroSphere`. -/
def morphism_bool_sphere : OscillatorMorphism Bool ZeroSphere where
  toFun := boolToZeroSphere
  inv := zeroSphereToBool
  left_inv := by intro b; cases b <;> rfl
  right_inv := by intro z; cases z <;> rfl
  map_seed := by rfl
  map_step := by intro b; cases b <;> rfl
  map_obs := by intro b; cases b <;> rfl

/-- `Bool ≃ₒ StarPlayer`. -/
def morphism_bool_star : OscillatorMorphism Bool StarPlayer where
  toFun := boolToStarPlayer
  inv := starPlayerToBool
  left_inv := by intro b; cases b <;> rfl
  right_inv := by intro s; cases s <;> rfl
  map_seed := by rfl
  map_step := by intro b; cases b <;> rfl
  map_obs := by intro b; cases b <;> rfl

/-- `Bool ≃ₒ EulerRestriction`. -/
def morphism_bool_euler : OscillatorMorphism Bool EulerRestriction where
  toFun := boolToEulerRestriction
  inv := eulerRestrictionToBool
  left_inv := by intro b; rfl
  right_inv := by intro x; cases x; rfl
  map_seed := by rfl
  map_step := by intro b; cases b <;> rfl
  map_obs := by intro b; cases b <;> rfl

/-- `Bool ≃ₒ PreGameOscillatorState`. -/
def morphism_bool_pregame : OscillatorMorphism Bool PreGameOscillatorState where
  toFun := boolToPreGameOscillator
  inv := preGameOscillatorToBool
  left_inv := by intro b; rfl
  right_inv := by intro x; cases x; rfl
  map_seed := by rfl
  map_step := by intro b; cases b <;> rfl
  map_obs := by intro b; cases b <;> rfl

/-- `Bool ≃ₒ CliffordGrade`. -/
def morphism_bool_clifford : OscillatorMorphism Bool CliffordGrade where
  toFun := boolToCliffordGrade
  inv := cliffordGradeToBool
  left_inv := by intro b; rfl
  right_inv := by intro x; cases x; rfl
  map_seed := by rfl
  map_step := by intro b; cases b <;> rfl
  map_obs := by intro b; cases b <;> rfl

/-- `Bool ≃ₒ LinearPolarity`. -/
def morphism_bool_linear : OscillatorMorphism Bool LinearPolarity where
  toFun := boolToLinearPolarity
  inv := linearPolarityToBool
  left_inv := by intro b; rfl
  right_inv := by intro x; cases x; rfl
  map_seed := by rfl
  map_step := by intro b; cases b <;> rfl
  map_obs := by intro b; cases b <;> rfl

/-- `Bool ≃ₒ DialecticaRole`. -/
def morphism_bool_dialectica : OscillatorMorphism Bool DialecticaRole where
  toFun := boolToDialecticaRole
  inv := dialecticaRoleToBool
  left_inv := by intro b; rfl
  right_inv := by intro x; cases x; rfl
  map_seed := by rfl
  map_step := by intro b; cases b <;> rfl
  map_obs := by intro b; cases b <;> rfl

/-- `Bool ≃ₒ OrthoPolarity`. -/
def morphism_bool_ortho : OscillatorMorphism Bool OrthoPolarity where
  toFun := boolToOrthoPolarity
  inv := orthoPolarityToBool
  left_inv := by intro b; rfl
  right_inv := by intro x; cases x; rfl
  map_seed := by rfl
  map_step := by intro b; cases b <;> rfl
  map_obs := by intro b; cases b <;> rfl

/-- Reverse orientation helper aliases. -/
abbrev morphism_iterant_bool : OscillatorMorphism IterantPhase Bool :=
  OscillatorMorphism.symm morphism_bool_iterant

abbrev morphism_infostate_bool : OscillatorMorphism InfoState Bool :=
  OscillatorMorphism.symm morphism_bool_infostate

abbrev morphism_side_bool : OscillatorMorphism Side Bool :=
  OscillatorMorphism.symm morphism_bool_side

abbrev morphism_genesis_bool : OscillatorMorphism GamePolarity Bool :=
  OscillatorMorphism.symm morphism_bool_genesis

abbrev morphism_sphere_bool : OscillatorMorphism ZeroSphere Bool :=
  OscillatorMorphism.symm morphism_bool_sphere

abbrev morphism_star_bool : OscillatorMorphism StarPlayer Bool :=
  OscillatorMorphism.symm morphism_bool_star

abbrev morphism_euler_bool : OscillatorMorphism EulerRestriction Bool :=
  OscillatorMorphism.symm morphism_bool_euler

abbrev morphism_pregame_bool : OscillatorMorphism PreGameOscillatorState Bool :=
  OscillatorMorphism.symm morphism_bool_pregame

abbrev morphism_clifford_bool : OscillatorMorphism CliffordGrade Bool :=
  OscillatorMorphism.symm morphism_bool_clifford

abbrev morphism_linear_bool : OscillatorMorphism LinearPolarity Bool :=
  OscillatorMorphism.symm morphism_bool_linear

abbrev morphism_dialectica_bool : OscillatorMorphism DialecticaRole Bool :=
  OscillatorMorphism.symm morphism_bool_dialectica

abbrev morphism_ortho_bool : OscillatorMorphism OrthoPolarity Bool :=
  OscillatorMorphism.symm morphism_bool_ortho

end Bridges
end Noneism
end HeytingLean
