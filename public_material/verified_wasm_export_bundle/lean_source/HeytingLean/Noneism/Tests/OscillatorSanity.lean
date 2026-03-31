import HeytingLean.Noneism.Bridges.OscillatorRegistry

/-!
# Noneism.Tests.OscillatorSanity

Smoke tests for primordial oscillator unification.
-/

namespace HeytingLean
namespace Noneism
namespace Tests

open HeytingLean.Noneism
open HeytingLean.Noneism.Bridges
open HeytingLean.Information

#check (inferInstance : PrimordialTension Bool)
#check (inferInstance : PrimordialTension IterantPhase)
#check (inferInstance : PrimordialTension InfoState)
#check (inferInstance : PrimordialTension Side)
#check (inferInstance : PrimordialTension GamePolarity)
#check (inferInstance : PrimordialTension ZeroSphere)
#check (inferInstance : PrimordialTension StarPlayer)
#check (inferInstance : PrimordialTension EulerRestriction)
#check (inferInstance : PrimordialTension PreGameOscillatorState)
#check (inferInstance : PrimordialTension CliffordGrade)
#check (inferInstance : PrimordialTension LinearPolarity)
#check (inferInstance : PrimordialTension DialecticaRole)
#check (inferInstance : PrimordialTension OrthoPolarity)

example (b : Bool) : morphism_bool_iterant.inv (morphism_bool_iterant.toFun b) = b :=
  morphism_bool_iterant.left_inv b

example (b : Bool) : morphism_bool_infostate.inv (morphism_bool_infostate.toFun b) = b :=
  morphism_bool_infostate.left_inv b

example (b : Bool) : morphism_bool_side.inv (morphism_bool_side.toFun b) = b :=
  morphism_bool_side.left_inv b

example (b : Bool) : morphism_bool_genesis.inv (morphism_bool_genesis.toFun b) = b :=
  morphism_bool_genesis.left_inv b

example (b : Bool) : morphism_bool_sphere.inv (morphism_bool_sphere.toFun b) = b :=
  morphism_bool_sphere.left_inv b

example (b : Bool) : morphism_bool_star.inv (morphism_bool_star.toFun b) = b :=
  morphism_bool_star.left_inv b

example (b : Bool) : morphism_bool_euler.inv (morphism_bool_euler.toFun b) = b :=
  morphism_bool_euler.left_inv b

example (b : Bool) : morphism_bool_pregame.inv (morphism_bool_pregame.toFun b) = b :=
  morphism_bool_pregame.left_inv b

example (b : Bool) : morphism_bool_clifford.inv (morphism_bool_clifford.toFun b) = b :=
  morphism_bool_clifford.left_inv b

example (b : Bool) : morphism_bool_linear.inv (morphism_bool_linear.toFun b) = b :=
  morphism_bool_linear.left_inv b

example (b : Bool) : morphism_bool_dialectica.inv (morphism_bool_dialectica.toFun b) = b :=
  morphism_bool_dialectica.left_inv b

example (b : Bool) : morphism_bool_ortho.inv (morphism_bool_ortho.toFun b) = b :=
  morphism_bool_ortho.left_inv b

example : PrimordialTension.step (Nothing := Bool) (PrimordialTension.step (Nothing := Bool) false) = false := by
  decide

example (x : IterantPhase) : PrimordialTension.step (Nothing := IterantPhase) (PrimordialTension.step (Nothing := IterantPhase) x) = x := by
  exact PrimordialTension.step_step (Nothing := IterantPhase) x

example (x : InfoState) : PrimordialTension.step (Nothing := InfoState) (PrimordialTension.step (Nothing := InfoState) x) = x := by
  exact PrimordialTension.step_step (Nothing := InfoState) x

example (x : Side) : PrimordialTension.step (Nothing := Side) (PrimordialTension.step (Nothing := Side) x) = x := by
  exact PrimordialTension.step_step (Nothing := Side) x

example (x : GamePolarity) : PrimordialTension.step (Nothing := GamePolarity) (PrimordialTension.step (Nothing := GamePolarity) x) = x := by
  exact PrimordialTension.step_step (Nothing := GamePolarity) x

example (x : ZeroSphere) : PrimordialTension.step (Nothing := ZeroSphere) (PrimordialTension.step (Nothing := ZeroSphere) x) = x := by
  exact PrimordialTension.step_step (Nothing := ZeroSphere) x

example (x : StarPlayer) : PrimordialTension.step (Nothing := StarPlayer) (PrimordialTension.step (Nothing := StarPlayer) x) = x := by
  exact PrimordialTension.step_step (Nothing := StarPlayer) x

example (x : EulerRestriction) : PrimordialTension.step (Nothing := EulerRestriction) (PrimordialTension.step (Nothing := EulerRestriction) x) = x := by
  exact PrimordialTension.step_step (Nothing := EulerRestriction) x

example (x : PreGameOscillatorState) : PrimordialTension.step (Nothing := PreGameOscillatorState) (PrimordialTension.step (Nothing := PreGameOscillatorState) x) = x := by
  exact PrimordialTension.step_step (Nothing := PreGameOscillatorState) x

example (x : CliffordGrade) : PrimordialTension.step (Nothing := CliffordGrade) (PrimordialTension.step (Nothing := CliffordGrade) x) = x := by
  exact PrimordialTension.step_step (Nothing := CliffordGrade) x

example (x : LinearPolarity) : PrimordialTension.step (Nothing := LinearPolarity) (PrimordialTension.step (Nothing := LinearPolarity) x) = x := by
  exact PrimordialTension.step_step (Nothing := LinearPolarity) x

example (x : DialecticaRole) : PrimordialTension.step (Nothing := DialecticaRole) (PrimordialTension.step (Nothing := DialecticaRole) x) = x := by
  exact PrimordialTension.step_step (Nothing := DialecticaRole) x

example (x : OrthoPolarity) : PrimordialTension.step (Nothing := OrthoPolarity) (PrimordialTension.step (Nothing := OrthoPolarity) x) = x := by
  exact PrimordialTension.step_step (Nothing := OrthoPolarity) x

#check thm_sheaf_glue_oscillator_bool_to_oscillator_iterant
#check thm_sheaf_glue_oscillator_star_to_oscillator_clifford
#check thm_sheaf_glue_oscillator_ortho_to_oscillator_dialectica

#eval (EulerRestriction.step ⟨false⟩).phase
#eval (PreGameOscillatorState.step ⟨true⟩).isComplement
#eval GamePolarity.obs (GamePolarity.step GamePolarity.void)

def allOscillatorTags : List OscillatorTag :=
  [OscillatorTag.bool, OscillatorTag.iterant, OscillatorTag.infoState,
   OscillatorTag.side, OscillatorTag.genesis, OscillatorTag.sphere,
   OscillatorTag.star, OscillatorTag.euler, OscillatorTag.preGame,
   OscillatorTag.clifford, OscillatorTag.linear,
   OscillatorTag.dialectica, OscillatorTag.ortho]

example : allOscillatorTags.length = 13 := by decide

end Tests
end Noneism
end HeytingLean
