import HeytingLean.Generative.SpinorBridge.ClosureSDK.HopfCoordinates
import HeytingLean.Generative.SpinorBridge.DimensionalityFromSU2

/-
# Closure-SDK unit quaternions and SU2-compatible generator bridge

This module promotes the existing Closure-SDK quaternion carrier to a genuine
unit-quaternion layer and records the smallest honest compatibility facts with
the existing `SpinorBridge` SU2 generator surface.
-/

noncomputable section

open scoped Quaternion
open HeytingLean.Generative.SpinorBridge

namespace HeytingLean.Generative.SpinorBridge.ClosureSDK

/-- Unit quaternions on the Closure-SDK carrier. -/
abbrev UnitQuaternion := {q : Q // ‖q‖ = 1}

@[simp] theorem quatI_normSq : Quaternion.normSq quatI = 1 := by
  norm_num [Quaternion.normSq_def', quatI]

@[simp] theorem quatJ_normSq : Quaternion.normSq quatJ = 1 := by
  norm_num [Quaternion.normSq_def', quatJ]

@[simp] theorem quatK_normSq : Quaternion.normSq quatK = 1 := by
  norm_num [Quaternion.normSq_def', quatK]

@[simp] theorem quatUniform_normSq : Quaternion.normSq quatUniform = 1 := by
  norm_num [Quaternion.normSq_def', quatUniform]

@[simp] theorem quatI_norm : ‖quatI‖ = 1 := by
  have hsq : ‖quatI‖ * ‖quatI‖ = 1 := by
    rw [← Quaternion.normSq_eq_norm_mul_self, quatI_normSq]
  nlinarith [norm_nonneg quatI, hsq]

@[simp] theorem quatJ_norm : ‖quatJ‖ = 1 := by
  have hsq : ‖quatJ‖ * ‖quatJ‖ = 1 := by
    rw [← Quaternion.normSq_eq_norm_mul_self, quatJ_normSq]
  nlinarith [norm_nonneg quatJ, hsq]

@[simp] theorem quatK_norm : ‖quatK‖ = 1 := by
  have hsq : ‖quatK‖ * ‖quatK‖ = 1 := by
    rw [← Quaternion.normSq_eq_norm_mul_self, quatK_normSq]
  nlinarith [norm_nonneg quatK, hsq]

@[simp] theorem quatUniform_norm : ‖quatUniform‖ = 1 := by
  have hsq : ‖quatUniform‖ * ‖quatUniform‖ = 1 := by
    rw [← Quaternion.normSq_eq_norm_mul_self, quatUniform_normSq]
  nlinarith [norm_nonneg quatUniform, hsq]

/-- The quaternion basis elements as unit quaternions. -/
def quatIUnit : UnitQuaternion := ⟨quatI, quatI_norm⟩
def quatJUnit : UnitQuaternion := ⟨quatJ, quatJ_norm⟩
def quatKUnit : UnitQuaternion := ⟨quatK, quatK_norm⟩
def quatUniformUnit : UnitQuaternion := ⟨quatUniform, quatUniform_norm⟩

@[simp] theorem quatIUnit_val : (quatIUnit : Q) = quatI := rfl
@[simp] theorem quatJUnit_val : (quatJUnit : Q) = quatJ := rfl
@[simp] theorem quatKUnit_val : (quatKUnit : Q) = quatK := rfl
@[simp] theorem quatUniformUnit_val : (quatUniformUnit : Q) = quatUniform := rfl

theorem quatI_ne_quatJ : quatI ≠ quatJ := by
  intro h
  have himI := congrArg (fun q : Q => q.imI) h
  norm_num [quatI, quatJ] at himI

theorem quatI_ne_quatK : quatI ≠ quatK := by
  intro h
  have himI := congrArg (fun q : Q => q.imI) h
  norm_num [quatI, quatK] at himI

theorem quatJ_ne_quatK : quatJ ≠ quatK := by
  intro h
  have himJ := congrArg (fun q : Q => q.imJ) h
  norm_num [quatJ, quatK] at himJ

/-- The three SU(2) generators viewed as unit quaternions. -/
def generatorQuaternion : SU2Generator → UnitQuaternion
  | .x => quatIUnit
  | .y => quatJUnit
  | .z => quatKUnit

@[simp] theorem generatorQuaternion_x : generatorQuaternion .x = quatIUnit := rfl
@[simp] theorem generatorQuaternion_y : generatorQuaternion .y = quatJUnit := rfl
@[simp] theorem generatorQuaternion_z : generatorQuaternion .z = quatKUnit := rfl

theorem generatorQuaternion_injective : Function.Injective generatorQuaternion := by
  intro a b h
  cases a <;> cases b <;> try rfl
  · exfalso
    exact quatI_ne_quatJ (by simpa using congrArg (fun q : UnitQuaternion => (q : Q)) h)
  · exfalso
    exact quatI_ne_quatK (by simpa using congrArg (fun q : UnitQuaternion => (q : Q)) h)
  · exfalso
    exact quatI_ne_quatJ (by simpa using congrArg (fun q : UnitQuaternion => (q : Q)) h.symm)
  · exfalso
    exact quatJ_ne_quatK (by simpa using congrArg (fun q : UnitQuaternion => (q : Q)) h)
  · exfalso
    exact quatI_ne_quatK (by simpa using congrArg (fun q : UnitQuaternion => (q : Q)) h.symm)
  · exfalso
    exact quatJ_ne_quatK (by simpa using congrArg (fun q : UnitQuaternion => (q : Q)) h.symm)

@[simp] theorem scalarPart_generatorQuaternion (g : SU2Generator) :
    scalarPart (generatorQuaternion g : Q) = 0 := by
  cases g <;> simp [generatorQuaternion]

@[simp] theorem star_generatorQuaternion (g : SU2Generator) :
    star (generatorQuaternion g : Q) = -(generatorQuaternion g : Q) := by
  cases g <;> simp [generatorQuaternion]

/-- Honest compatibility summary: the three SU(2) generators correspond to three distinct
unit pure-imaginary quaternion directions with the expected quaternion multiplication law. -/
theorem su2_generator_unit_quaternion_bridge :
    Function.Injective generatorQuaternion ∧
      scalarPart (generatorQuaternion .x : Q) = 0 ∧
      scalarPart (generatorQuaternion .y : Q) = 0 ∧
      scalarPart (generatorQuaternion .z : Q) = 0 ∧
      ((generatorQuaternion .x : Q) * (generatorQuaternion .y : Q) =
        (generatorQuaternion .z : Q)) ∧
      Fintype.card SU2Generator = 3 := by
  refine ⟨generatorQuaternion_injective, ?_, ?_, ?_, ?_, su2_generator_count⟩
  · simp
  · simp
  · simp
  · simp [generatorQuaternion]

end HeytingLean.Generative.SpinorBridge.ClosureSDK
