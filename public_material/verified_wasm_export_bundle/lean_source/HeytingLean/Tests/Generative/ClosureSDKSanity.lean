import HeytingLean.Generative.SpinorBridge.ClosureSDK
import HeytingLean.ClosingTheLoop.Semantics.ClosureSDKBridge

open scoped Quaternion
open HeytingLean.Generative.SpinorBridge.ClosureSDK
open HeytingLean.ClosingTheLoop.Semantics

#check quaternion_noncommutative
#check scalar_vector_decomp
#check sigma_one
#check closureSDKNucleus_fixed_iff
#check sigma_zero_of_mem_coherencePoles
#check su2_generator_unit_quaternion_bridge

example : quatI * quatJ = quatK :=
  quatI_mul_quatJ

example : scalarPart quatI = 0 :=
  scalarPart_quatI

example : vectorPart quatI = quatI :=
  vectorPart_quatI

example : sigma (1 : Q) = 0 :=
  sigma_one

example : sigma (-1 : Q) = 0 :=
  sigma_neg_one

example : sigma quatI = Real.pi :=
  sigma_quatI

example : hopfProject quatI 2 = -1 :=
  hopfProject_quatI_two

example : hopfProject (1 : Q) 2 = 1 :=
  hopfProject_one_two

example : hopfPhase quatI = Real.pi :=
  hopfPhase_quatI

example : hopfProject quatUniform 0 = 1 :=
  hopfProject_quatUniform_zero

example : hopfProject quatUniform 1 = 0 :=
  hopfProject_quatUniform_one

example : hopfProject quatUniform 2 = 0 :=
  hopfProject_quatUniform_two

example : hopfPhase quatUniform = Real.pi / 2 :=
  hopfPhase_quatUniform

example : ‖quatUniform‖ = 1 :=
  quatUniform_norm

example : Function.Injective generatorQuaternion :=
  generatorQuaternion_injective

example : scalarPart (generatorQuaternion .x : Q) = 0 :=
  scalarPart_generatorQuaternion .x

example : (generatorQuaternion .x : Q) * (generatorQuaternion .y : Q) = (generatorQuaternion .z : Q) :=
  by simp [generatorQuaternion]

example : coherencePoles ⊆ closureSDKNucleus (∅ : Set ClosureSDKQ) := by
  exact coherencePoles_subset_closed ∅

example :
    HeytingLean.Generative.SpinorBridge.ClosureSDK.sigma (1 : ClosureSDKQ) = 0 := by
  exact sigma_zero_of_mem_coherencePoles (by simp [coherencePoles])
