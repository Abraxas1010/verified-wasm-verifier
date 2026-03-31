import HeytingLean.LoF.Combinators.Differential.Derivative
import HeytingLean.ProgramCalculus.AdelicOpsInstances.SKYAdelic
import HeytingLean.ProgramCalculus.AdelicFutamura
import HeytingLean.Tropical.ReLU
import HeytingLean.ActiveInference.FreeEnergy
import HeytingLean.LoF.Combinators.Topos.SheafNeuralNet

/-!
# Integration: Organic Alignment Stack (compile-time)

This module is a compile-time integration check for the cross-slice “stack”:

Tropical → Differential → Adelic → Futamura → Sheaf.

The goal is to ensure the named hooks exist and can be imported together.
-/

#check HeytingLean.LoF.Combinators.Differential.S_derivative_correct
#check HeytingLean.LoF.Combinators.Differential.dualApp_chainRule_consistent
#check HeytingLean.ProgramCalculus.AdelicOpsInstances.skyAdelicProgramOps
#check HeytingLean.ProgramCalculus.futamura_preserves_reconstruction
#check HeytingLean.Tropical.relu_is_tropical
#check HeytingLean.ActiveInference.freeEnergy_bounds_surprise
#check HeytingLean.LoF.Combinators.Topos.sheaf_diffusion_converges

