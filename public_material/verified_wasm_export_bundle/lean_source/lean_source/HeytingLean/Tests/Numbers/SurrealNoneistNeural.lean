import HeytingLean.Numbers.Surreal.Experimental.NoneistNeural

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Numbers.Surreal
open HeytingLean.Numbers.SurrealCore
open HeytingLean.Numbers.Surreal.Experimental

private def t0 : AttentionToken :=
  { core := nullCut, velocity := 0, anchor := none }

private def tFast : AttentionToken :=
  { core := PreGame.build [nullCut] [], velocity := 3, anchor := none }

private def neuron0 : NoneistNeuron :=
  { gate := 2, bias := PreGame.build [nullCut] [] }

private def neuron1 : NoneistNeuron :=
  { gate := 5, bias := nullCut }

example : t0.core.birth ≤ (forwardSymbolic neuron0 t0).core.birth :=
  forwardSymbolic_birth_monotone neuron0 t0

example : tFast.core.birth ≤ (forwardSymbolic neuron0 tFast).core.birth :=
  forwardSymbolic_birth_monotone neuron0 tFast

example : t0.core.birth ≤ forwardNumeric neuron0 t0 :=
  forwardNumeric_ge_birth neuron0 t0

example : (forwardLayer neuron0 [t0, tFast]).length = 2 := by
  simp [forwardLayer]

example :
    t0.core.birth ≤ (networkForward [neuron0, neuron1] t0).core.birth :=
  networkForward_birth_monotone [neuron0, neuron1] t0

end Numbers
end Tests
end HeytingLean
