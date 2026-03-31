import HeytingLean.Bridge.NoCoincidence

open HeytingLean.Bridge.NoCoincidence.Basic

namespace HeytingLean.Tests.Bridge.NoCoincidence

#check RevGate.toffoliGate
#check RevCircuit.lowBitToggleCircuit

example : ¬ PropertyP 1 (RevCircuit.identity 1) :=
  identity_fails_P 1 (by decide)

example : PropertyP 1 (RevCircuit.lowBitToggleCircuit 1 (by decide)) :=
  lowBitToggle_satisfies_P 1 (by decide)

end HeytingLean.Tests.Bridge.NoCoincidence
