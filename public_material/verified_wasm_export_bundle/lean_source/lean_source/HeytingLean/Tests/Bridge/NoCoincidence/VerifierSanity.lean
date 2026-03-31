import HeytingLean.Bridge.NoCoincidence

open HeytingLean.Bridge.NoCoincidence.Basic
open HeytingLean.Bridge.NoCoincidence.Nucleus

namespace HeytingLean.Tests.Bridge.NoCoincidence

def lowBitC : RevCircuit 1 := RevCircuit.lowBitToggleCircuit 1 (by decide)

#eval candidateScreen 1 lowBitC "size"
#eval candidateScreen 1 lowBitC "involution"
#eval candidateScreen 1 (RevCircuit.identity 1) "size"
#eval candidateVerifier 1 lowBitC "size"
#eval candidateVerifier 1 lowBitC "property"

example : candidateScreen 1 lowBitC "size" = true := by
  exact candidateScreen_complete_of_small 1 lowBitC
    (by simp [lowBitC, smallCircuit, RevCircuit.lowBitToggleCircuit, RevCircuit.singleton,
      RevCircuit.size])
    (lowBitToggle_satisfies_P 1 (by decide))

example : candidateScreen 1 lowBitC "involution" = true := by
  apply candidateScreen_complete_of_involution
  · intro x
    simpa [lowBitC, RevCircuit.lowBitToggleCircuit, RevCircuit.singleton,
      RevCircuit.eval, RevCircuit.evalSteps] using
      (RevGate.toggleLowBitGate 1 (by decide)).left_inv x
  · exact lowBitToggle_satisfies_P 1 (by decide)

example : candidateVerifier 1 lowBitC "size" = false := by
  simp [candidateVerifier]

example : candidateVerifier 1 lowBitC "property" = true := by
  exact candidateVerifier_complete_of_property 1 lowBitC (lowBitToggle_satisfies_P 1 (by decide))

end HeytingLean.Tests.Bridge.NoCoincidence
