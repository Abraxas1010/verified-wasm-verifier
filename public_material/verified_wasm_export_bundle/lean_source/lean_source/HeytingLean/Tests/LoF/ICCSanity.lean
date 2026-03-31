import HeytingLean.LoF.ICC.Syntax
import HeytingLean.LoF.ICC.ConservativeEmbedding
import HeytingLean.LoF.ICC.Encodings
import HeytingLean.LoF.ICC.Reduction
import HeytingLean.Bridge.INet.ICCBasic
import HeytingLean.Bridge.INet.ICCLowering
import HeytingLean.CLI.ICCSmokeMain

namespace HeytingLean.Tests.LoF

open HeytingLean.LoF
open HeytingLean.LoF.ICC
open HeytingLean.Bridge.INet.ICC

#check Term
#check Term.size
#check Term.shiftAbove
#check Term.subst0
#check embedLegacy
#check eraseLegacy?
#check legacyY
#check Step
#check Steps
#check containsLegacyYShim
#check reduceFuel
#check checkYFree
#check Arr
#check All
#check Ind
#check ICCAgent
#check ICCNet
#check lower
#check emitJson

example : eraseLegacy? (embedLegacy .K) = some .K := by
  simp

example : eraseLegacy? (embedLegacy (.app .S .K)) = some (.app .S .K) := by
  simp

example : eraseLegacy? (.ann (.var 0) (.var 0)) = none := by
  native_decide

example : Term.shift (embedLegacy .S) 4 = embedLegacy .S := by
  simp

example : Term.subst0 (embedLegacy .K) (embedLegacy .S) = embedLegacy .S := by
  exact Term.subst0_closed (repl := embedLegacy .K) (t := embedLegacy .S) (closed_embedLegacy _)

example : step? (.app (.lam (.var 0)) (embedLegacy .K)) = some (embedLegacy .K) := by
  native_decide

example : step? (.app legacyY (embedLegacy .K)) =
    some (.app (embedLegacy .K) (.app legacyY (embedLegacy .K))) := by
  simp [step?, legacyY]

example : containsLegacyYShim (.ann (embedLegacy (.app (.app .K .S) .Y)) Set) := by
  native_decide

example : isYFree (.ann (embedLegacy (.app (.app .K .S) .Y)) Set) = false := by
  native_decide

example : reduceFuel 3 (embedLegacy (.app (.app .K .S) .Y)) = embedLegacy .S := by
  native_decide

example : checkYFree 8 HeytingLean.CLI.ICCSmokeMain.sampleTerm = false := by
  native_decide

example : ICCAgent.arity .ann = 2 := rfl
example : ICCAgent.arity .var = 0 := rfl

example : (lower (.app (.var 0) (.var 1))).agentCount = 3 := rfl

example : (lower (embedLegacy .K)).isNormalForm := by
  rfl

example : (lower (.app (.lam (.var 0)) (embedLegacy .K))).activePairs.length = 1 := by
  native_decide

example : (lower (.app (.lam (.var 0)) (embedLegacy .K))).activePairs ≠ [] := by
  native_decide

end HeytingLean.Tests.LoF
