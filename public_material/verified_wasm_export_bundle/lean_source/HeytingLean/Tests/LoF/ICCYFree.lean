import HeytingLean.LoF.ICC.YFree
import HeytingLean.CLI.ICCSmokeMain

namespace HeytingLean.Tests.LoF

open HeytingLean.LoF
open HeytingLean.LoF.ICC

example : YFree (embedLegacy .K) := by
  simpa using (yFree_embedLegacy_iff .K).2 rfl

example : ¬ YFree (embedLegacy .Y) := by
  simpa [embedLegacy] using yFree_legacyY

example : isYFree (embedLegacy (.app .S .K)) = true := by
  native_decide

example : isYFree (embedLegacy (.app .K .Y)) = false := by
  native_decide

example : YFree (.app (.lam (.var 0)) (embedLegacy .K)) := by
  show isYFree (.app (.lam (.var 0)) (embedLegacy .K)) = true
  native_decide

example : checkYFree 8 HeytingLean.CLI.ICCSmokeMain.sampleTerm = false := by
  native_decide

example : checkYFree 8 (embedLegacy (.app .S .K)) = true := by
  native_decide

example : YFree (embedLegacy (.app .S .K)) := by
  simpa [YFree] using (checkYFree_sound (fuel := 8) (t := embedLegacy (.app .S .K)) (by native_decide)).1
