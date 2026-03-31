import HeytingLean.Quantum.LoFCircuit

namespace HeytingLean
namespace Tests
namespace Quantum

open HeytingLean.Quantum

/-! Quick compile-time regressions for the LoF↔Bloch laptop core. -/

example : runCircuit createPlus LoFState.void = LoFState.reentry := by
  simpa using createPlus_correct

example (s : LoFState) : poissonCoord 0 1 s = s.mark := by
  simp

example (s : LoFState) : poissonCoord 1 2 s = s.j := by
  simp

example (s : LoFState) : poissonCoord 2 0 s = s.k := by
  simp

end Quantum
end Tests
end HeytingLean

