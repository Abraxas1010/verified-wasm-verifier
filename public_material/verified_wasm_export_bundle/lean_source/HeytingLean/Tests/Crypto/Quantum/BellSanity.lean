import HeytingLean.Crypto.Quantum.Bell

/-!
# Test: Bell / CHSH / Tsirelson sanity

Importing the module and referencing the main theorems is the test.
-/

namespace HeytingLean.Tests.Crypto.Quantum.BellSanity

open HeytingLean.Crypto.Quantum.Bell

-- LHV bound: `|S| ≤ 2`.
example (M : HeytingLean.Crypto.Quantum.Bell.CHSH.LocalHiddenVariableModel) :
    |HeytingLean.Crypto.Quantum.Bell.CHSH.chshQuantity (M.toCorrelator)| ≤ (2 : ℝ) :=
  HeytingLean.Crypto.Quantum.Bell.CHSH.LocalHiddenVariableModel.chsh_inequality (M := M)

-- Tsirelson achievability statement exists and typechecks.
example :
    HeytingLean.Crypto.Quantum.Bell.CHSH.chshQuantity
        (HeytingLean.Crypto.Quantum.Bell.Tsirelson.Examples.tsirelsonAchievingStrategy.toCorrelator) =
      2 * Real.sqrt 2 :=
  HeytingLean.Crypto.Quantum.Bell.Tsirelson.Examples.achieves_tsirelson

end HeytingLean.Tests.Crypto.Quantum.BellSanity

