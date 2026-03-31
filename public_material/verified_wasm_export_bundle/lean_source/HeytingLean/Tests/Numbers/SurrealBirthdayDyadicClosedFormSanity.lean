import HeytingLean.Numbers.Surreal.Birthday.DyadicClosedForm
import HeytingLean.Numbers.Surreal.Birthday.CanonicalDyadic

/-!
# Sanity tests for DyadicClosedForm

Validates that `dyadicSimplestForm` and the birthday-preservation theorem
agree with the concrete values proved in `CanonicalDyadic.lean`.
-/

namespace HeytingLean.Tests.Numbers

open HeytingLean.Numbers.Surreal
open HeytingLean.Numbers.Surreal.Birthday

-- 1/2: birthday 2
example : normalizedBirthday (LoFProgram.dyadicPreGame 1 1) = 2 :=
  normalizedBirthday_oneHalf

-- 3/2: birthday 3
example : normalizedBirthday (LoFProgram.dyadicPreGame 3 1) = 3 :=
  normalizedBirthday_threeHalves

-- 1/4: birthday 3
example : normalizedBirthday (LoFProgram.dyadicPreGame 1 2) = 3 :=
  normalizedBirthday_oneQuarter

-- -1/2: birthday 2
example : normalizedBirthday (LoFProgram.dyadicPreGame (-1) 1) = 2 :=
  normalizedBirthday_minusOneHalf

-- -3/2: birthday 3
example : normalizedBirthday (LoFProgram.dyadicPreGame (-3) 1) = 3 :=
  normalizedBirthday_minusThreeHalves

-- 2/4 = 1/2: birthday 2 (simplest-form reduction)
example : normalizedBirthday (LoFProgram.dyadicPreGame 2 2) = 2 :=
  normalizedBirthday_twoQuarters

-- dyadicSimplestForm concrete checks
example : dyadicSimplestForm 4 3 = (1, 1) := by native_decide
example : dyadicSimplestForm 0 5 = (0, 0) := by native_decide
example : dyadicSimplestForm 3 2 = (3, 2) := by native_decide
example : dyadicSimplestForm 6 1 = (3, 0) := by native_decide

end HeytingLean.Tests.Numbers
