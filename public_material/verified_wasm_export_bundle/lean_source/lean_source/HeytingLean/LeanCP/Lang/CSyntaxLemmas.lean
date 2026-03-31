import HeytingLean.LeanCP.Lang.CSyntax
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.ModEq

namespace HeytingLean.LeanCP

private theorem uintModulus_pos (sz : IntSize) : 0 < uintModulus sz := by
  cases sz <;> decide

theorem uint_add_wraps (a b : Nat) (sz : IntSize) :
    ((a % uintModulus sz) + (b % uintModulus sz)) % uintModulus sz =
      (a + b) % uintModulus sz := by
  simpa [Nat.ModEq] using
    (((Nat.mod_modEq a (uintModulus sz)).add (Nat.mod_modEq b (uintModulus sz))).symm)

theorem bitAnd_distrib_bitOr (a b c : Nat) :
    a &&& (b ||| c) = (a &&& b) ||| (a &&& c) := by
  refine Nat.eq_of_testBit_eq ?_
  intro k
  simp
  cases h1 : Nat.testBit a k <;> cases h2 : Nat.testBit b k <;> cases h3 : Nat.testBit c k <;> decide

end HeytingLean.LeanCP
