import HeytingLean.Genesis

/-!
# Genesis Virtual Oscillation Sanity
-/

namespace HeytingLean.Tests.Genesis

open HeytingLean.Genesis

#check dnot
#check dnot_dnot
#check dnot_phaseI
#check dnot_phaseJ
#check dnot_fixedPoints
#check evalLife_true_eq_J
#check evalLife_false_eq_I

example : dnot phaseI = phaseI := dnot_phaseI

example : dnot phaseJ = phaseJ := dnot_phaseJ

example : dnot (dnot phaseI) = phaseI := by
  exact dnot_dnot phaseI

example : evalLife true = phaseJ := evalLife_true_eq_J

example : evalLife false = phaseI := evalLife_false_eq_I

example (x : Iterant Bool) (hx : dnot x = x) : x = phaseI ∨ x = phaseJ :=
  dnot_fixedPoints x hx

end HeytingLean.Tests.Genesis
