import HeytingLean.Numbers.Goldbach.Core

/-
Basic compliance checks for Goldbach core predicates.

These tests keep to tiny explicit examples (4, 6, 8, 9, …) to ensure
that the `isGoldbachPair` / `isGoldbachTriple` predicates are usable
and behave as expected on concrete values.  No global conjectures are
assumed here.
-/

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Numbers
open HeytingLean.Numbers.Goldbach

/-- Sanity check: 2 is prime in the sense used by Goldbach predicates. -/
lemma prime_two : Nat.Prime 2 := by
  decide

/-- Sanity check: 3 and 5 are prime. -/
lemma prime_three : Nat.Prime 3 := by
  decide

lemma prime_five : Nat.Prime 5 := by
  decide

/-- The smallest even number `4` admits the Goldbach decomposition `4 = 2 + 2`. -/
lemma four_isGoldbach :
    isGoldbachPair 4 2 2 := by
  unfold isGoldbachPair
  refine And.intro ?h2 (And.intro ?h2' ?hsum)
  · exact prime_two
  · exact prime_two
  · decide

/-- The even number `6` admits the Goldbach decomposition `6 = 3 + 3`. -/
lemma six_isGoldbach :
    isGoldbachPair 6 3 3 := by
  unfold isGoldbachPair
  refine And.intro ?h3 (And.intro ?h3' ?hsum)
  · exact prime_three
  · exact prime_three
  · decide

/-- The even number `8` admits the Goldbach decomposition `8 = 3 + 5`. -/
lemma eight_isGoldbach :
    isGoldbachPair 8 3 5 := by
  unfold isGoldbachPair
  refine And.intro ?h3 (And.intro ?h5 ?hsum)
  · exact prime_three
  · exact prime_five
  · decide

/-- A tiny weak-Goldbach-style example: `9 = 3 + 3 + 3`. -/
lemma nine_isGoldbachTriple :
    isGoldbachTriple 9 3 3 3 := by
  unfold isGoldbachTriple
  refine And.intro ?h3 (And.intro ?h3' (And.intro ?h3'' ?hsum))
  · exact prime_three
  · exact prime_three
  · exact prime_three
  · decide

end Numbers
end Tests
end HeytingLean

