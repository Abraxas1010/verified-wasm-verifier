import Mathlib.Tactic.Positivity

set_option autoImplicit false

namespace HeytingLean.Moonshine

/-- The Monster group order, defined by its standard prime factorization. -/
def monsterOrder : Nat :=
  2^46 * 3^20 * 5^9 * 7^6 * 11^2 * 13^3 * 17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 * 71

lemma monsterOrder_pos : 0 < monsterOrder := by
  dsimp [monsterOrder]
  positivity

/-- The smallest dimension of a nontrivial faithful complex representation (used as a named constant). -/
def minFaithfulComplexRepDim : Nat := 196883

/-- The first positive coefficient in `J(q) = j(q) - 744`: `196884`. -/
def firstJCoeff : Nat := 196884

/-- The next coefficient (often quoted in moonshine tables): `21493760`. -/
def secondJCoeff : Nat := 21493760

/-- McKay's observation: `196884 = 1 + 196883`. -/
theorem mckay_identity : firstJCoeff = 1 + minFaithfulComplexRepDim := by
  decide

end HeytingLean.Moonshine
