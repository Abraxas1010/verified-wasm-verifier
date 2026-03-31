import HeytingLean.CDL.RNucleusPolynomial

namespace HeytingLean.HeytingVeil.Monadic

open HeytingLean.CDL

/-- P1 monadic hook: expose the `Option` monad polynomial as a HeytingVeil lane input. -/
def optionLanePoly (A : Type) : CategoryTheory.Polynomial.Poly :=
  optionMonadPoly.asPoly A

/-- First monadic theorem: Option lane uses Bool positions. -/
theorem optionLanePosBool (A : Type) : (optionLanePoly A).pos = Bool :=
  rfl

end HeytingLean.HeytingVeil.Monadic
