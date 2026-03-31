import HeytingLean.LoF.ICC.UnrestrictedY

open HeytingLean.LoF.ICC

example : Term.Closed legacyYOrbit0 := by
  simpa [legacyYOrbit0] using closed_legacyYSelfChain 0

example : ¬ YFree legacyYOrbit1 := by
  simpa [legacyYOrbit1] using not_yFree_legacyYSelfChain 1

example : step? legacyYOrbit0 = some legacyYOrbit1 := by
  exact step?_legacyYOrbit0

example : step? legacyYOrbit3 = some legacyYOrbit4 := by
  exact step?_legacyYOrbit3

example : reduceFuel 4 legacyYOrbit0 = legacyYOrbit4 := by
  simpa using unrestrictedY_bounded_operational_prefix

example : Term.size legacyYOrbit2 < Term.size legacyYOrbit3 := by
  simpa using legacyYOrbit_size_growth_23

example : legacyYSelfChain 2 ≠ legacyYOrbit2 := by
  exact legacyYSelfChain_two_ne_legacyYOrbit2

example : step? (legacyYOrbit 7) = some (legacyYOrbit 8) := by
  exact step?_legacyYOrbit 7

example : Term.size (legacyYOrbit 6) < Term.size (legacyYOrbit 7) := by
  exact legacyYOrbit_size_growth 6

example : unrestrictedYFinalVerdict = .refuted unrestrictedYRefutation := by
  exact unrestrictedY_final_verdict_refuted
