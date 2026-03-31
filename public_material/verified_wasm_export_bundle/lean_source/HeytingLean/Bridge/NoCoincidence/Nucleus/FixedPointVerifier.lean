import HeytingLean.Bridge.NoCoincidence.Nucleus.AdviceAsNucleus

namespace HeytingLean.Bridge.NoCoincidence.Nucleus

open HeytingLean.Bridge.NoCoincidence.Basic

theorem candidateVerifier_sound (n : ℕ) (C : RevCircuit n) (π : String)
    (hAccept : candidateVerifier n C π = true) :
    PropertyP n C := by
  rcases (candidateVerifier_eq_true_iff n C π).1 hAccept with ⟨R, _, hExplain⟩
  exact R.certifies C hExplain

/-- The direct executable screen accepts the `size` lens when both the lens and `PropertyP` hold. -/
theorem candidateScreen_complete_of_small (n : ℕ) (C : RevCircuit n)
    (hSize : smallCircuit n C) (hP : PropertyP n C) :
    candidateScreen n C "size" = true := by
  unfold candidateScreen
  simp [hSize, hP]

/-- The direct executable screen accepts the `involution` lens when both the lens and `PropertyP`
hold. -/
theorem candidateScreen_complete_of_involution (n : ℕ) (C : RevCircuit n)
    (hInv : involutiveCircuit n C) (hP : PropertyP n C) :
    candidateScreen n C "involution" = true := by
  unfold candidateScreen
  simp [hInv, hP]

/-- The direct executable screen accepts the `property` lens whenever `PropertyP` holds. -/
theorem candidateScreen_complete_of_property (n : ℕ) (C : RevCircuit n)
    (hP : PropertyP n C) :
    candidateScreen n C "property" = true := by
  unfold candidateScreen propertyFocus
  simp [hP]

/-- The structural verifier is complete for the currently certified `property` advice lens. -/
theorem candidateVerifier_complete_of_property (n : ℕ) (C : RevCircuit n)
    (hP : PropertyP n C) :
    candidateVerifier n C "property" = true := by
  unfold candidateVerifier propertyFocus
  simp [hP]

end HeytingLean.Bridge.NoCoincidence.Nucleus
