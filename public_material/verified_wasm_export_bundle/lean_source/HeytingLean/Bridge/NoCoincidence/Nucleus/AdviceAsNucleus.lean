import HeytingLean.Bridge.NoCoincidence.Nucleus.CircuitNucleus

namespace HeytingLean.Bridge.NoCoincidence.Nucleus

open HeytingLean.Bridge.NoCoincidence.Basic

/-- The CNCC property itself can be used as a focus lens: these are the circuits already known to
avoid the zero-suffix coincidence. -/
def propertyFocus (n : ℕ) : CircuitProp n :=
  Basic.PropertyP n

/-- Canonical nuclei attached to the three advice lenses used in this development. -/
def sizeNucleus (n : ℕ) : CircuitNucleus n :=
  mkFocusNucleus "size" (smallCircuit n)

def involutionNucleus (n : ℕ) : CircuitNucleus n :=
  mkFocusNucleus "involution" (involutiveCircuit n)

def propertyNucleus (n : ℕ) : CircuitNucleus n :=
  mkFocusNucleus "property" (propertyFocus n)

/-- Parse an advice string as a nucleus choice. -/
def nucleusFromAdvice (n : ℕ) (π : String) : Option (CircuitNucleus n) :=
  if π = "size" then
    some (sizeNucleus n)
  else if π = "involution" then
    some (involutionNucleus n)
  else if π = "property" then
    some (propertyNucleus n)
  else
    none

instance instDecidablePropertyP (n : ℕ) (C : RevCircuit n) : Decidable (Basic.PropertyP n C) := by
  unfold Basic.PropertyP
  infer_instance

instance instDecidableSmallCircuit (n : ℕ) (C : RevCircuit n) :
    Decidable (smallCircuit n C) := by
  unfold smallCircuit
  infer_instance

instance instDecidableInvolutiveCircuit (n : ℕ) (C : RevCircuit n) :
    Decidable (involutiveCircuit n C) := by
  unfold involutiveCircuit
  infer_instance

instance instDecidablePropertyFocus (n : ℕ) (C : RevCircuit n) :
    Decidable (propertyFocus n C) := by
  unfold propertyFocus
  infer_instance

/-- A direct finite screen combining the advice-selected lens with an explicit `PropertyP` check.
This is useful for executable examples, but it is not a structural verifier in Neyman's sense
because it still decides the target property directly. -/
def candidateScreen (n : ℕ) (C : RevCircuit n) (π : String) : Bool :=
  if π = "size" then
    decide (smallCircuit n C ∧ Basic.PropertyP n C)
  else if π = "involution" then
    decide (involutiveCircuit n C ∧ Basic.PropertyP n C)
  else if π = "property" then
    decide (propertyFocus n C ∧ Basic.PropertyP n C)
  else
    false

/-- The executable screen succeeds exactly when the parsed advice lens explains the circuit and the
target property also holds. -/
theorem candidateScreen_eq_true_iff (n : ℕ) (C : RevCircuit n) (π : String) :
    candidateScreen n C π = true ↔
      ∃ R, nucleusFromAdvice n π = some R ∧ R.explains C ∧ Basic.PropertyP n C := by
  classical
  unfold candidateScreen nucleusFromAdvice
  by_cases hπ : π = "size"
  · simp [hπ, sizeNucleus, mkFocusNucleus, smallCircuit, CircuitNucleus.explains]
  · by_cases hπ' : π = "involution"
    · simp [hπ', involutionNucleus, mkFocusNucleus, involutiveCircuit, CircuitNucleus.explains]
    · by_cases hπ'' : π = "property"
      · simp [hπ'', propertyNucleus, propertyFocus, mkFocusNucleus,
          CircuitNucleus.explains]
      · simp [hπ, hπ', hπ'']

/-- Advice lenses that come with a proof that structural explanation implies `PropertyP`. -/
structure CertifiedCircuitNucleus (n : ℕ) where
  nucleus : CircuitNucleus n
  certifies : ∀ C, nucleus.explains C → Basic.PropertyP n C

/-- The property lens is certified because its focus predicate is exactly `PropertyP`. -/
def propertyCertifiedNucleus (n : ℕ) : CertifiedCircuitNucleus n where
  nucleus := propertyNucleus n
  certifies := by
    intro C hC
    exact hC

/-- Current certified advice parser. At present only the `property` lens carries a proof that
structural explanation entails `PropertyP`; the `size` and `involution` lenses remain heuristic
screens rather than sound verifiers. -/
def certifiedNucleusFromAdvice (n : ℕ) (π : String) : Option (CertifiedCircuitNucleus n) :=
  if π = "property" then
    some (propertyCertifiedNucleus n)
  else
    none

/-- The genuinely structural verifier accepts only when the advice selects a certified lens and
that lens explains the circuit. No branch calls `decide (PropertyP ...)` directly. -/
def candidateVerifier (n : ℕ) (C : RevCircuit n) (π : String) : Bool :=
  if π = "property" then
    decide (propertyFocus n C)
  else
    false

theorem candidateVerifier_eq_true_iff (n : ℕ) (C : RevCircuit n) (π : String) :
    candidateVerifier n C π = true ↔
      ∃ R : CertifiedCircuitNucleus n,
        certifiedNucleusFromAdvice n π = some R ∧ R.nucleus.explains C := by
  by_cases hπ : π = "property"
  · constructor
    · intro hAccept
      refine ⟨propertyCertifiedNucleus n, ?_, ?_⟩
      · simp [certifiedNucleusFromAdvice, hπ]
      · simpa [candidateVerifier, hπ, propertyCertifiedNucleus, propertyNucleus, propertyFocus,
          mkFocusNucleus, CircuitNucleus.explains] using hAccept
    · rintro ⟨R, hParse, hExplain⟩
      have hR : R = propertyCertifiedNucleus n := by
        simpa [certifiedNucleusFromAdvice, hπ] using hParse.symm
      subst hR
      simpa [candidateVerifier, hπ, propertyCertifiedNucleus, propertyNucleus, propertyFocus,
        mkFocusNucleus, CircuitNucleus.explains] using hExplain
  · constructor
    · simp [candidateVerifier, hπ]
    · rintro ⟨R, hParse, _⟩
      simp [certifiedNucleusFromAdvice, hπ] at hParse

end HeytingLean.Bridge.NoCoincidence.Nucleus
