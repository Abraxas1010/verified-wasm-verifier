import HeytingLean.Bridge.NoCoincidence.Nucleus.AdviceAsNucleus
import Mathlib.Tactic

namespace HeytingLean.Bridge.NoCoincidence.Nucleus

/-- Named structural lenses used in the advice decomposition story. -/
structure NucleusLens (n : ℕ) where
  nucleus : CircuitNucleus n
  lensName : String

/-- Two lenses are independent when their closure operators commute. -/
def NucleusLens.independent (l₁ l₂ : NucleusLens n) : Prop :=
  ∀ P : CircuitProp n,
    l₁.nucleus.toNucleus.R (l₂.nucleus.toNucleus.R P) =
    l₂.nucleus.toNucleus.R (l₁.nucleus.toNucleus.R P)

def sizeLens (n : ℕ) : NucleusLens n :=
  { nucleus := sizeNucleus n, lensName := "size" }

def involutionLens (n : ℕ) : NucleusLens n :=
  { nucleus := involutionNucleus n, lensName := "involution" }

def propertyLens (n : ℕ) : NucleusLens n :=
  { nucleus := propertyNucleus n, lensName := "property" }

/-- The three focus-generated nuclei commute algebraically because each closure operator is of the
form `P ↦ P ∨ focus`. This is a commutativity fact about disjunction, not a claim that the three
lenses are structurally independent in a stronger semantic sense. -/
theorem canonical_lenses_commute_algebraically (n : ℕ) :
    (sizeLens n).independent (involutionLens n) ∧
    (sizeLens n).independent (propertyLens n) ∧
    (involutionLens n).independent (propertyLens n) := by
  constructor
  · intro P
    funext C
    apply propext
    unfold sizeLens involutionLens sizeNucleus involutionNucleus
    simp [CircuitNucleus.toNucleus, closureByFocus]
    tauto
  constructor
  · intro P
    funext C
    apply propext
    unfold sizeLens propertyLens sizeNucleus propertyNucleus propertyFocus
    simp [CircuitNucleus.toNucleus, closureByFocus]
    tauto
  · intro P
    funext C
    apply propext
    unfold involutionLens propertyLens involutionNucleus propertyNucleus propertyFocus
    simp [CircuitNucleus.toNucleus, closureByFocus]
    tauto

/-- Documentation theorem recording the exhaustive parser cases for `nucleusFromAdvice`: every
recognized advice string names one of the three canonical lenses. -/
theorem recognized_advice_uses_one_of_three_lenses (n : ℕ) (π : String) :
    ∃ l₁ l₂ l₃ : NucleusLens n,
      match nucleusFromAdvice n π with
      | none => True
      | some R =>
          R.adviceTag = l₁.lensName ∨ R.adviceTag = l₂.lensName ∨ R.adviceTag = l₃.lensName := by
  refine ⟨sizeLens n, involutionLens n, propertyLens n, ?_⟩
  unfold nucleusFromAdvice
  by_cases hSize : π = "size"
  · simp [hSize, sizeLens, involutionLens, propertyLens, sizeNucleus, involutionNucleus,
      propertyNucleus, mkFocusNucleus]
  · by_cases hInv : π = "involution"
    · simp [hInv, sizeLens, involutionLens, propertyLens, sizeNucleus, involutionNucleus,
        propertyNucleus, mkFocusNucleus]
    · by_cases hProp : π = "property"
      · simp [hProp, sizeLens, involutionLens, propertyLens, sizeNucleus,
          involutionNucleus, propertyNucleus, mkFocusNucleus]
      · simp [hSize, hInv, hProp]

end HeytingLean.Bridge.NoCoincidence.Nucleus
