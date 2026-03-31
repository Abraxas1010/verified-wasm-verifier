import HeytingLean.Crypto.Information

/-!
# Test: information-theoretic primitives (Phase 3) sanity

Importing the modules and typechecking small witnesses is the test.
-/

namespace HeytingLean.Tests.Crypto.Information.InfoTheorySanity

open HeytingLean.Crypto.Information
open scoped BigOperators

example : Hashing.TwoUniversal Bool Bool Bool :=
  inferInstance

example : PrivacyAmplification.PrivacyAmplificationPlan Bool Bool Bool where
  H := (Hashing.xorHash)
  seed := true

noncomputable example : PrivacyAmplification.FiniteSource Bool where
  dist := PrivacyAmplification.Finite.uniform
  nonneg := by
    intro x
    simp [PrivacyAmplification.Finite.uniform, Fintype.card_bool]
  normalized := by
    simp [PrivacyAmplification.Finite.uniform, Fintype.card_bool]

noncomputable example (L : PrivacyAmplification.LeftoverHashLemma Bool Bool Bool) :
    let W : PrivacyAmplification.PublicSeededExtractionWitness Bool Bool Bool := {
      source := {
        dist := PrivacyAmplification.Finite.uniform
        nonneg := by
          intro _
          simp [PrivacyAmplification.Finite.uniform, Fintype.card_bool]
        normalized := by
          simp [PrivacyAmplification.Finite.uniform, Fintype.card_bool]
      }
      theoremBundle := L
      entropyLowerBound := L.minEntropy PrivacyAmplification.Finite.uniform
      entropyLowerBound_valid := le_rfl
    }
    PrivacyAmplification.Finite.statDistance W.actualDist W.idealDist ≤ W.extractionError := by
  intro W
  exact W.statDistance_le_extractionError

end HeytingLean.Tests.Crypto.Information.InfoTheorySanity
