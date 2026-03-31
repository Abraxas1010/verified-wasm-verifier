import HeytingLean.Crypto.Information.PrivacyAmplification.LeftoverHashLemma

/-!
# Privacy amplification (interface-first)

This file provides a minimal "wiring layer" around the packaged Leftover Hash Lemma.
It does not attempt to implement a full QKD privacy amplification pipeline.
-/

namespace HeytingLean
namespace Crypto
namespace Information
namespace PrivacyAmplification

open scoped BigOperators
open HeytingLean.Crypto.Information.Hashing

/-- An operational privacy amplification plan with an explicit seed choice. -/
structure PrivacyAmplificationPlan (D R S : Type*) where
  H : HashFamily D R S
  seed : S

/--
A normalized finite source distribution. This is the theorem-facing input object for privacy
amplification; unlike a raw `D → ℝ`, it carries the pmf obligations explicitly.
-/
structure FiniteSource (D : Type*) [Fintype D] where
  dist : D → ℝ
  nonneg : ∀ x, 0 ≤ dist x
  normalized : ∑ x : D, dist x = 1

/--
A theorem-facing privacy amplification witness using the public uniform seed semantics that appear
in the packaged Leftover Hash Lemma.
-/
structure PublicSeededExtractionWitness (D R S : Type*)
    [Fintype D] [Fintype R] [Fintype S] [DecidableEq R] [TwoUniversal D R S] where
  source : FiniteSource D
  theoremBundle : LeftoverHashLemma D R S
  entropyLowerBound : ℝ
  entropyLowerBound_valid : entropyLowerBound ≤ theoremBundle.minEntropy source.dist

namespace PublicSeededExtractionWitness

variable {D R S : Type*}
variable [Fintype D] [Fintype R] [Fintype S] [DecidableEq R] [TwoUniversal D R S]

/-- Output length in bits for the extracted range. -/
noncomputable def outputBits (_W : PublicSeededExtractionWitness D R S) : ℝ :=
  Real.log (Fintype.card R) / Real.log 2

/-- The leftover-hash extraction error bound determined by the entropy lower bound. -/
noncomputable def extractionError (W : PublicSeededExtractionWitness D R S) : ℝ :=
  Real.rpow 2 (-(W.entropyLowerBound - W.outputBits) / 2)

/-- Actual joint distribution of public seed and extracted output. -/
noncomputable def actualDist (W : PublicSeededExtractionWitness D R S) : S × R → ℝ :=
  Finite.jointDist (R := R)
    (H := (TwoUniversal.toHashFamily (D := D) (R := R) (S := S))) W.source.dist

/-- Ideal distribution: independent uniform seed and uniform output. -/
noncomputable def idealDist (_W : PublicSeededExtractionWitness D R S) : S × R → ℝ :=
  Finite.productDist (Finite.seedDist (S := S)) (Finite.uniform (α := R))

/-- The packaged leftover-hash theorem applies directly to the witness. -/
theorem statDistance_le_extractionError (W : PublicSeededExtractionWitness D R S) :
    Finite.statDistance W.actualDist W.idealDist ≤ W.extractionError := by
  simpa [actualDist, idealDist, extractionError, outputBits] using
    W.theoremBundle.lhl W.source.dist W.source.nonneg W.source.normalized
      W.entropyLowerBound W.entropyLowerBound_valid

end PublicSeededExtractionWitness

end PrivacyAmplification
end Information
end Crypto
end HeytingLean
