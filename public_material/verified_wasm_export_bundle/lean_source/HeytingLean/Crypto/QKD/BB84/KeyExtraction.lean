import HeytingLean.Crypto.Information.PrivacyAmplification
import HeytingLean.Crypto.QKD.BB84.ProbabilisticSecurity

/-!
# BB84 key extraction (interface-first)

This layer now distinguishes two surfaces:

- an operational extraction record containing a normalized raw-key distribution and a concrete
  fixed-seed plan; and
- a theorem-facing extracted-key security witness that reuses the public-seed leftover-hash
  interface honestly.
-/

namespace HeytingLean
namespace Crypto
namespace QKD
namespace BB84

open HeytingLean.Crypto.Information.Hashing
open HeytingLean.Crypto.Information.PrivacyAmplification

variable {D R S : Type*}

/-- A BB84 key extraction record: normalized raw key, and a plan to hash it to a final key. -/
structure BB84KeyExtraction (D R S : Type*) [Fintype D] where
  rawKey : FiniteSource D
  plan : PrivacyAmplificationPlan D R S

/--
A theorem-facing BB84 extracted-key witness. The operational plan remains available, but secrecy is
stated using the public-seed semantics required by the packaged leftover-hash theorem.
-/
structure BB84ExtractedKeySecurity (D R S : Type*)
    [Fintype D] [Fintype R] [Fintype S] [DecidableEq R] [TwoUniversal D R S]
    extends BB84KeyExtraction D R S where
  theoremBundle : LeftoverHashLemma D R S
  entropyLowerBound : ℝ
  entropyLowerBound_valid : entropyLowerBound ≤ theoremBundle.minEntropy rawKey.dist

namespace BB84ExtractedKeySecurity

variable [Fintype D] [Fintype R] [Fintype S] [DecidableEq R] [TwoUniversal D R S]

/-- Forget the BB84-specific wrapper down to the generic public-seed privacy-amplification witness. -/
noncomputable def toPublicSeededExtractionWitness
    (E : BB84ExtractedKeySecurity D R S) :
    PublicSeededExtractionWitness D R S where
  source := E.toBB84KeyExtraction.rawKey
  theoremBundle := E.theoremBundle
  entropyLowerBound := E.entropyLowerBound
  entropyLowerBound_valid := by
    simpa using E.entropyLowerBound_valid

/-- The extracted-key secrecy error induced by the entropy lower bound. -/
noncomputable def extractionError (E : BB84ExtractedKeySecurity D R S) : ℝ :=
  E.toPublicSeededExtractionWitness.extractionError

/-- Actual joint distribution of public seed and extracted BB84 key. -/
noncomputable def actualDist (E : BB84ExtractedKeySecurity D R S) : S × R → ℝ :=
  E.toPublicSeededExtractionWitness.actualDist

/-- Ideal uniform joint distribution for the BB84 extracted key witness. -/
noncomputable def idealDist (E : BB84ExtractedKeySecurity D R S) : S × R → ℝ :=
  E.toPublicSeededExtractionWitness.idealDist

/-- The BB84 extracted-key witness inherits the generic leftover-hash distance theorem. -/
theorem statDistance_le_extractionError (E : BB84ExtractedKeySecurity D R S) :
    Finite.statDistance E.actualDist E.idealDist ≤ E.extractionError := by
  simpa [actualDist, idealDist, extractionError] using
    E.toPublicSeededExtractionWitness.statDistance_le_extractionError

end BB84ExtractedKeySecurity

end BB84
end QKD
end Crypto
end HeytingLean
