import HeytingLean.Crypto.KEM.FujisakiOkamoto
import HeytingLean.Crypto.KEM.MLKEM203Params
import HeytingLean.Crypto.KEM.MLKEMFailureBounds
import Mathlib.Data.Rat.Defs

namespace HeytingLean
namespace Crypto
namespace KEM
namespace FIPS203
namespace ProofLine

open HeytingLean.Crypto.KEM.FujisakiOkamoto

/-!
# ML-KEM proof-line skeleton

This file records the composition shape of the current ML-KEM security story:

1. a base K-PKE correctness / IND-CPA component,
2. an FO transform step,
3. an implementation-refinement / proof-provenance witness,
4. an explicit published decryption-failure bound from FIPS 203.

It is an honest repository-native bridge to the external EasyCrypt proof corpus,
not a claim that the full Episode V argument has already been rechecked in Lean.
-/

/-- External references used by the imported ML-KEM proof line. -/
structure ImportedProofBundle where
  basePKE : ExternalReference
  foTransform : ExternalReference
  implementationRefinement : ExternalReference
  deriving Repr

/-- A named security component used in the assembled statement. -/
structure SecurityComponent where
  name : String
  bound : BoundDescriptor
  deriving Repr

/-- Repo-native ML-KEM statement bundle corresponding to the external proof line. -/
structure StatementBundle (p : MLKEM203Params) where
  parameterSet : String
  mlweParams : Lattice.MLWEParams
  proofSources : ImportedProofBundle
  baseIndCpa : SecurityComponent
  decryptionFailure : SecurityComponent
  foReduction : ImportedReduction
  implementationBoundary : String
  claimSummary : String
  deriving Repr

def fips203Reference : ExternalReference :=
  { label := "FIPS 203 ML-KEM"
    location := "https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.203.pdf"
    theoremId := "Published parameter and failure-bound table"
    model := "standard specification" }

def episodeVBundle : ImportedProofBundle :=
  { basePKE := kyberEpisodeV2024
    foTransform := hofheinzHovelmannsKiltz2017
    implementationRefinement := kyberEpisodeV2024 }

noncomputable def reportedFailureComponent (p : MLKEM203Params) : SecurityComponent :=
  { name := "decryption_failure_bound"
    bound :=
      { name := s!"reported_failure_bound_{p.name}"
        numericUpperBound := some (reportedFailureBoundQ p)
        provenance := fips203Reference } }

noncomputable def importedEpisodeV (p : MLKEM203Params) : StatementBundle p :=
  { parameterSet := p.name
    mlweParams := toMLWEParams p
    proofSources := episodeVBundle
    baseIndCpa :=
      { name := "kpke_ind_cpa"
        bound :=
          { name := "kpke_ind_cpa_advantage"
            numericUpperBound := none
            provenance := kyberEpisodeV2024 } }
    decryptionFailure := reportedFailureComponent p
    foReduction := importedEpisodeVReduction
    implementationBoundary := "PQClean / Jasmin runtime parity remains the executable boundary"
    claimSummary :=
      "ML-KEM IND-CCA is tracked as the composition of the external K-PKE proof, FO transform, and implementation-refinement witnesses." }

theorem importedEpisodeV_parameterSet (p : MLKEM203Params) :
    (importedEpisodeV p).parameterSet = p.name := rfl

theorem importedEpisodeV_failureBound_present (p : MLKEM203Params) :
    (importedEpisodeV p).decryptionFailure.bound.numericUpperBound = some (reportedFailureBoundQ p) := rfl

end ProofLine
end FIPS203
end KEM
end Crypto
end HeytingLean
