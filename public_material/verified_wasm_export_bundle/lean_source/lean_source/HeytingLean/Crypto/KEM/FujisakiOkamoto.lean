import Mathlib.Data.Rat.Defs

namespace HeytingLean
namespace Crypto
namespace KEM
namespace FujisakiOkamoto

/-!
# Fujisaki-Okamoto Transform: theorem-shape metadata

This file does not claim to formalize the full FO security proof. It records the
reduction shape, budgets, and external provenance needed to wire an honest ML-KEM
proof line into the rest of the repository.
-/

/-- Stable external citation metadata for imported proof-line components. -/
structure ExternalReference where
  label : String
  location : String
  theoremId : String
  model : String
  deriving Repr, DecidableEq

/-- Query budget tracked by a transform-level security statement. -/
structure AdversaryBudget where
  randomOracleQueries : Nat
  decapsulationQueries : Nat
  deriving Repr, DecidableEq, Inhabited

/-- A named upper bound appearing in an imported proof line. -/
structure BoundDescriptor where
  name : String
  numericUpperBound : Option ℚ
  provenance : ExternalReference
  deriving Repr

/-- The FO transform contributes a reduction-shape statement plus query budget. -/
structure ImportedReduction where
  budget : AdversaryBudget
  reductionLoss : BoundDescriptor
  transformReference : ExternalReference
  deriving Repr

/-- Canonical FO modular-analysis citation used throughout the ML-KEM proof line. -/
def hofheinzHovelmannsKiltz2017 : ExternalReference :=
  { label := "Modular Analysis of the Fujisaki-Okamoto Transformation"
    location := "https://eprint.iacr.org/2017/604"
    theoremId := "TCC 2017 modular FO analysis"
    model := "ROM / transform-level reduction" }

/-- Canonical Kyber / ML-KEM EasyCrypt proof-line citation. -/
def kyberEpisodeV2024 : ExternalReference :=
  { label := "Formally verifying Kyber Episode V"
    location := "https://eprint.iacr.org/2024/843"
    theoremId := "Machine-checked IND-CCA security and correctness of ML-KEM"
    model := "EasyCrypt + Jasmin" }

/-- A repo-local imported reduction shell for the external ML-KEM proof line. -/
def importedEpisodeVReduction : ImportedReduction :=
  { budget := { randomOracleQueries := 0, decapsulationQueries := 0 }
    reductionLoss :=
      { name := "fo_transform_loss"
        numericUpperBound := none
        provenance := hofheinzHovelmannsKiltz2017 }
    transformReference := kyberEpisodeV2024 }

end FujisakiOkamoto
end KEM
end Crypto
end HeytingLean
