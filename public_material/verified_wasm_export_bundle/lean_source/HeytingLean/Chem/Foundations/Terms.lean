import Mathlib.Data.String.Basic

/-!
# Chemistry terms (provenance-first)

This module is deliberately lightweight: it stores chemistry-facing terms and their provenance
(definitions, identifiers, URLs) without committing to a deep physical semantics yet.

The intent is to let later modules (Bonding, QED, Bridges) refer to stable term objects.
-/

namespace HeytingLean
namespace Chem
namespace Foundations

/-- Minimal provenance record (human-auditable, machine-friendly). -/
structure Provenance where
  source : String
  url    : String := ""
  note   : String := ""

/-- A named term and its definition text, together with provenance metadata. -/
structure Term where
  name       : String
  definition : String
  provenance : Provenance

/-- IUPAC Gold Book: "chemical bond" term record (content kept short; see URL for the canonical definition). -/
def chemicalBondTerm : Term :=
  { name := "chemical bond"
    definition := "A term for the interaction linking atoms in molecules/aggregates; see provenance URL for the canonical definition."
    provenance :=
      { source := "IUPAC Gold Book"
        url := "https://goldbook.iupac.org/terms/view/CT07009/plain"
        note := "Used as the canonical reference for the term 'chemical bond' in this project." } }

end Foundations
end Chem
end HeytingLean

