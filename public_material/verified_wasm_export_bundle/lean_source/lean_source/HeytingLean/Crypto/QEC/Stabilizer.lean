import HeytingLean.Quantum.StabilizerNucleus

/-!
# Quantum error correction (QEC): stabilizer-code interface

This module re-exports the already-landed *set-algebraic* stabilizer-code formalism from
`HeytingLean.Quantum.StabilizerNucleus` into the crypto namespace used by the unified roadmap.

Phase 8 uses this as the “formal spine” for concrete small codes (e.g. the three-qubit repetition
code), without committing to density matrices or channels.
-/

namespace HeytingLean
namespace Crypto
namespace QEC

abbrev StabilizerCode := HeytingLean.Quantum.StabilizerCode

namespace StabilizerCode

abbrev codeSpace {α : Type _} (C : StabilizerCode α) : Set α :=
  HeytingLean.Quantum.StabilizerCode.codeSpace C

end StabilizerCode

abbrev stabilizerNucleus {α : Type _} (C : StabilizerCode α) :=
  HeytingLean.Quantum.StabilizerNucleus.stabilizerNucleus (α := α) C

end QEC
end Crypto
end HeytingLean
