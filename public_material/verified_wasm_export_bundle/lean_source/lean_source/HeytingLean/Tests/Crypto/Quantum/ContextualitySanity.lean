import HeytingLean.Quantum.Contextuality

/-!
# Contextuality sanity tests

Compile-time checks for the Phase 9 contextuality re-export layer and crypto link theorem.
-/

namespace HeytingLean.Tests.Crypto.Quantum.ContextualitySanity

open HeytingLean.Quantum.Contextuality

-- Core witness packaging
#check Witness

-- Triangle witness (re-export)
#check Triangle.witness
#check Triangle.noGlobal

-- Mermin–Peres parity obstruction (re-export)
#check MerminPeres.no_assignment

-- Crypto link theorem (triangle instance)
#check CryptoLink.triangle_no_constructor_globalSectionTask

end HeytingLean.Tests.Crypto.Quantum.ContextualitySanity

