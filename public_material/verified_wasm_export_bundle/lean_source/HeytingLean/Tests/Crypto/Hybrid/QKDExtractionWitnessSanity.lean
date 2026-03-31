import HeytingLean.Crypto.Hybrid.QKDExtractionWitness

/-!
# Test: hybrid-facing QKD extraction witness sanity

Compile-time checks for the compatibility import surface around the now-native hybrid witness.
-/

namespace HeytingLean.Tests.Crypto.Hybrid.QKDExtractionWitnessSanity

open HeytingLean.Crypto.Hybrid

#check QKDExtractionWitness
#check QKDExtractionWitness.statDistance_le_epsilonSec
#check QKDExtractionWitness.correctness_plus_extraction_le_total

end HeytingLean.Tests.Crypto.Hybrid.QKDExtractionWitnessSanity
