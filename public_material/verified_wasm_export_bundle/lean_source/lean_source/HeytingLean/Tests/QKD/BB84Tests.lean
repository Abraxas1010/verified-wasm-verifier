import HeytingLean.Crypto.QKD.BB84

/-!
# QKD tests: BB84 (Phase 12)

Compile-time checks for the BB84 API.
-/

namespace HeytingLean.Tests.QKD.BB84Tests

open HeytingLean.Crypto.QKD.BB84

#check bb84_secure
#check bb84_uc_secure
#check BB84ExtractedKeySecurity
#check BB84ExtractedKeySecurity.statDistance_le_extractionError
#check BB84FiniteKeySecurity.coversExtractionWitness
#check BB84FiniteKeySecurity.statDistance_le_epsilonSec
#check BB84FiniteKeySecurity.correctness_plus_extraction_le_total

end HeytingLean.Tests.QKD.BB84Tests
