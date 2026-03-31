import HeytingLean.Crypto.QEC

/-!
# QEC Sanity Tests

Verifies that the Phase 8 QEC/stabilizer-code layer is correctly wired.
-/

namespace HeytingLean.Tests.Crypto.QECSanity

open HeytingLean.Crypto.QEC

#check StabilizerCode
#check StabilizerCode.codeSpace
#check stabilizerNucleus

open HeytingLean.Crypto.QEC.ThreeQubit

#check code
#check encode
#check decode
#check decode_flipAt_encode

end HeytingLean.Tests.Crypto.QECSanity

