import HeytingLean.Crypto.QKD.BB84.MultiRound

/-!
# BB84 multi-round sanity checks

Compile-time checks for the multi-round reduction layer.
-/

namespace HeytingLean.Tests.Crypto.BB84MultiRoundSanity

open HeytingLean.Crypto.QKD.BB84

#check attackSeqPow
#check attackParPow
#check bb84_attackSeqPow_impossible
#check bb84_attackParPow_impossible

end HeytingLean.Tests.Crypto.BB84MultiRoundSanity

