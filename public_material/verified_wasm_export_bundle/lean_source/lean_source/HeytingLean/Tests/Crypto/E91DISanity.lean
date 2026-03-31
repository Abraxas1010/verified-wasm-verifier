import HeytingLean.Crypto.QKD.E91.DI.CHSH.CHSHInequality
import HeytingLean.Crypto.QKD.E91.DI.Tsirelson.TsirelsonBound
import HeytingLean.Crypto.QKD.E91.DI.Tsirelson.Achievability
import HeytingLean.Crypto.QKD.E91.DI.Security.CHSHSecurity

/-!
# E91 device-independent sanity checks

Compile-time checks for the CHSH/Tsirelson layer.
-/

namespace HeytingLean.Tests.Crypto.E91DISanity

open HeytingLean.Crypto.QKD.E91.DI.CHSH
open HeytingLean.Crypto.QKD.E91.DI.Tsirelson
open HeytingLean.Crypto.QKD.E91.DI.Security

#check LocalHiddenVariableModel.chsh_inequality
#check QuantumStrategy.tsirelson_bound
#check Examples.tsirelsonAchievingStrategy
#check Examples.achieves_tsirelson
#check chsh_violation_no_lhv

end HeytingLean.Tests.Crypto.E91DISanity

