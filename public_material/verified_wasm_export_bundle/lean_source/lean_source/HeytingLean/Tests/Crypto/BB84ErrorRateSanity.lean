import HeytingLean.Crypto.QKD.BB84.ErrorRate

/-!
# BB84 error-rate sanity checks

Compile-time checks ensuring the QBER / threshold layer is wired and stable.
-/

namespace HeytingLean.Tests.Crypto.BB84ErrorRateSanity

open HeytingLean.Crypto.QKD.BB84
open HeytingLean.Crypto.QKD.BB84.ErrorRate

#check BitComparison
#check KeyComparison
#check KeyComparison.errorCount
#check KeyComparison.qberReal
#check KeyComparison.qber_bounds

#check InterceptionRate
#check expectedQBER
#check expectedQBER_eq_rate_div_4
#check fullInterception
#check full_interception_qber

#check securityThreshold
#check full_interception_detected
#check interception_detectable
#check secure_implies_limited_interception

#check hoeffdingBound
#check sample300

end HeytingLean.Tests.Crypto.BB84ErrorRateSanity

