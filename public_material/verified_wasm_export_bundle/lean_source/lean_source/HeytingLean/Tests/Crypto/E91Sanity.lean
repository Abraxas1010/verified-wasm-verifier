import HeytingLean.Crypto.QKD.E91

/-!
# E91 Sanity Tests

Verifies that the E91 API is correctly wired.
-/

namespace HeytingLean.Tests.Crypto.E91Sanity

open HeytingLean.Crypto.QKD.E91

-- CT toy instantiation
#check E91State
#check attrKey
#check attrTest
#check copyAll
#check e91TaskCT
#check e91Superinfo
#check e91_secure
#check intercept_impossible

-- Core protocol interface
#check Transcript
#check Transcript.score
#check Transcript.passesCHSH

-- LHV-exclusion security layer
#check InLHVSet
#check chsh_abs_le_two_of_inLHV
#check no_lhv_of_chsh_violation
#check e91_secure_di

-- Explicit Tsirelson-violating transcript
#check Examples.tsirelsonTranscript
#check Examples.tsirelsonTranscript_score
#check Examples.tsirelsonTranscript_violates_lhv
#check Examples.tsirelsonTranscript_not_lhv

-- Device-independent certificate interface
#check E91DICertificate
#check e91_di_secure

end HeytingLean.Tests.Crypto.E91Sanity
