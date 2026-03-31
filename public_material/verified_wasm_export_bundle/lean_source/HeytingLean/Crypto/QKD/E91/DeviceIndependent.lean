import HeytingLean.Crypto.Information.Entropy.ConditionalMinEntropy
import HeytingLean.Crypto.QKD.E91.Security

/-!
# E91 device-independent security (interface-first)

Full DIQKD security proofs require quantitative bounds (e.g. on conditional min-entropy) derived
from Bell inequality violation, plus finite-size analysis and privacy amplification.

This file packages the “Bell violation ⇒ min-entropy” step as *data* (a certificate) rather than
as a global assumption, mirroring the interface-first style used elsewhere (UC, leftover hash lemma).
-/

namespace HeytingLean
namespace Crypto
namespace QKD
namespace E91

open HeytingLean.Crypto.Information.Entropy

/-- A device-independent E91 security certificate, parameterized by a min-entropy interface. -/
structure E91DICertificate (X E : Type*) [MinEntropySpace X] where
  transcript : Transcript
  keyDist : MinEntropySpace.Dist (α := X)
  advState : E
  condHmin : ConditionalMinEntropy X E
  /-- A certified (quantitative) lower bound on conditional min-entropy. -/
  lowerBound : ℝ
  lowerBound_pos : 2 < |transcript.score| → 0 < lowerBound
  certified :
    2 < |transcript.score| → lowerBound ≤ condHmin.condHmin keyDist advState

/-- If a DI certificate is supplied and the CHSH test is violated, we obtain a positive entropy
lower bound (and therefore a DI-style secrecy witness). -/
theorem e91_di_secure {X E : Type*} [MinEntropySpace X]
    (cert : E91DICertificate X E) (hvio : 2 < |cert.transcript.score|) :
    0 < cert.lowerBound ∧ cert.lowerBound ≤ cert.condHmin.condHmin cert.keyDist cert.advState := by
  exact ⟨cert.lowerBound_pos hvio, cert.certified hvio⟩

end E91
end QKD
end Crypto
end HeytingLean
