import HeytingLean.Crypto.Quantum.Bell.CHSH.Correlations

/-!
# E91 protocol (interface-first)

We keep the E91 development lightweight and interface-first:
- an E91 run is represented by an observed CHSH correlator (two binary settings per party),
- the CHSH score is the derived quantity used for Bell tests.

Later work can refine this into a distributional protocol model (basis choice sampling, sifting,
parameter estimation, error correction, privacy amplification).
-/

namespace HeytingLean
namespace Crypto
namespace QKD
namespace E91

open HeytingLean.Crypto.Quantum.Bell.CHSH

abbrev Setting := HeytingLean.Crypto.Quantum.Bell.CHSH.Setting
abbrev Correlator := HeytingLean.Crypto.Quantum.Bell.CHSH.Correlator

/-- An E91 “transcript” consisting of an observed correlator box. -/
structure Transcript where
  correlator : Correlator

namespace Transcript

/-- The CHSH score associated to the transcript. -/
def score (T : Transcript) : ℝ :=
  chshQuantity T.correlator

/-- CHSH test predicate: the observed score exceeds a threshold. -/
def passesCHSH (T : Transcript) (threshold : ℝ) : Prop :=
  threshold < |T.score|

end Transcript

end E91
end QKD
end Crypto
end HeytingLean

