import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import HeytingLean.Crypto.QKD.E91.DI.CHSH.CHSHInequality
import HeytingLean.Crypto.QKD.E91.DI.Tsirelson.Achievability

/-!
# CHSH/Tsirelson security bridge (interface-first)

This module records the core *logical* implications used by device-independent security:

1. LHV (classical) strategies satisfy `|S| ≤ 2`.
2. Vector “quantum” strategies satisfy `|S| ≤ 2√2` and can achieve `2√2`.
3. Therefore any correlator with `|S| > 2` cannot come from any LHV model.

Turning CHSH violation into *quantitative secrecy bounds* requires additional
information-theoretic machinery (entropy bounds, monogamy of entanglement). We keep
that as future work.
-/

namespace HeytingLean
namespace Crypto
namespace QKD
namespace E91
namespace DI
namespace Security

open HeytingLean.Crypto.QKD.E91.DI.CHSH

/-- CHSH violation implies non-LHV: no local hidden variable model can induce the correlator. -/
theorem chsh_violation_no_lhv (C : Correlator)
    (h_violation : |chshQuantity C| > 2) :
    ¬ ∃ (M : LocalHiddenVariableModel), M.toCorrelator = C := by
  intro h
  rcases h with ⟨M, hMC⟩
  have h_bound : |chshQuantity (M.toCorrelator)| ≤ 2 :=
    LocalHiddenVariableModel.chsh_inequality (M := M)
  have h_violationM : 2 < |chshQuantity (M.toCorrelator)| := by
    simpa [hMC] using h_violation
  exact (not_lt_of_ge h_bound) h_violationM

end Security
end DI
end E91
end QKD
end Crypto
end HeytingLean
