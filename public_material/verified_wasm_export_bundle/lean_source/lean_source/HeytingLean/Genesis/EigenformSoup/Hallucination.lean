import Mathlib

/-!
# Genesis.EigenformSoup.Hallucination

Pre-eigenform rejection accounting used for LES-Omega "hallucination" telemetry.
-/

namespace HeytingLean.Genesis.EigenformSoup

/-- Candidate accounting ledger for one run/window. -/
structure CandidateLedger where
  candidates : Nat
  promoted : Nat

/-- Rejected pre-eigenforms. -/
def rejectedPreEigenforms (l : CandidateLedger) : Nat :=
  l.candidates - l.promoted

/-- Well-formed accounting requires promoted ≤ candidates. -/
def wellFormedLedger (l : CandidateLedger) : Prop :=
  l.promoted ≤ l.candidates

theorem rejectedPreEigenforms_le_candidates (l : CandidateLedger) :
    rejectedPreEigenforms l ≤ l.candidates := by
  exact Nat.sub_le _ _

theorem rejectedPreEigenforms_eq_zero_of_all_promoted
    (l : CandidateLedger)
    (h : l.candidates ≤ l.promoted) :
    rejectedPreEigenforms l = 0 := by
  exact Nat.sub_eq_zero_of_le h

theorem rejectedPreEigenforms_pos_of_strict_rejection
    (l : CandidateLedger)
    (h : l.promoted < l.candidates) :
    0 < rejectedPreEigenforms l := by
  simpa [rejectedPreEigenforms] using Nat.sub_pos_of_lt h

/-- Rejection rate numerator (safe for certificates without division by zero). -/
def rejectionRateNum (l : CandidateLedger) : Nat :=
  rejectedPreEigenforms l

/-- Rejection rate denominator (safe certificate field). -/
def rejectionRateDen (l : CandidateLedger) : Nat :=
  l.candidates

end HeytingLean.Genesis.EigenformSoup

