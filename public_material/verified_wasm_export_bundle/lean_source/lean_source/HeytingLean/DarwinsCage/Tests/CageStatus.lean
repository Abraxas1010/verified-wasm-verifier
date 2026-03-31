import HeytingLean.DarwinsCage.CageStatus

/-!
# Cage status helper lemmas (Phase 5 tests)

These lemmas ensure `determineCageStatus` reduces to the expected constructor
when fed inequalities that match Francisco's taxonomy. They act as lightweight
tests and reusable facts for future proofs.
-/

namespace HeytingLean
namespace DarwinsCage
namespace Tests

open DarwinsCage

variable (t : CageThresholds)

/-- If performance misses the threshold we always obtain `failed`. -/
theorem classify_failed {maxCorr rSquared : ℝ}
    (h_fail : rSquared < t.performance) :
    determineCageStatus ⟨maxCorr, rSquared⟩ t = CageStatus.failed := by
  simp [determineCageStatus, h_fail]

/-- Lock condition: performance above threshold and correlation ≥ locked. -/
theorem classify_locked {maxCorr rSquared : ℝ}
    (h_perf : t.performance ≤ rSquared)
    (h_corr : t.locked ≤ maxCorr) :
    determineCageStatus ⟨maxCorr, rSquared⟩ t = CageStatus.locked := by
  have h_perf' : ¬rSquared < t.performance := not_lt.mpr h_perf
  simp [determineCageStatus, h_perf', h_corr]

/-- Transition condition: performance ok, correlation between thresholds. -/
theorem classify_transition {maxCorr rSquared : ℝ}
    (h_perf : t.performance ≤ rSquared)
    (h_lo : ¬t.locked ≤ maxCorr)
    (h_hi : t.transition ≤ maxCorr) :
    determineCageStatus ⟨maxCorr, rSquared⟩ t = CageStatus.transition := by
  have h_perf' : ¬rSquared < t.performance := not_lt.mpr h_perf
  simp [determineCageStatus, h_perf', h_lo, h_hi]

/-- Broken condition: performance ok, correlation below the transition band. -/
theorem classify_broken {maxCorr rSquared : ℝ}
    (h_perf : t.performance ≤ rSquared)
    (h_lo : ¬t.locked ≤ maxCorr)
    (h_low : ¬t.transition ≤ maxCorr) :
    determineCageStatus ⟨maxCorr, rSquared⟩ t = CageStatus.broken := by
  have h_perf' : ¬rSquared < t.performance := not_lt.mpr h_perf
  simp [determineCageStatus, h_perf', h_lo, h_low]

end Tests
end DarwinsCage
end HeytingLean
