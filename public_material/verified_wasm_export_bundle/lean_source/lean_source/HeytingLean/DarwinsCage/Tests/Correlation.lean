import Mathlib.Data.Real.Basic
import HeytingLean.DarwinsCage.Correlation

/-!
# Correlation helper lemmas (Phase 5 tests)

Small facts about the numeric thresholds used by cage classification. These are
intended as reusable lemmas and smoke tests.
-/

namespace HeytingLean
namespace DarwinsCage
namespace Tests

open DarwinsCage

theorem transitionCorrelation_not_highCorrelation
    (bounds : CorrelationBounds) (value : ℝ)
    (h : transitionCorrelation value bounds) :
    ¬highCorrelation value bounds := by
  intro hHigh
  exact (not_lt_of_ge hHigh) h.2

theorem highCorrelation_not_transitionCorrelation
    (bounds : CorrelationBounds) (value : ℝ)
    (hHigh : highCorrelation value bounds) :
    ¬transitionCorrelation value bounds := by
  intro hTrans
  exact (not_lt_of_ge hHigh) hTrans.2

end Tests
end DarwinsCage
end HeytingLean

