import HeytingLean.Analysis.RZ.Dyadic
import HeytingLean.Analysis.RZ.Interval
import HeytingLean.Analysis.RZ.ExactReal

namespace HeytingLean
namespace Analysis

/-!
# RZ (exact reals) scaffolding

This module re-exports the current “RZ-style” numeric core:

* dyadic rounding on `ℚ` (`HeytingLean.Analysis.RZ.roundDown` / `roundUp`)
* dyadic-rounded interval arithmetic on `ℚ` (`HeytingLean.Analysis.RZ.Interval`)

We also provide a first “exact real” layer `HeytingLean.Analysis.RZ.ExactReal`, represented as a
monotone chain of nested intervals with a quantitative width bound.
-/

end Analysis
end HeytingLean
