/-
Teorth / Analysis I (Lean formalization).

Why this wrapper exists:
- The upstream `Analysis.lean` umbrella imports a very large module set.
- At our pinned toolchain (Lean v4.24.0 / Mathlib v4.24.0), a small number of upstream
  modules currently do not build cleanly (tactic breakage / goal mismatch).
- For HeytingLean, we want (1) a buildable import set, and (2) the largest practical chunk
  of `Analysis.*` declarations indexed into `lean_index/` for search.

This file intentionally imports only the subset that builds in our environment.
If upstream fixes land, we can regenerate and expand this list.
-/

-- Core early chapters (safe subset)
import Analysis.Section_2_1
import Analysis.Section_3_1
import Analysis.Section_3_2
import Analysis.Section_3_3
import Analysis.Section_3_epilogue
import Analysis.Section_4_1
import Analysis.Section_4_2
import Analysis.Section_4_3

-- Later selected sections that currently build
import Analysis.Section_7_1
import Analysis.Section_7_2
import Analysis.Section_8_1
import Analysis.Section_9_2
import Analysis.Section_9_10
import Analysis.Section_10_1
import Analysis.Section_10_3
import Analysis.Section_11_1
import Analysis.Section_11_2

-- Appendices (safe subset)
import Analysis.Appendix_A_1
import Analysis.Appendix_A_2
import Analysis.Appendix_A_3
import Analysis.Appendix_A_5
import Analysis.Appendix_A_7
import Analysis.Appendix_B_1
import Analysis.Appendix_B_2

-- Misc / extra (safe subset)
import Analysis.Misc.FiniteChoice
import Analysis.Misc.Probability
import Analysis.Misc.erdos_379
import Analysis.Misc.erdos_613
import Analysis.Misc.erdos_707

-- Measure theory track (notation only for now)
import Analysis.MeasureTheory.Notation

