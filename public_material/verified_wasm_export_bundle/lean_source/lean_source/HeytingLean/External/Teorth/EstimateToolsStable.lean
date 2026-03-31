/-
Teorth / estimate_tools.

At our pinned toolchain (Lean v4.24.0 / Mathlib v4.24.0), parts of the upstream
`EstimateTools` library do not build due to API drift (e.g. removed order-structure fields).

This wrapper imports only the subset that currently builds, so we still get some
`EstimateTools.*` declarations into `lean_index/`.
-/

import EstimateTools.analysis.Section_2_1
