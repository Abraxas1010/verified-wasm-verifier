/-
Teorth / symmetric_project.

Upstream `symmetric_project` is pinned to a very old Lean/Mathlib, and its sources currently
do not compile under our pinned toolchain (Lean v4.24.0 / Mathlib v4.24.0) due to:
- renamed/removed Mathlib modules (e.g. `Mathlib.Data.Polynomial.Basic`, `Mathlib.Algebra.BigOperators.Basic`)
- Lean tactic API drift in custom tactic code.

For now this wrapper is intentionally empty so it is buildable, while the dependency stays
available for later backport work.
-/

-- (intentionally empty)
