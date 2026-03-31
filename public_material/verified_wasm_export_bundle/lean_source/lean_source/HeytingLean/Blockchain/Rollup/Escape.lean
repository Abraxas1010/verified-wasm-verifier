import HeytingLean.Blockchain.Rollup.Model
import HeytingLean.Blockchain.Contracts.PEGv0

/-
# Rollup.Escape

Minimal escape-hatch model connecting the PEG v0 guard to a simple
rollup/L1 state split. This does **not** attempt to model full rollup
semantics; it provides a small, fully proved instance of an escape-hatch
property that can serve as a target for more refined models.
-/

namespace HeytingLean
namespace Blockchain
namespace Rollup
namespace Escape

open HeytingLean.Blockchain
open HeytingLean.Blockchain.Contracts
open HeytingLean.Blockchain.Contracts.PEGv0

/-- Combined rollup/L1 state for a PEG-style escape hatch: we pair an
    existing rollup `State` (from `Rollup.Model`) with a non-negative L1
    escrow balance. -/
structure EscapeState where
  l2       : Rollup.State
  l1Escrow : Nat
  deriving Repr, Inhabited, DecidableEq

/-- Apply a single PEG v0 escape step. If `permitted` holds for the
    step, we move `spentNow` units into the L1 escrow; otherwise the
    state is left unchanged. The rollup component `l2` is kept abstract
    here and is not modified. -/
def applyPegExit (st : EscapeState) (step : Contracts.Step) : EscapeState :=
  if PEGv0.permitted step = true then
    { st with l1Escrow := st.l1Escrow + step.spentNow }
  else
    st

/-- Run a list of PEG v0 steps through the escape-hatch state by
    iterating `applyPegExit`. -/
def runExits (st : EscapeState) (steps : List Contracts.Step) : EscapeState :=
  steps.foldl applyPegExit st

/-- Single-step monotonicity: a PEG v0 escape step never decreases the
    L1 escrow balance. -/
theorem applyPegExit_l1Escrow_monotone
    (st : EscapeState) (step : Contracts.Step) :
    st.l1Escrow ≤ (applyPegExit st step).l1Escrow := by
  classical
  by_cases h : PEGv0.permitted step = true
  · -- In the permitted case, escrow increases by `step.spentNow ≥ 0`.
    simp [applyPegExit, h]
  · -- Otherwise the state is unchanged.
    simp [applyPegExit, h]

/-- Multi-step monotonicity: processing any list of PEG v0 steps never
    decreases the L1 escrow balance. -/
theorem l1Escrow_monotone (steps : List Contracts.Step) :
    ∀ st : EscapeState,
      st.l1Escrow ≤ (runExits st steps).l1Escrow := by
  classical
  induction steps with
  | nil =>
      intro st
      simp [runExits]
  | cons step steps ih =>
      intro st
      -- First step is monotone by `applyPegExit_l1Escrow_monotone`.
      have hHead :
          st.l1Escrow ≤ (applyPegExit st step).l1Escrow :=
        applyPegExit_l1Escrow_monotone st step
      -- Remaining steps are monotone by the induction hypothesis.
      have hTail :
          (applyPegExit st step).l1Escrow ≤
            (runExits (applyPegExit st step) steps).l1Escrow :=
        ih (applyPegExit st step)
      have h := Nat.le_trans hHead hTail
      simp [runExits, List.foldl]
      exact h

/-- Single-step strict increase: if a PEG v0 step is permitted and
    spends a positive amount, then the L1 escrow balance increases
    strictly after applying that step. -/
theorem applyPegExit_l1Escrow_strict
    (st : EscapeState) (step : Contracts.Step)
    (hPerm : PEGv0.permitted step = true)
    (hPos : step.spentNow > 0) :
    st.l1Escrow < (applyPegExit st step).l1Escrow := by
  classical
  -- Evaluate the permitted branch explicitly.
  simp [applyPegExit, hPerm]
  -- We need `st.l1Escrow < st.l1Escrow + step.spentNow` from `hPos`.
  have h' :
      st.l1Escrow + 0 < st.l1Escrow + step.spentNow := by
    -- Add `st.l1Escrow` to both sides of the inequality `0 < step.spentNow`.
    simpa using Nat.add_lt_add_left hPos st.l1Escrow
  simpa [Nat.add_zero] using h'

end Escape
end Rollup
end Blockchain
end HeytingLean
