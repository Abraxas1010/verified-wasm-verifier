import HeytingLean.Blockchain.Rollup.Escape

/-
# Consensus.RollupEscapeHatch

Semantic target for `Consensus.Spec.PropertyId.escapeHatch`, built from
the minimal rollup escape-hatch model in `Blockchain.Rollup.Escape`.

At this abstraction level, the escape-hatch property captures two
guarantees about the L1 escrow component:

* **Monotonicity:** processing any list of PEG v0 steps via `runExits`
  never decreases the L1 escrow balance.
* **Strict increase for permitted positive steps:** applying a single
  PEG v0 step that is permitted and spends a positive amount strictly
  increases the L1 escrow balance.

More refined models (e.g. with explicit rollup/execution semantics or
sequencer assumptions) can later strengthen this statement; for now, it
provides a concrete, fully proved semantic target for the
`escapeHatch` consensus property.
-/

namespace HeytingLean
namespace Blockchain
namespace Consensus
namespace RollupEscapeHatch

open HeytingLean.Blockchain
open HeytingLean.Blockchain.Rollup
open HeytingLean.Blockchain.Rollup.Escape
open HeytingLean.Blockchain.Contracts
open HeytingLean.Blockchain.Contracts.PEGv0

/-- Semantic statement for `Spec.PropertyId.escapeHatch`.

It bundles the two core properties of the minimal escape‑hatch model:

* `monotone` states that L1 escrow is non‑decreasing along any sequence
  of PEG v0 steps.
* `strictIfPermitted` states that a single permitted step spending a
  positive amount strictly increases the L1 escrow balance.
-/
structure Statement : Prop where
  monotone :
    ∀ (steps : List Contracts.Step) (st : EscapeState),
      st.l1Escrow ≤ (runExits st steps).l1Escrow
  strictIfPermitted :
    ∀ (st : EscapeState) (step : Contracts.Step),
      PEGv0.permitted step = true →
      step.spentNow > 0 →
      st.l1Escrow < (applyPegExit st step).l1Escrow

/-- `Statement` holds for the current minimal escape‑hatch model via the
underlying monotonicity and strict‑increase lemmas from
`Blockchain.Rollup.Escape`. -/
theorem statement_holds : Statement := by
  refine
    { monotone := ?mono
      strictIfPermitted := ?strict }
  · intro steps st
    -- Directly reuse the run‑level monotonicity lemma.
    simpa using Escape.l1Escrow_monotone steps st
  · intro st step hPerm hPos
    -- Directly reuse the single‑step strict‑increase lemma.
    exact Escape.applyPegExit_l1Escrow_strict st step hPerm hPos

end RollupEscapeHatch
end Consensus
end Blockchain
end HeytingLean

