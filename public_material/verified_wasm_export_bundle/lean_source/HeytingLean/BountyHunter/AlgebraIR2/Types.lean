import Std

/-!
# HeytingLean.BountyHunter.AlgebraIR2.Types

`AlgebraIR` (v1) is effect-first: it intentionally discards most value-level semantics.

`AlgebraIR2` is a minimal, *executable* follow-on IR whose first purpose is to
support emitting a **compilable replay/decompiler artifact** (currently as Yul)
that can be checked against the existing Foundry oracle (return bytes + selected
storage snapshot).

This is not a full decompiler: it is a witness-level replay IR that starts with
the smallest “chokepoint” semantics we need (slot computation + CEI ordering).
-/

namespace HeytingLean.BountyHunter.AlgebraIR2

inductive CEIOrder where
  | writeThenCall
  | callThenWrite
  deriving Repr, DecidableEq, Inhabited

structure ReplaySpec where
  /-- Whether the selected slot is restored before the boundary call. -/
  order : CEIOrder
  /-- Fallback behavior: treat *any* calldata as a call to this replay entry. -/
  entryName : String := "bh_entry"
  /-- Selected slot: either literal, or computed from `slotExpr` via `SlotRef`. -/
  slot : Nat
  slotExpr? : Option String := none
  /-- Value to store (v0: keep deterministic; `0` matches our CEI fixtures). -/
  writeValue : Nat := 0
  deriving Repr, DecidableEq, Inhabited

end HeytingLean.BountyHunter.AlgebraIR2

