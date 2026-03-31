import Std
import HeytingLean.BountyHunter.AlgebraIR.SlotRef
import HeytingLean.BountyHunter.AlgebraIR2.Types

/-!
# HeytingLean.BountyHunter.AlgebraIR2.DecompileYul

Emit a **compilable Yul object** that replays a minimal CEI-relevant effect
sequence, parameterized by `ReplaySpec`.

This is intentionally conservative:
- we only support `SlotRef` patterns we can deterministically emit into Yul;
- if `slotExpr` is present but not supported, callers should treat this path as
  `OUT_OF_SCOPE` and disable the check.
-/

namespace HeytingLean.BountyHunter.AlgebraIR2

open HeytingLean.BountyHunter.AlgebraIR

private structure EmitState where
  nextId : Nat := 0
  lines : Array String := #[]

private def fresh (st : EmitState) : EmitState × String :=
  let name := s!"__bh_t{st.nextId}"
  ({ st with nextId := st.nextId + 1 }, name)

private def pushLine (st : EmitState) (line : String) : EmitState :=
  { st with lines := st.lines.push line }

private def keyToYulExpr? : SlotKey → Option String
  | .caller => some "caller()"
  | .this => some "address()"
  | .nat n => some (toString n)
  | .ident _ => none
  | .raw _ => none

private def offsetToYulExpr? : SlotOffset → Option String
  | .nat n => some (toString n)
  | .key _ => none

/-- Emit Yul statements that compute `r` into a fresh variable name. -/
private partial def emitSlotRefE (st : EmitState) (r : SlotRef) : Except String (EmitState × String) := do
  match r with
  | .literal n => pure (st, toString n)
  | .raw s => throw s!"unsupported SlotRef.raw for Yul emission: {s}"
  | .packed base _ _ => emitSlotRefE st base
  | .add base off =>
      let (st, b) ← emitSlotRefE st base
      let o ←
        match offsetToYulExpr? off with
        | some s => pure s
        | none => throw "unsupported SlotOffset for Yul emission (expected nat offset)"
      let (st, out) := fresh st
      let st := pushLine st s!"let {out} := add({b}, {o})"
      pure (st, out)
  | .keccak base =>
      let (st, b) ← emitSlotRefE st base
      let st := pushLine st s!"mstore(0x00, {b})"
      let (st, out) := fresh st
      let st := pushLine st s!"let {out} := keccak256(0x00, 0x20)"
      pure (st, out)
  | .mapping base key =>
      let (st, b) ← emitSlotRefE st base
      let k ←
        match keyToYulExpr? key with
        | some s => pure s
        | none => throw "unsupported SlotKey for Yul emission (expected caller/this/nat)"
      let st := pushLine st s!"mstore(0x00, {k})"
      let st := pushLine st s!"mstore(0x20, {b})"
      let (st, out) := fresh st
      let st := pushLine st s!"let {out} := keccak256(0x00, 0x40)"
      pure (st, out)

private def emitSlotRefFromExprE (slotExpr : String) : Except String (Array String × String) := do
  match slotRefParse? slotExpr with
  | none => throw s!"slotExpr did not parse as SlotRef: {slotExpr}"
  | some r =>
      let (st, outVar) ← emitSlotRefE {} r
      pure (st.lines, outVar)

def yulObjectForCEIReplayE (spec : ReplaySpec) : Except String String := do
  let (slotLines, slotVar) ←
    match spec.slotExpr? with
    | none => pure (#[], toString spec.slot)
    | some se => emitSlotRefFromExprE se
  let storeLine := s!"sstore({slotVar}, {spec.writeValue})"
  let callLine := "pop(call(gas(), caller(), 0, 0, 0, 0, 0))"
  let bodyLines :=
    match spec.order with
    | .writeThenCall => slotLines ++ #[storeLine, callLine]
    | .callThenWrite => slotLines ++ #[callLine, storeLine]
  let runtime :=
    String.intercalate "\n"
      ([
        "object \"BountyHunterDecompiled\" {",
        "  code {",
        "    datacopy(0, dataoffset(\"Runtime\"), datasize(\"Runtime\"))",
        "    return(0, datasize(\"Runtime\"))",
        "  }",
        "  object \"Runtime\" {",
        "    code {",
      ] ++
      (bodyLines.toList.map (fun l => s!"      {l}")) ++
      [
        "      return(0, 0)",
        "    }",
        "  }",
        "}"
      ])
  pure runtime

end HeytingLean.BountyHunter.AlgebraIR2
