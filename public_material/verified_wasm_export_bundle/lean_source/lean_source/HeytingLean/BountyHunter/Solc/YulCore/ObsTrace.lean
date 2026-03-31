import HeytingLean.BountyHunter.Solc.YulCore.Types
import HeytingLean.BountyHunter.Solc.YulTextMini.EffectSemantics
import HeytingLean.BountyHunter.EvmTrace.Types
import HeytingLean.BountyHunter.AlgebraIR.Types

/-!
# HeytingLean.BountyHunter.Solc.YulCore.ObsTrace

Observer trace projection for the current “security-first” semantics lane.

Today we only need a CEI-relevant observer trace (writes vs. external boundary),
so we project `AlgebraIR.Effect`s into an `EvmTrace.Trace` that only records the
opcode *kind* (`SLOAD`/`SSTORE`/`CALL`).

This is intentionally minimal and will be refined when we add value-level
semantics (u256, memory, keccak, ABI).
-/

namespace HeytingLean.BountyHunter.Solc.YulCore

open HeytingLean.BountyHunter
open HeytingLean.BountyHunter.AlgebraIR

private def padLeft (c : Char) (n : Nat) (s : String) : String :=
  if s.length ≥ n then s else
    String.mk (List.replicate (n - s.length) c) ++ s

private def slotKeyHex32 (slot : Nat) : String :=
  -- Render a Nat as a 32-byte big-endian word, as a 0x-prefixed 64-hex-digit string.
  let hex := (Nat.toDigits 16 slot).asString
  "0x" ++ padLeft '0' 64 (if hex.isEmpty then "0" else hex)

private def eventOfEffect : Effect → Option EvmTrace.Event
  | .storageRead slot => some { op := "SLOAD", sload := some { key := slotKeyHex32 slot } }
  | .storageReadDyn slotExpr => some { op := "SLOAD", sload := some { key := slotExpr } }
  | .storageWrite slot => some { op := "SSTORE", sstore := some { key := slotKeyHex32 slot } }
  | .storageWriteDyn slotExpr => some { op := "SSTORE", sstore := some { key := slotExpr } }
  | .boundaryCall target => some { op := "CALL", boundary := some { kind := "CALL", to := target } }

def traceOfEffects (effs : Array Effect) : EvmTrace.Trace :=
  let evs := effs.filterMap eventOfEffect
  { events := evs }

def effectsOfStmts (ss : Array Stmt) : Array Effect :=
  -- Phase-1: reuse the existing (deterministic) effect semantics from YulTextMini.
  (HeytingLean.BountyHunter.Solc.YulTextMini.evalStmts
        { env := HeytingLean.BountyHunter.Solc.YulTextMini.envEmpty } ss).2

def traceOfStmts (ss : Array Stmt) : EvmTrace.Trace :=
  traceOfEffects (effectsOfStmts ss)

end HeytingLean.BountyHunter.Solc.YulCore
