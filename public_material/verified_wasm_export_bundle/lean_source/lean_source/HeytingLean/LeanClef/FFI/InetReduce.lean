import HeytingLean.LeanClef.FFI.NetSerialize

/-!
# ICC Precompiled Reduction Kernel — Lean FFI Bridge

In-process FFI to `libinet_reduce.so` — the precompiled C reducer for ICC terms.
Zero subprocess overhead: no process spawn, no file I/O, no gcc compilation.

The C library implements the same 4 ICC reduction rules as `ICC.Reduction.step?`:
  1. app(lam(body), arg)    → subst0(arg, body)
  2. app(bridge(body), arg) → bridge(app(body, ann(var(0), shift(arg,1))))
  3. ann(val, lam(body))    → lam(ann(app(shift(val,1), var(0)), subst0(bridge(var(0)), body)))
  4. ann(val, bridge(body)) → subst0(val, body)

Usage:
  inetInit                    -- call once at startup
  reduceViaInet term fuel     -- reduce a term
  inetShutdown                -- call once at shutdown
-/

namespace LeanClef.FFI

open HeytingLean.LoF.ICC

/-- Initialize the precompiled reducer (allocates arena). Call once. -/
@[extern "lean_inet_init"]
opaque inetInit : IO Unit

/-- Shutdown the reducer (frees arena). Call once. -/
@[extern "lean_inet_shutdown"]
opaque inetShutdown : IO Unit

/-- Raw FFI: reduce serialized bytes with fuel.
    Returns ByteArray where last 8 bytes encode interaction count (LE u64),
    and preceding bytes are the serialized result term. -/
@[extern "lean_inet_reduce_raw"]
opaque inetReduceRaw (netData : @& ByteArray) (fuel : UInt32) : IO ByteArray

/-- High-level API: reduce an ICC.Term via the precompiled kernel.
    Returns (normalized_term, interaction_count). -/
def reduceViaInet (t : Term) (fuel : Nat := 1000000) : IO (Option Term × Nat) := do
  let bytes := serializeTerm t
  let resultBytes ← inetReduceRaw bytes fuel.toUInt32
  -- Last 8 bytes are interaction count (LE u64)
  if resultBytes.size < 8 then
    return (none, 0)
  let termEnd := resultBytes.size - 8
  let interactions :=
    (resultBytes.get! termEnd).toNat
    ||| ((resultBytes.get! (termEnd + 1)).toNat <<< 8)
    ||| ((resultBytes.get! (termEnd + 2)).toNat <<< 16)
    ||| ((resultBytes.get! (termEnd + 3)).toNat <<< 24)
    ||| ((resultBytes.get! (termEnd + 4)).toNat <<< 32)
    ||| ((resultBytes.get! (termEnd + 5)).toNat <<< 40)
    ||| ((resultBytes.get! (termEnd + 6)).toNat <<< 48)
    ||| ((resultBytes.get! (termEnd + 7)).toNat <<< 56)
  let termBytes := resultBytes.extract 0 termEnd
  match deserializeTerm termBytes with
  | some (result, _) => return (some result, interactions)
  | none => return (none, interactions)

end LeanClef.FFI
