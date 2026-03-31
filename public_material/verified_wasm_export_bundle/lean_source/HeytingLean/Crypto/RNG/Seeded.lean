import HeytingLean.Util.SHA

namespace HeytingLean
namespace Crypto
namespace RNG

/-!
# Seeded RNG (Test-Only)

Deterministic byte generator for tests and KAT harnessing.

This is **not** an SP 800-90 DRBG implementation; it is a simple SHA-256-based expander.
-/

open HeytingLean.Util

structure SeededRNG where
  seed : ByteArray
  counter : Nat

def init (seed : ByteArray) : SeededRNG :=
  { seed := seed, counter := 0 }

private def baAppend (a b : ByteArray) : ByteArray :=
  ByteArray.mk (a.data ++ b.data)

private def natToBE8 (n : Nat) : ByteArray := Id.run do
  let mut out : Array UInt8 := #[]
  for i in [0:8] do
    let shift := (7 - i) * 8
    let byteVal : Nat := (n / (2 ^ shift)) % 256
    out := out.push (UInt8.ofNat byteVal)
  return ByteArray.mk out

private def tag : ByteArray :=
  ("heytinglean-seeded-rng" : String).toUTF8

private def block (seed : ByteArray) (counter : Nat) : ByteArray :=
  SHA256.sha256Bytes (baAppend (baAppend tag seed) (natToBE8 counter))

/-- Return `n` bytes and the updated RNG state. -/
def nextBytes (rng : SeededRNG) (n : Nat) : ByteArray × SeededRNG := Id.run do
  let mut out : Array UInt8 := #[]
  let mut ctr := rng.counter
  while out.size < n do
    let b := block rng.seed ctr
    ctr := ctr + 1
    for x in b.data do
      if out.size < n then
        out := out.push x
  return (ByteArray.mk out, { rng with counter := ctr })

namespace SeededRNG

/-- Convenience alias: `SeededRNG.init seed` (preferred call site style). -/
@[inline] def init (seed : ByteArray) : SeededRNG :=
  RNG.init seed

/-- Convenience alias: `SeededRNG.nextBytes rng n` (preferred call site style). -/
@[inline] def nextBytes (rng : SeededRNG) (n : Nat) : ByteArray × SeededRNG :=
  RNG.nextBytes rng n

end SeededRNG

end RNG
end Crypto
end HeytingLean
