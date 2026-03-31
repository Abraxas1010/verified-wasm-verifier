import Lean

/-!
Native (library‑free) Poseidon‑like commitment implemented in pure Lean, compiled to C.

Design:
- Domain separation: tag ++ ":" ++ payload (UTF‑8 bytes)
- Map bytes to a big integer modulo the BN254 field prime p
- Emit 32‑byte big‑endian hex (0x‑prefixed), padded

Note: This is a deterministic, library‑free stand‑in for Poseidon that avoids
external binaries. It does not claim cryptographic strength. Replace the
mapping with a true Poseidon permutation later while maintaining the same
interface.
-/

namespace HeytingLean
namespace Crypto
namespace PoseidonNative

open System

-- BN254 scalar field prime (Fr modulus)
def bn254_p : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

private def toBytesUtf8 (s : String) : List UInt8 :=
  s.toUTF8.data.toList

private def modFromBytes (bytes : List UInt8) (p : Nat := bn254_p) : Nat :=
  bytes.foldl (fun acc b => (acc * 256 + (b.toNat)) % p) 0

private def hexOfNatBE32 (n : Nat) : String :=
  let hexNibble (d : Nat) : Char :=
    if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d)
  let rec toHexDigits (m : Nat) (acc : List Char) : List Char :=
    if m = 0 then acc
    else
      let digit := (m % 16)
      let ch := hexNibble digit
      toHexDigits (m / 16) (ch :: acc)
  let hex := String.mk (toHexDigits n [])
  -- pad to 64 hex chars (32 bytes)
  let padded :=
    if hex.length ≥ 64 then hex.drop (hex.length - 64) else
      String.join (List.replicate (64 - hex.length) "0") ++ hex
  s!"0x{padded}"

def commitHex (tag payload : String) : String :=
  let bytes := toBytesUtf8 (tag ++ ":" ++ payload)
  let v := modFromBytes bytes
  hexOfNatBE32 v

def commitCanonical (payload : String) : String :=
  commitHex "CANON" payload

end PoseidonNative
end Crypto
end HeytingLean
