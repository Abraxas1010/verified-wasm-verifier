import HeytingLean.Crypto.RNG.Seeded
import HeytingLean.Util.SHA

namespace HeytingLean
namespace Crypto
namespace KEM

/-!
# ML-KEM (FIPS 203) — Parameter Bundle + Spec Skeleton

This file defines:
- a minimal parameter bundle for wiring KAT runners; and
- an executable **spec skeleton** (toy KEM) with explicit decapsulation error semantics.

It does **not** implement real ML‑KEM.
-/

structure MLKEMParams where
  /-- Human name (e.g. `ML-KEM-512`). -/
  name : String
  /-- Kyber-style module rank (2/3/4 for 512/768/1024). -/
  k : Nat
  /-- NIST KAT filename bits suffix used by `PQCkemKAT_<bits>.rsp` (1632/2400/3168). -/
  katBits : Nat
  deriving Repr, Inhabited

def mlkem512 : MLKEMParams := { name := "ML-KEM-512", k := 2, katBits := 1632 }
def mlkem768 : MLKEMParams := { name := "ML-KEM-768", k := 3, katBits := 2400 }
def mlkem1024 : MLKEMParams := { name := "ML-KEM-1024", k := 4, katBits := 3168 }

def all : Array MLKEMParams :=
  #[mlkem512, mlkem768, mlkem1024]

def katFileName (p : MLKEMParams) : String :=
  s!"PQCkemKAT_{p.katBits}.rsp"

def pqcleanKatFileName (p : MLKEMParams) : String :=
  s!"PQCkemKAT_pqclean_{p.katBits}.rsp"

/-!
## Spec Skeleton (Toy)

We provide a tiny, deterministic toy KEM to exercise the end-to-end wiring in Lean:

- keys/ciphertexts are byte arrays;
- randomness is sourced from a seedable RNG (test-only);
- decapsulation can fail on malformed ciphertexts.

This is **not** a cryptographic construction.
-/

structure PublicKey where
  bytes : ByteArray

structure SecretKey where
  bytes : ByteArray

structure Ciphertext where
  bytes : ByteArray

structure SharedSecret where
  bytes : ByteArray

inductive DecapError where
  | invalidCiphertext
  deriving Repr, DecidableEq

namespace Toy

open HeytingLean.Util
open HeytingLean.Crypto.RNG

private def mkBA (xs : Array UInt8) : ByteArray := ByteArray.mk xs

private def baAppend (a b : ByteArray) : ByteArray :=
  mkBA (a.data ++ b.data)

private def baConcat (xs : List ByteArray) : ByteArray :=
  xs.foldl baAppend (mkBA #[])

private def tagPk : ByteArray := ("mlkem-toy:pk:" : String).toUTF8
private def tagCt : ByteArray := ("mlkem-toy:ct:" : String).toUTF8
private def tagSs : ByteArray := ("mlkem-toy:ss:" : String).toUTF8

private def sha (ba : ByteArray) : ByteArray :=
  SHA256.sha256Bytes ba

def keygen (_p : MLKEMParams) (rng : SeededRNG) : PublicKey × SecretKey × SeededRNG :=
  let (skBytes, rng') := SeededRNG.nextBytes rng 32
  let pkBytes := sha (baConcat [tagPk, skBytes])
  ({ bytes := pkBytes }, { bytes := skBytes }, rng')

def encap (_p : MLKEMParams) (pk : PublicKey) (rng : SeededRNG) :
    Ciphertext × SharedSecret × SeededRNG :=
  let (r, rng') := SeededRNG.nextBytes rng 32
  let h := sha (baConcat [tagCt, pk.bytes, r])
  let ctBytes := baAppend r h
  let ssBytes := sha (baConcat [tagSs, pk.bytes, ctBytes])
  ({ bytes := ctBytes }, { bytes := ssBytes }, rng')

def decap (_p : MLKEMParams) (sk : SecretKey) (ct : Ciphertext) : Except DecapError SharedSecret := do
  if ct.bytes.size != 64 then
    throw .invalidCiphertext
  let pkBytes := sha (baConcat [tagPk, sk.bytes])
  let r := mkBA (ct.bytes.data.extract 0 32)
  let h := mkBA (ct.bytes.data.extract 32 64)
  let h' := sha (baConcat [tagCt, pkBytes, r])
  if h' != h then
    throw .invalidCiphertext
  let ssBytes := sha (baConcat [tagSs, pkBytes, ct.bytes])
  return { bytes := ssBytes }

end Toy

end KEM
end Crypto
end HeytingLean
