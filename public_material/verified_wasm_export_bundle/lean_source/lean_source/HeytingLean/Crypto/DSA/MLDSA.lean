import HeytingLean.Crypto.RNG.Seeded
import HeytingLean.Util.SHA

namespace HeytingLean
namespace Crypto
namespace DSA

/-!
# ML-DSA (FIPS 204) — Parameter Bundle + Spec Skeleton

This file defines:
- a minimal parameter bundle for wiring KAT runners; and
- an executable **spec skeleton** (toy sign/open) with explicit error semantics.

It does **not** implement real ML‑DSA.
-/

structure MLDSAParams where
  /-- Human name (e.g. `ML-DSA-44`). -/
  name : String
  /-- Corresponding Dilithium security level identifier (2/3/5). -/
  dilithiumLevel : Nat
  deriving Repr, Inhabited

def mldsa44 : MLDSAParams := { name := "ML-DSA-44", dilithiumLevel := 2 }
def mldsa65 : MLDSAParams := { name := "ML-DSA-65", dilithiumLevel := 3 }
def mldsa87 : MLDSAParams := { name := "ML-DSA-87", dilithiumLevel := 5 }

def all : Array MLDSAParams :=
  #[mldsa44, mldsa65, mldsa87]

def katFileName (p : MLDSAParams) : String :=
  s!"PQCsignKAT_Dilithium{p.dilithiumLevel}.rsp"

def signCliName (p : MLDSAParams) : String :=
  s!"dsa_sign_cli_{p.dilithiumLevel}"

def openCliName (p : MLDSAParams) : String :=
  s!"dsa_open_cli_{p.dilithiumLevel}"

/-!
## Spec Skeleton (Toy)

We provide a tiny, deterministic toy "sign attached / open" flow to exercise the Lean-side
message plumbing.

- keygen/sign are seeded by a test-only RNG façade;
- `open` returns `Except` instead of crashing on malformed inputs.

This is **not** a cryptographic construction.
-/

structure PublicKey where
  bytes : ByteArray

structure SecretKey where
  bytes : ByteArray

structure SignedMessage where
  bytes : ByteArray

inductive OpenError where
  | invalidSignedMessage
  | invalidSignature
  deriving Repr, DecidableEq

namespace Toy

open HeytingLean.Util
open HeytingLean.Crypto.RNG

private def mkBA (xs : Array UInt8) : ByteArray := ByteArray.mk xs

private def baAppend (a b : ByteArray) : ByteArray :=
  mkBA (a.data ++ b.data)

private def baConcat (xs : List ByteArray) : ByteArray :=
  xs.foldl baAppend (mkBA #[])

private def tagPk : ByteArray := ("mldsa-toy:pk:" : String).toUTF8
private def tagSig : ByteArray := ("mldsa-toy:sig:" : String).toUTF8

private def sha (ba : ByteArray) : ByteArray :=
  SHA256.sha256Bytes ba

private def sigLen : Nat := 64

def keygen (_p : MLDSAParams) (rng : SeededRNG) : PublicKey × SecretKey × SeededRNG :=
  let (skBytes, rng') := SeededRNG.nextBytes rng 32
  let pkBytes := sha (baConcat [tagPk, skBytes])
  ({ bytes := pkBytes }, { bytes := skBytes }, rng')

def signAttached (_p : MLDSAParams) (sk : SecretKey) (msg : ByteArray) (rng : SeededRNG) :
    SignedMessage × SeededRNG :=
  let pkBytes := sha (baConcat [tagPk, sk.bytes])
  let (nonce, rng') := SeededRNG.nextBytes rng 32
  let h := sha (baConcat [tagSig, pkBytes, msg, nonce])
  let sig := baAppend nonce h
  ({ bytes := baAppend sig msg }, rng')

private def verifyDetached (pk : PublicKey) (msg sig : ByteArray) : Bool :=
  if sig.size != sigLen then
    false
  else
    let nonce := mkBA (sig.data.extract 0 32)
    let h := mkBA (sig.data.extract 32 64)
    let h' := sha (baConcat [tagSig, pk.bytes, msg, nonce])
    h' == h

def openSignedMessage (_p : MLDSAParams) (pk : PublicKey) (sm : SignedMessage) : Except OpenError ByteArray := do
  if sm.bytes.size < sigLen then
    throw .invalidSignedMessage
  let sig := mkBA (sm.bytes.data.extract 0 sigLen)
  let msg := mkBA (sm.bytes.data.extract sigLen sm.bytes.size)
  if verifyDetached pk msg sig then
    return msg
  else
    throw .invalidSignature

end Toy

end DSA
end Crypto
end HeytingLean
