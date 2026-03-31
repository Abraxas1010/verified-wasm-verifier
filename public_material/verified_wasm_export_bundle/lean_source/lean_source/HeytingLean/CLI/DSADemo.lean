import Lean
import HeytingLean.Crypto.DSA.MLDSA
import HeytingLean.Util.SHA

/-!
dsa_sign_demo: small, self-contained PQC demo (Lean-only)

Exercises the Lean-side ML-DSA "spec skeleton" toy sign/open flow.
-/

open HeytingLean.Util

private def normHex (s : String) : String :=
  let isHex (c : Char) : Bool :=
    ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')
  String.mk <| (s.toList.filter isHex).map Char.toLower

private def hexToBA (s : String) : ByteArray := Id.run do
  let ss := normHex s
  let val (c : Char) : Nat :=
    if c.isDigit then c.toNat - '0'.toNat
    else if c ≥ 'a' && c ≤ 'f' then 10 + (c.toNat - 'a'.toNat)
    else if c ≥ 'A' && c ≤ 'F' then 10 + (c.toNat - 'A'.toNat)
    else 0
  let rec loop (xs : List Char) (acc : Array UInt8) : Array UInt8 :=
    match xs with
    | c1 :: c2 :: rest => loop rest (acc.push (UInt8.ofNat (val c1 * 16 + val c2)))
    | _ => acc
  ByteArray.mk (loop ss.toList #[])

private def seedFromEnv : IO ByteArray := do
  match (← IO.getEnv "RNG_SEED") with
  | none => pure ("heytinglean-demo-seed" : String).toUTF8
  | some s =>
      let s := normHex s
      if s.isEmpty then
        pure ("heytinglean-demo-seed" : String).toUTF8
      else
        pure (hexToBA s)

private def flipFirstByte (ba : ByteArray) : ByteArray :=
  if ba.size == 0 then
    ba
  else
    let b0 := ba.data[0]!
    let b0' := b0 + 1
    ByteArray.mk (ba.data.set! 0 b0')

def main (_args : List String) : IO UInt32 := do
  let seed ← seedFromEnv
  let rng0 := HeytingLean.Crypto.RNG.SeededRNG.init seed
  let p := HeytingLean.Crypto.DSA.mldsa44
  let (pk, sk, rng1) := HeytingLean.Crypto.DSA.Toy.keygen p rng0
  let msg := ("hello-ml-dsa" : String).toUTF8
  let (sm, _rng2) := HeytingLean.Crypto.DSA.Toy.signAttached p sk msg rng1

  match HeytingLean.Crypto.DSA.Toy.openSignedMessage p pk sm with
  | .error e =>
      IO.eprintln s!"dsa_sign_demo: open failed: {repr e}"
      return 1
  | .ok m2 =>
      if m2 != msg then
        IO.eprintln "dsa_sign_demo: message mismatch after open"
        return 1

  let smBad : HeytingLean.Crypto.DSA.SignedMessage := { bytes := flipFirstByte sm.bytes }
  match HeytingLean.Crypto.DSA.Toy.openSignedMessage p pk smBad with
  | .ok _ =>
      IO.eprintln "dsa_sign_demo: open unexpectedly accepted a tampered signed message"
      return 1
  | .error _ =>
      pure ()

  let seedHex := SHA256.toHex seed
  IO.println s!"dsa_sign_demo ok (seed={seedHex})"
  return 0
