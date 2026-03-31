import Lean
import HeytingLean.Crypto.KEM.MLKEM
import HeytingLean.Crypto.Lattice.ToyLWE
import HeytingLean.Util.SHA

/-!
kem_keygen_demo: small, self-contained PQC demo (Lean-only)

This executable is meant to exercise the Lean-side "spec skeleton" plumbing without relying
on any external corpora or C binaries.
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

  -- Toy ring/LWE-style KEM roundtrip
  let pLWE : HeytingLean.Crypto.Lattice.ToyLWE.Params := {}
  let okLWE := HeytingLean.Crypto.Lattice.ToyLWE.roundTripOk pLWE seed
  if !okLWE then
    IO.eprintln "kem_keygen_demo: ToyLWE roundtrip failed"
    return 1

  -- Toy ML-KEM skeleton roundtrip + negative test (tampered ciphertext)
  let rng0 := HeytingLean.Crypto.RNG.SeededRNG.init seed
  let (pk, sk, rng1) := HeytingLean.Crypto.KEM.Toy.keygen HeytingLean.Crypto.KEM.mlkem512 rng0
  let (ct, ss1, _rng2) := HeytingLean.Crypto.KEM.Toy.encap HeytingLean.Crypto.KEM.mlkem512 pk rng1
  match HeytingLean.Crypto.KEM.Toy.decap HeytingLean.Crypto.KEM.mlkem512 sk ct with
  | .error _ =>
      IO.eprintln "kem_keygen_demo: MLKEM toy decap failed on valid ciphertext"
      return 1
  | .ok ss2 =>
      if ss1.bytes != ss2.bytes then
        IO.eprintln "kem_keygen_demo: MLKEM toy shared-secret mismatch"
        return 1

  let ctBad : HeytingLean.Crypto.KEM.Ciphertext := { bytes := flipFirstByte ct.bytes }
  match HeytingLean.Crypto.KEM.Toy.decap HeytingLean.Crypto.KEM.mlkem512 sk ctBad with
  | .ok _ =>
      IO.eprintln "kem_keygen_demo: MLKEM toy decap unexpectedly accepted a tampered ciphertext"
      return 1
  | .error _ =>
      pure ()

  -- Keep output minimal; QA harness suppresses stdout in smoke runs.
  let seedHex := SHA256.toHex seed
  IO.println s!"kem_keygen_demo ok (seed={seedHex})"
  return 0

