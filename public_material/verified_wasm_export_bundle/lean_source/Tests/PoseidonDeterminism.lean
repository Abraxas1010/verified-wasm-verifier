import Lean
import HeytingLean.Crypto.PoseidonNative

namespace Tests

open HeytingLean.Crypto

def isHexChar (c : Char) : Bool :=
  let n := c.toNat
  (48 ≤ n ∧ n ≤ 57) || (97 ≤ n ∧ n ≤ 102) || (65 ≤ n ∧ n ≤ 70)

def okHex (s : String) : Bool :=
  s.length = 66 && s.startsWith "0x" && (s.drop 2 |>.data.all isHexChar)

def run (_args : List String) : IO UInt32 := do
  IO.println "=== TEST: Native Poseidon Implementation ==="
  let input := "test:data"
  let h1 := PoseidonNative.commitCanonical input
  let h2 := PoseidonNative.commitCanonical input
  if h1 ≠ h2 then IO.eprintln "Determinism failed"; return 1
  let h3 := PoseidonNative.commitCanonical "test:different"
  if h1 = h3 then IO.eprintln "Collision on different inputs"; return 1
  if !(okHex h1) then IO.eprintln s!"Bad hex format: {h1}"; return 1
  -- basic collision check over 1024 values
  let hashes := (List.range 1024).map (fun i => PoseidonNative.commitCanonical s!"test:{i}")
  let uniques := hashes.eraseDups
  if uniques.length ≠ hashes.length then IO.eprintln "Collision found in 1024 values"; return 1
  IO.println "✓ Native Poseidon working correctly"
  return 0

end Tests

def main (args : List String) : IO UInt32 :=
  Tests.run args
