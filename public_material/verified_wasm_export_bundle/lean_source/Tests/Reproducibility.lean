import Lean
import Lean.Data.Json
import HeytingLean.Crypto.PoseidonNative
import HeytingLean.Util.SHA

open Lean

def toJson (name input poseidon shaLike : String) : Json :=
  Json.mkObj [ ("name", Json.str name), ("input", Json.str input), ("poseidon", Json.str poseidon), ("sha256", Json.str shaLike) ]

def main (_args : List String) : IO UInt32 := do
  IO.println "=== TEST: Reproducibility Vectors ==="
  let vectors := [ ("empty", ""), ("single","a"), ("unicode","🔐 test λ"), ("long", String.mk (List.replicate 1000 'x')) ]
  let arrJsons ← vectors.mapM (fun (name, inp) => do
    let p := HeytingLean.Crypto.PoseidonNative.commitCanonical inp
    let s ← HeytingLean.Util.sha256HexOfStringIO inp
    pure (toJson name inp p s))
  let arr := Json.arr (arrJsons.toArray)
  IO.FS.writeFile "test_vectors.json" (arr.compress)
  IO.println "✓ Wrote test_vectors.json"
  return 0
