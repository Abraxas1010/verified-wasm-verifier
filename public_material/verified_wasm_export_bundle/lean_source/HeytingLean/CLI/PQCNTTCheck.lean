import HeytingLean.Crypto.Lattice.NTTIterative
import Lean.Data.Json

/-!
# PQC NTT Checker (Gap 1 helper)

This executable validates the executable `NTTIterative` implementation against a runtime
**round-trip** property:

1. `inttIterative (nttIterative a) = a`

Notes:
- ML-KEM’s NTT domain is not “scalar pointwise multiplication”; it requires a quadratic-factor
  structure (`X^2 - μ`) and a corresponding `basemul` on coefficient pairs.
- `--experimental-mul` enables a runtime check that uses `NTTIterative.basemul` and compares
  against a naive `O(n^2)` negacyclic reference multiplication.

This is not a formal proof, but it is a compatibility check to help pin down the exact
ordering/twiddle conventions before attempting a full refinement proof.
-/

namespace HeytingLean
namespace CLI

open HeytingLean.Crypto.Lattice.NTTIterative

namespace PQCNTTCheck

abbrev q : Nat := HeytingLean.Crypto.Lattice.NTTIterative.q
abbrev F : Type := HeytingLean.Crypto.Lattice.NTTIterative.F

private def hasFlag (flag : String) (args : List String) : Bool :=
  args.any (fun x => x == flag)

private def getFlagValue? (flag : String) (args : List String) : Option String :=
  let rec go : List String → Option String
    | [] => none
    | x :: y :: xs => if x == flag then some y else go (y :: xs)
    | _ :: [] => none
  go args

private def natOr (s : Option String) (dflt : Nat) : Nat :=
  s.bind String.toNat? |>.getD dflt

private def ntt256 (a : Array F) : Array F :=
  if h : a.size = 256 then nttIterative a h else a

private def intt256 (a : Array F) : Array F :=
  if h : a.size = 256 then inttIterative a h else a

private def mkSample (seed : Nat) : Array F := Id.run do
  let mut a : Array F := Array.replicate 256 (0 : F)
  for i in [0:256] do
    let x := ((1103515245 * (seed + i) + 12345) % q)
    a := a.set! i (x : F)
  return a

private def dftArray (a : Array F) : Array F := Id.run do
  let mut out : Array F := Array.replicate 256 (0 : F)
  for j in [0:256] do
    let mut acc : F := 0
    for i in [0:256] do
      acc := acc + a[i]! * ((HeytingLean.Crypto.Lattice.NTT.zeta : F) ^ (i * j))
    out := out.set! j acc
  return out

private def bitRev8 (n : Nat) : Nat :=
  -- local 8-bit bit-reversal for index experiments
  let rec go (bits m acc : Nat) : Nat :=
    match bits with
    | 0 => acc
    | Nat.succ bits' => go bits' (m / 2) (acc * 2 + (m % 2))
  go 8 n 0

private def dftArray_bitRevOut (a : Array F) : Array F :=
  Array.ofFn (fun j : Fin 256 => (dftArray a)[bitRev8 j.val % 256]!)

private def quadSpecArray (a : Array F) : Array F := Id.run do
  let mut out : Array F := Array.replicate 256 (0 : F)
  for r in [0:128] do
    let rev : Nat := bitRevNat 7 r % 128
    let μ : F := (HeytingLean.Crypto.Lattice.NTT.zeta : F) ^ (2 * rev + 1)
    let mut acc0 : F := 0
    let mut acc1 : F := 0
    for k in [0:128] do
      acc0 := acc0 + a[2 * k]! * (μ ^ k)
      acc1 := acc1 + a[2 * k + 1]! * (μ ^ k)
    out := out.set! (2 * r) acc0
    out := out.set! (2 * r + 1) acc1
  return out

private def pointwiseMul (a b : Array F) : Array F :=
  Array.ofFn (fun i : Fin 256 => a[i.1]! * b[i.1]!)

private def mulNegacyclic (a b : Array F) : Array F := Id.run do
  let mut out : Array F := Array.replicate 256 (0 : F)
  for i in [0:256] do
    for j in [0:256] do
      let prod := a[i]! * b[j]!
      let t := i + j
      if t < 256 then
        out := out.set! t (out[t]! + prod)
      else
        let idx := t - 256
        out := out.set! idx (out[idx]! - prod)
  return out

private def checkRoundtripOnce (seed : Nat) : Bool :=
  let a := mkSample seed
  let a' := intt256 (ntt256 a)
  a' == a

private def checkMulOnce (seedA seedB : Nat) : Bool :=
  let a := mkSample seedA
  let b := mkSample seedB
  let na := ntt256 a
  let nb := ntt256 b
  let prodNTT :=
    if ha : na.size = 256 then
      if hb : nb.size = 256 then
        basemul na nb ha hb
      else
        pointwiseMul na nb
    else
      pointwiseMul na nb
  let prodCoeff := intt256 prodNTT
  let ref := mulNegacyclic a b
  prodCoeff == ref

private def countTrue (xs : List Bool) : Nat :=
  xs.foldl (init := 0) (fun acc b => if b then acc + 1 else acc)

private def reportJson (mulEnabled : Bool) (roundtripOk mulOk : List Bool) : Lean.Json :=
  Lean.Json.mkObj
    [ ("mulEnabled", Lean.Json.bool mulEnabled)
    , ("roundtripSamples", Lean.Json.num (Lean.JsonNumber.fromNat roundtripOk.length))
    , ("roundtripPassed", Lean.Json.num (Lean.JsonNumber.fromNat (countTrue roundtripOk)))
    , ("mulSamples", Lean.Json.num (Lean.JsonNumber.fromNat mulOk.length))
    , ("mulPassed", Lean.Json.num (Lean.JsonNumber.fromNat (countTrue mulOk)))
    , ("roundtripAll", Lean.Json.bool (roundtripOk.all id))
    , ("mulAll", Lean.Json.bool (mulEnabled && mulOk.all id))
    ]

def main (argv : List String) : IO Unit := do
  if argv.isEmpty || hasFlag "--help" argv then
    IO.println "usage: pqc_ntt_check [--samples N] [--seed S] [--no-roundtrip] [--experimental-mul]"
    IO.println "                     [--compare-dft]"
    IO.println "  default: N=3, S=1, checks roundtrip only"
    return
  let samples := natOr (getFlagValue? "--samples" argv) 3
  let seed0 := natOr (getFlagValue? "--seed" argv) 1
  let doRoundtrip := !hasFlag "--no-roundtrip" argv
  let doMul := hasFlag "--experimental-mul" argv
  let doCompareDft := hasFlag "--compare-dft" argv
  let roundtripOk :=
    if doRoundtrip then
      (List.range samples).map (fun t => checkRoundtripOnce (seed0 + t))
    else
      []
  let mulOk :=
    if doMul then
      (List.range samples).map (fun t => checkMulOnce (seed0 + t) (seed0 + 1000 + t))
    else
      []
  let json0 := reportJson doMul roundtripOk mulOk
  let json :=
    if doCompareDft then
      let a := mkSample seed0
      let na := ntt256 a
      let d := dftArray a
      let dbr := dftArray_bitRevOut a
      let qspec := quadSpecArray a
      json0.mergeObj (Lean.Json.mkObj
        [ ("dftMatches", Lean.Json.bool (na == d))
        , ("dftBitRevOutMatches", Lean.Json.bool (na == dbr))
        , ("quadSpecMatches", Lean.Json.bool (na == qspec))
        ])
    else
      json0
  IO.println (toString json)

end PQCNTTCheck

end CLI
end HeytingLean
