import HeytingLean.Crypto.Lattice.Distributions

/-!
# CBD exact counts + convolution (toy computed bounds)

This module provides a **fully computed** (not axiomatized) distributional pipeline for the
Centered Binomial Distribution (CBD), suitable for:
- exact, finite verification on *toy* parameter sizes; and
- serving as a stepping stone toward a scalable (proof-based) failure-bound development.

We intentionally work with **counts** (natural numbers) rather than probability values:
the probability of an event under a uniform bit model is `count / 2^N`, so proving bounds can be
done by cross-multiplying inequalities in `Nat`.

Important: this does **not** claim to model ML-KEM's full residual noise (which involves products,
NTT structure, compression noise, etc.). It is the minimal, policy-compliant “computed kernel”
needed to start closing the remaining failure-probability gap.
-/

namespace HeytingLean
namespace Crypto
namespace Lattice
namespace CBDCounts

open HeytingLean.Crypto.Lattice.Dist

/-!
## CBD sample from a `2*eta`-bit word

We follow the standard CBD definition:
`sample = popcount(low eta bits) - popcount(high eta bits)`.
-/

def cbdSample (eta x : Nat) : Int :=
  let a := popcountLow x eta
  let b := popcountLow (x / (2 ^ eta)) eta
  (a : ℤ) - (b : ℤ)

theorem cbdSample_natAbs_le (eta x : Nat) :
    Int.natAbs (cbdSample eta x) ≤ eta := by
  have ha : popcountLow x eta ≤ eta := popcountLow_le x eta
  have hb : popcountLow (x / (2 ^ eta)) eta ≤ eta := popcountLow_le (x / (2 ^ eta)) eta
  simpa [cbdSample] using Int.natAbs_coe_sub_coe_le_of_le ha hb

/-!
## Centered count vectors

For a bound `B`, a centered count vector stores counts for values in `[-B, ..., B]` in an array of
length `2*B+1`, indexed by shifting by `B`.
-/

structure CenteredCounts where
  B : Nat
  data : Array Nat
  deriving Repr

def mkZero (B : Nat) : CenteredCounts :=
  { B := B
  , data := Array.replicate (2 * B + 1) 0
  }

def mkDelta0 : CenteredCounts :=
  { B := 0, data := #[1] }

def idxToInt (B i : Nat) : Int :=
  (i : Int) - (B : Int)

def intToIdx (B : Nat) (z : Int) : Nat :=
  Int.toNat (z + (B : Int))

def totalCount (c : CenteredCounts) : Nat :=
  c.data.foldl (init := 0) (fun acc x => acc + x)

def tailCount (c : CenteredCounts) (t : Nat) : Nat := Id.run do
  let mut acc : Nat := 0
  for i in [0:c.data.size] do
    let z : Int := idxToInt c.B i
    if z.natAbs > t then
      acc := acc + c.data[i]!
  return acc

/-!
## CBD exact counts

`cbdCounts eta` enumerates all `2^(2*eta)` bit-words and counts the resulting CBD samples.
-/

def cbdCounts (eta : Nat) : CenteredCounts := Id.run do
  let c0 := mkZero eta
  let mut data := c0.data
  let n := 2 ^ (2 * eta)
  for x in [0:n] do
    let z := cbdSample eta x
    let idx := intToIdx eta z
    if idx < data.size then
      data := data.set! idx (data[idx]! + 1)
  return { B := eta, data := data }

/-!
## Convolution of centered counts

If `c₁` counts values in `[-B₁,B₁]` and `c₂` counts values in `[-B₂,B₂]`, then `convolve c₁ c₂`
counts the distribution of the sum, which lives in `[-(B₁+B₂), (B₁+B₂)]`.
-/

def convolve (c1 c2 : CenteredCounts) : CenteredCounts := Id.run do
  let Bout := c1.B + c2.B
  let out0 := mkZero Bout
  let mut out := out0.data
  for i in [0:c1.data.size] do
    for j in [0:c2.data.size] do
      let zi := idxToInt c1.B i
      let zj := idxToInt c2.B j
      let z := zi + zj
      let idx := intToIdx Bout z
      if idx < out.size then
        out := out.set! idx (out[idx]! + c1.data[i]! * c2.data[j]!)
  return { B := Bout, data := out }

def convolvePow (base : CenteredCounts) : Nat → CenteredCounts
  | 0 => mkDelta0
  | 1 => base
  | n + 2 => convolve (convolvePow base (n + 1)) base

def convolvePowFast (base : CenteredCounts) (n : Nat) : CenteredCounts :=
  let rec go : Nat → CenteredCounts → CenteredCounts → CenteredCounts
    | 0, acc, _cur => acc
    | exp + 1, acc, cur =>
        let exp' := exp + 1
        let acc' := if exp' % 2 = 1 then convolve acc cur else acc
        go (exp' / 2) acc' (convolve cur cur)
  go n mkDelta0 base

end CBDCounts
end Lattice
end Crypto
end HeytingLean
