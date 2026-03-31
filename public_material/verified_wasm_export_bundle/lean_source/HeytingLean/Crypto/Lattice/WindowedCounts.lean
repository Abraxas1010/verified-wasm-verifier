import HeytingLean.Crypto.Lattice.CBDCounts

/-!
# Windowed distributions (counts) with tail upper bounds

To scale exact-count reasoning beyond tiny toy cases, we use a **window + overflow** encoding:

- keep exact counts for values in `[-W, W]`;
- store a single `overflow` bucket for values outside the window.

When convolving two such distributions, we compute an **upper bound** on the resulting overflow:
any contribution involving an unknown (overflow) value is conservatively assigned to overflow.

This gives a practical way to upper-bound tail probabilities like `P(|X| > T)` for large sums by
choosing `W = T` so the tail is exactly “overflow”.
-/

namespace HeytingLean
namespace Crypto
namespace Lattice
namespace WindowedCounts

open HeytingLean.Crypto.Lattice.CBDCounts

structure WC where
  W : Nat
  inside : Array Nat   -- length `2*W+1`, indexed by shift `W`
  overflow : Nat
  deriving Repr

def mkZero (W : Nat) : WC :=
  { W := W, inside := Array.replicate (2 * W + 1) 0, overflow := 0 }

def mkDelta0 (W : Nat) : WC :=
  let inside := (mkZero W).inside.set! W 1
  { W := W, inside := inside, overflow := 0 }

def idxToInt (W i : Nat) : Int :=
  (i : Int) - (W : Int)

def intToIdx (W : Nat) (z : Int) : Nat :=
  Int.toNat (z + (W : Int))

def insideSum (c : WC) : Nat :=
  c.inside.foldl (init := 0) (fun acc x => acc + x)

def total (c : WC) : Nat :=
  insideSum c + c.overflow

def ofCenteredCounts (W : Nat) (c : CenteredCounts) : WC := Id.run do
  let out0 := mkZero W
  let mut inside := out0.inside
  let mut overflow := 0
  for i in [0:c.data.size] do
    let z : Int := CBDCounts.idxToInt c.B i
    if z.natAbs ≤ W then
      let idx := intToIdx W z
      if idx < inside.size then
        inside := inside.set! idx (inside[idx]! + c.data[i]!)
    else
      overflow := overflow + c.data[i]!
  return { W := W, inside := inside, overflow := overflow }

/-- Convolution (upper bound): exact on the window, conservative outside. -/
def convolveUB (a b : WC) : WC := Id.run do
  let W := a.W
  let out0 := mkZero W
  let mut inside := out0.inside
  let mut overflowKnown : Nat := 0
  for i in [0:a.inside.size] do
    for j in [0:b.inside.size] do
      let zi := idxToInt W i
      let zj := idxToInt W j
      let z := zi + zj
      let contrib := a.inside[i]! * b.inside[j]!
      if z.natAbs ≤ W then
        let idx := intToIdx W z
        if idx < inside.size then
          inside := inside.set! idx (inside[idx]! + contrib)
      else
        overflowKnown := overflowKnown + contrib
  let totalA := total a
  let totalB := total b
  let overflowUnknown : Nat := a.overflow * totalB + b.overflow * (totalA - a.overflow)
  return { W := W, inside := inside, overflow := overflowKnown + overflowUnknown }

def powUB (base : WC) (n : Nat) : WC :=
  let rec go : Nat → WC → WC → WC
    | 0, acc, _cur => acc
    | exp + 1, acc, cur =>
        let exp' := exp + 1
        let acc' := if exp' % 2 = 1 then convolveUB acc cur else acc
        go (exp' / 2) acc' (convolveUB cur cur)
  go n (mkDelta0 base.W) base

end WindowedCounts
end Lattice
end Crypto
end HeytingLean
