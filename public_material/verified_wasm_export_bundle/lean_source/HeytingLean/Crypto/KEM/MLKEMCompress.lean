import HeytingLean.Crypto.KEM.MLKEM203Params
import HeytingLean.Crypto.Lattice.RingReductions
import Mathlib.Data.ZMod.ValMinAbs

/-!
# ML-KEM compression/decompression (spec-level, coefficient-wise)

This file formalizes the **shape** of the FIPS 203 compression functions used in ML-KEM:

- `compress` maps `ZMod q` coefficients into `d`-bit buckets (`Fin (2^d)`),
  using "nearest integer" rounding.
- `decompress` maps a `d`-bit bucket back into `ZMod q`.

We then lift these operations coefficient-wise to:

- polynomials as coefficient vectors `Poly n q` and
- the cyclotomic quotient ring `Rq` via `RingReductions.rqCoeffs` / `polyToRq`.

This module does **not** prove the tight compression error bounds yet; the core correctness
connection is done at the K-PKE layer by explicitly threading a "compression noise" term.
The numerical/tight bounds are tracked separately.

Reference: NIST FIPS 203, Section 4.2.1 (Compress / Decompress).
-/

namespace HeytingLean
namespace Crypto
namespace KEM
namespace FIPS203

open scoped BigOperators
open HeytingLean.Crypto.Lattice

namespace Compress

private def pow2 (d : Nat) : Nat := 2 ^ d

private def roundBias (d : Nat) : Nat :=
  match d with
  | 0 => 0
  | Nat.succ d' => 2 ^ d'

variable (q : Nat) [NeZero q]

/-- Compress: `ZMod q → Fin (2^d)` via scaled rounding and reduction mod `2^d`. -/
def compress (d : Nat) (x : ZMod q) : Fin (pow2 d) :=
  let xNat := x.val
  let scaled := (xNat * pow2 d + q / 2) / q
  ⟨scaled % pow2 d, Nat.mod_lt _ (by
    have : 0 < pow2 d := by
      dsimp [pow2]
      exact Nat.pow_pos (Nat.succ_pos 1)
    exact this)⟩

/-- Decompress: `Fin (2^d) → ZMod q` via scaled rounding. -/
def decompress (d : Nat) (y : Fin (pow2 d)) : ZMod q :=
  let scaled := (y.val * q + roundBias d) / pow2 d
  (scaled : ZMod q)

/-- Centered distance in `ZMod q`, measured using `valMinAbs`. -/
def centeredDist (x y : ZMod q) : Nat :=
  Int.natAbs ((x - y).valMinAbs)

/-- Coefficient-level compression error distance. -/
def compressionError (d : Nat) (x : ZMod q) : Nat :=
  centeredDist (q := q) x (decompress q d (compress q d x))

/-!
## Lifts (coeff vectors and quotient ring)
-/

abbrev CompressedCoeff (d : Nat) : Type :=
  Fin (pow2 d)

abbrev CompressedPoly (n d : Nat) : Type :=
  Fin n → CompressedCoeff d

def compressPoly {n : Nat} (d : Nat) (v : Poly n q) : CompressedPoly n d :=
  fun i => compress q d (v i)

def decompressPoly {n : Nat} (d : Nat) (v : CompressedPoly n d) : Poly n q :=
  fun i => decompress q d (v i)

noncomputable def compressRq (P : MLWEParams) (d : Nat) (x : RingReductions.Rq P) :
    CompressedPoly P.n d :=
  compressPoly (q := P.q) d (RingReductions.rqCoeffs P x)

noncomputable def decompressRq (P : MLWEParams) (d : Nat) (x : CompressedPoly P.n d) :
    RingReductions.Rq P :=
  RingReductions.polyToRq P (decompressPoly (q := P.q) d x)

noncomputable def compressionErrorRq (P : MLWEParams) (d : Nat) (x : RingReductions.Rq P) :
    RingReductions.Rq P :=
  decompressRq P d (compressRq P d x) - x

noncomputable def compressModVec (P : MLWEParams) (d : Nat) (x : RingReductions.RModVec P) :
    Fin P.k → CompressedPoly P.n d :=
  fun i => compressRq (P := P) d (x i)

noncomputable def decompressModVec (P : MLWEParams) (d : Nat)
    (x : Fin P.k → CompressedPoly P.n d) : RingReductions.RModVec P :=
  fun i => decompressRq (P := P) d (x i)

noncomputable def compressionErrorModVec (P : MLWEParams) (d : Nat) (x : RingReductions.RModVec P) :
    RingReductions.RModVec P :=
  decompressModVec (P := P) d (compressModVec (P := P) d x) - x

end Compress

end FIPS203
end KEM
end Crypto
end HeytingLean
