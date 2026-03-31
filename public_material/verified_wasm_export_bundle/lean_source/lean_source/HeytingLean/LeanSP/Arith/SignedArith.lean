import HeytingLean.LeanSP.Arith.Word256

/-!
# LeanSP.Arith.SignedArith

Two's complement signed arithmetic for EVM (SDIV, SMOD, SLT, SGT).
Reference: LeanCP's `wrapSignedInt` at CSyntax.lean:39-43 for the same pattern.
-/

namespace LeanSP.Arith

/-- Two's complement interpretation: values ≥ 2^255 are negative. -/
def toSigned (w : Word256) : Int :=
  if w.toNat < 2^255 then Int.ofNat w.toNat
  else Int.ofNat w.toNat - Int.ofNat (2^256)

/-- Convert signed integer back to Word256 (two's complement encoding). -/
def fromSigned (i : Int) : Word256 :=
  BitVec.ofNat 256 (Int.toNat (i % Int.ofNat (2^256)))

/-- The minimum signed 256-bit value: -2^255. -/
def minInt256 : Word256 := BitVec.ofNat 256 (2^255)

/-- EVM SDIV: signed division. `SDIV(a, 0) = 0`. `SDIV(MIN_INT256, -1) = MIN_INT256`. -/
def sdiv (a b : Word256) : Word256 :=
  if b == Word256.zero then Word256.zero
  else
    let sa := toSigned a
    let sb := toSigned b
    -- EVM special case: MIN_INT256 / -1 = MIN_INT256 (no overflow to positive)
    if a == minInt256 && sb == -1 then minInt256
    else fromSigned (sa / sb)

/-- EVM SMOD: signed modulo. `SMOD(a, 0) = 0`. Sign of result = sign of `a`. -/
def smod (a b : Word256) : Word256 :=
  if b == Word256.zero then Word256.zero
  else
    let sa := toSigned a
    let sb := toSigned b
    -- Int.mod in Lean already preserves sign of dividend
    fromSigned (sa % sb)

/-- EVM SLT: signed less-than. -/
def slt (a b : Word256) : Word256 :=
  if toSigned a < toSigned b then Word256.one else Word256.zero

/-- EVM SGT: signed greater-than. -/
def sgt (a b : Word256) : Word256 :=
  if toSigned a > toSigned b then Word256.one else Word256.zero

end LeanSP.Arith
