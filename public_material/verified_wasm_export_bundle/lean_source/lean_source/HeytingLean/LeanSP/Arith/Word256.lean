import Init.Data.BitVec

/-!
# LeanSP.Arith.Word256

EVM 256-bit word arithmetic. All operations match the EVM Yellow Paper specification.

Constraint H7: `Word256 := BitVec 256` — uses Lean's built-in bitvector type
with full Mathlib/Batteries lemma support. No custom `Fin (2^256)` wrappers.
-/

namespace LeanSP.Arith

abbrev Word256 := BitVec 256

def Word256.zero : Word256 := BitVec.ofNat 256 0
def Word256.one : Word256 := BitVec.ofNat 256 1
def Word256.maxVal : Word256 := BitVec.allOnes 256

/-- EVM ADD: modular addition (mod 2^256). -/
@[inline] def add (a b : Word256) : Word256 := a + b

/-- EVM MUL: modular multiplication (mod 2^256). -/
@[inline] def mul (a b : Word256) : Word256 := a * b

/-- EVM SUB: modular subtraction (wraps on underflow). -/
@[inline] def sub (a b : Word256) : Word256 := a - b

/-- EVM DIV: unsigned division. `div(a, 0) = 0` (EVM convention). -/
def div (a b : Word256) : Word256 :=
  if b == Word256.zero then Word256.zero else a / b

/-- EVM MOD: unsigned modulo. `mod(a, 0) = 0` (EVM convention). -/
def mod (a b : Word256) : Word256 :=
  if b == Word256.zero then Word256.zero else a % b

/-- EVM ADDMOD: `(a + b) % N` without intermediate overflow. Returns 0 if `N = 0`. -/
def addmod (a b n : Word256) : Word256 :=
  if n == Word256.zero then Word256.zero
  else BitVec.ofNat 256 ((a.toNat + b.toNat) % n.toNat)

/-- EVM MULMOD: `(a * b) % N` without intermediate overflow. Returns 0 if `N = 0`. -/
def mulmod (a b n : Word256) : Word256 :=
  if n == Word256.zero then Word256.zero
  else BitVec.ofNat 256 ((a.toNat * b.toNat) % n.toNat)

/-- EVM EXP: `base^exponent mod 2^256`. -/
def exp (base exponent : Word256) : Word256 :=
  BitVec.ofNat 256 (base.toNat ^ exponent.toNat)

/-- EVM LT: unsigned less-than. Returns 1 or 0. -/
def lt (a b : Word256) : Word256 := if a.toNat < b.toNat then Word256.one else Word256.zero

/-- EVM GT: unsigned greater-than. Returns 1 or 0. -/
def gt (a b : Word256) : Word256 := if a.toNat > b.toNat then Word256.one else Word256.zero

/-- EVM EQ: equality check. Returns 1 or 0. -/
def eq (a b : Word256) : Word256 := if a == b then Word256.one else Word256.zero

/-- EVM ISZERO: returns 1 if value is 0, else 0. -/
def isZero (a : Word256) : Word256 := if a == Word256.zero then Word256.one else Word256.zero

-- Bitwise operations: BitVec provides these natively
@[inline] def and (a b : Word256) : Word256 := a &&& b
@[inline] def or (a b : Word256) : Word256 := a ||| b
@[inline] def xor (a b : Word256) : Word256 := a ^^^ b
@[inline] def not (a : Word256) : Word256 := ~~~ a

/-- EVM SHL: shift left. `shl(shift, value) = value << shift`. -/
def shl (shift value : Word256) : Word256 :=
  if shift.toNat ≥ 256 then Word256.zero
  else value <<< shift.toNat

/-- EVM SHR: logical shift right. `shr(shift, value) = value >>> shift`. -/
def shr (shift value : Word256) : Word256 :=
  if shift.toNat ≥ 256 then Word256.zero
  else value >>> shift.toNat

/-- EVM SAR: arithmetic shift right (sign-preserving). -/
def sar (shift value : Word256) : Word256 :=
  if shift.toNat ≥ 256 then
    -- If shift ≥ 256, result is all 0s or all 1s depending on sign bit
    if value.toNat ≥ 2^255 then Word256.maxVal else Word256.zero
  else
    BitVec.sshiftRight value shift.toNat

/-- EVM SIGNEXTEND: sign-extend `x` from byte `b`. -/
def signextend (b x : Word256) : Word256 :=
  if b.toNat ≥ 31 then x
  else
    let bitPos := b.toNat * 8 + 7
    let mask := BitVec.ofNat 256 ((1 <<< (bitPos + 1)) - 1)
    let signBit := (x.toNat >>> bitPos) &&& 1
    if signBit == 1 then
      x ||| (~~~ mask)  -- fill upper bits with 1s
    else
      x &&& mask  -- fill upper bits with 0s

/-- EVM BYTE: extract byte `i` from `x` (byte 0 = most significant). -/
def byte_ (i x : Word256) : Word256 :=
  if i.toNat ≥ 32 then Word256.zero
  else
    let shift := (31 - i.toNat) * 8
    BitVec.ofNat 256 ((x.toNat >>> shift) &&& 0xFF)

/-- Convert Word256 to 32 big-endian bytes. -/
def word256ToBytesBE (w : Word256) : ByteArray := Id.run do
  let n := w.toNat
  let mut arr := ByteArray.mkEmpty 32
  for i in [:32] do
    arr := arr.push (UInt8.ofNat ((n >>> (8 * (31 - i))) % 256))
  return arr

/-- Read 32 big-endian bytes from a ByteArray at a given offset into a Word256. -/
def bytesToWord256BE (bytes : ByteArray) (offset : Nat) : Word256 := Id.run do
  let mut n : Nat := 0
  for i in [:32] do
    let idx := offset + i
    let b := if idx < bytes.size then bytes.get! idx else 0
    n := n * 256 + b.toNat
  BitVec.ofNat 256 n

end LeanSP.Arith
