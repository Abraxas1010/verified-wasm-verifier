import HeytingLean.Crypto.KEM.MLKEM203Params
import HeytingLean.Util.SHA
import HeytingLean.Util.SHA3

namespace HeytingLean
namespace Crypto
namespace KEM
namespace FIPS203
namespace ByteCodec

private def mkBA (xs : Array UInt8) : ByteArray := ByteArray.mk xs

private def takeBytes (n : Nat) (bytes : ByteArray) : ByteArray :=
  mkBA (bytes.data.extract 0 n)

private def dropBytes (n : Nat) (bytes : ByteArray) : ByteArray :=
  mkBA (bytes.data.extract n bytes.size)

private def sliceBytes (start stop : Nat) (bytes : ByteArray) : ByteArray :=
  mkBA (bytes.data.extract start stop)

private def pow2 (d : Nat) : Nat := 2 ^ d

private def coeffModulus (q d : Nat) : Nat :=
  if d < 12 then pow2 d else q

private def bitAtLE (b : UInt8) (i : Nat) : UInt8 :=
  UInt8.ofNat ((b.toNat / pow2 i) % 2)

/-- FIPS 203 `BytesToBits`: bytes expand little-endian within each byte. -/
def bytesToBits (bytes : ByteArray) : Array UInt8 := Id.run do
  let mut out : Array UInt8 := #[]
  for b in bytes.data do
    for i in [0:8] do
      out := out.push (bitAtLE b i)
  return out

/-- FIPS 203 `BitsToBytes`: bits are packed little-endian within each byte. -/
def bitsToBytes (bits : Array UInt8) : ByteArray := Id.run do
  let mut out : Array UInt8 := #[]
  let byteCount := (bits.size + 7) / 8
  for i in [0:byteCount] do
    let mut acc : Nat := 0
    let mut weight : Nat := 1
    for j in [0:8] do
      let idx := i * 8 + j
      let bit : Nat := if h : idx < bits.size then (bits[idx]'h).toNat else 0
      acc := acc + bit * weight
      weight := weight * 2
    out := out.push (UInt8.ofNat acc)
  return mkBA out

/-- FIPS 203 Algorithm 5 on an arbitrary array of `d`-bit coefficients. -/
def byteEncode (d : Nat) (coeffs : Array Nat) : ByteArray := Id.run do
  let mut bits : Array UInt8 := #[]
  for coeff in coeffs do
    let mut a := coeff
    for _ in [0:d] do
      bits := bits.push (UInt8.ofNat (a % 2))
      a := a / 2
  return bitsToBytes bits

/-- FIPS 203 Algorithm 6 on an arbitrary byte array, grouped into `d`-bit coefficients. -/
def byteDecode (q d : Nat) (bytes : ByteArray) : Array Nat := Id.run do
  let bits := bytesToBits bytes
  let coeffCount := bits.size / d
  let modulus := coeffModulus q d
  let mut out : Array Nat := #[]
  for i in [0:coeffCount] do
    let mut acc : Nat := 0
    let mut weight : Nat := 1
    for j in [0:d] do
      let idx := i * d + j
      let bit := bits[idx]!.toNat
      acc := acc + bit * weight
      weight := weight * 2
    out := out.push (acc % modulus)
  return out

def byteEncode12 (coeffs : Array Nat) : ByteArray :=
  byteEncode 12 coeffs

def byteDecode12 (q : Nat) (bytes : ByteArray) : Array Nat :=
  byteDecode q 12 bytes

def ekPrefixBytes (p : MLKEM203Params) : Nat := 384 * p.k

def embeddedEk (p : MLKEM203Params) (dk : ByteArray) : ByteArray :=
  sliceBytes (384 * p.k) (768 * p.k + 32) dk

def embeddedHash (p : MLKEM203Params) (dk : ByteArray) : ByteArray :=
  sliceBytes (768 * p.k + 32) (768 * p.k + 64) dk

def embeddedRejectSeed (p : MLKEM203Params) (dk : ByteArray) : ByteArray :=
  sliceBytes (768 * p.k + 64) (768 * p.k + 96) dk

private def ekModulusCheck (p : MLKEM203Params) (ek : ByteArray) : Bool :=
  byteEncode12 (byteDecode12 p.q (takeBytes (ekPrefixBytes p) ek)) ==
    takeBytes (ekPrefixBytes p) ek

/-- FIPS 203 encapsulation-key modulus check: `ByteEncode12(ByteDecode12(ek[..])) = ek[..]`. -/
def checkEncapsulationKey (p : MLKEM203Params) (ek : ByteArray) : Bool :=
  if ek.size != p.ekSize then
    false
  else
    ekModulusCheck p ek

def checkCiphertext (p : MLKEM203Params) (ct : ByteArray) : Bool :=
  ct.size == p.ctSize

/-- FIPS 203 decapsulation-key check: size plus embedded `H(ek)` consistency. -/
def checkDecapsulationKey (p : MLKEM203Params) (dk : ByteArray) : Bool :=
  if dk.size != p.dkSize then
    false
  else
    embeddedHash p dk == Util.SHA3.sha3_256 (embeddedEk p dk)

/-- Useful stronger local check for a generated keypair: the stored `ek` also passes the modulus check. -/
def checkStoredKeypair (p : MLKEM203Params) (ek dk : ByteArray) : Bool :=
  checkEncapsulationKey p ek &&
    checkDecapsulationKey p dk &&
    embeddedEk p dk == ek &&
    (embeddedRejectSeed p dk).size == 32

private def hexNibble? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then
    some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then
    some (10 + c.toNat - 'a'.toNat)
  else if 'A' ≤ c && c ≤ 'F' then
    some (10 + c.toNat - 'A'.toNat)
  else
    none

def hexToBytes? (s : String) : Option ByteArray := Id.run do
  let chars := s.data.toArray
  if chars.size % 2 != 0 then
    return none
  let mut out : Array UInt8 := #[]
  for i in [0:(chars.size / 2)] do
    let hi? := hexNibble? chars[2 * i]!
    let lo? := hexNibble? chars[2 * i + 1]!
    match hi?, lo? with
    | some hi, some lo =>
        out := out.push (UInt8.ofNat (16 * hi + lo))
    | _, _ =>
        return none
  return some (mkBA out)

def bytesToHex (bytes : ByteArray) : String :=
  Util.SHA256.toHex bytes

end ByteCodec
end FIPS203
end KEM
end Crypto
end HeytingLean
