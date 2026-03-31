import Lean
import Lean.Data.Json

namespace HeytingLean
namespace Util

open Lean

/-
Pure SHA-256 implementation and IO helpers.

We provide a self-contained SHA-256 over `ByteArray`, then expose
hex-encoded IO wrappers. When the external `hashutil` binary is
available and `LOF_SHA_MODE=external`, we use it as an optional
accelerator; otherwise we fall back to the pure Lean implementation.
-/

namespace SHA256

private def rotr (x : UInt32) (n : Nat) : UInt32 :=
  let s  := UInt32.ofNat n
  let s' := UInt32.ofNat (32 - n)
  UInt32.shiftRight x s ||| UInt32.shiftLeft x s'

private def shr (x : UInt32) (n : Nat) : UInt32 :=
  UInt32.shiftRight x (UInt32.ofNat n)

private def k : Array UInt32 :=
  #[
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
    0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
    0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
    0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
    0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
    0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
    0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
    0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
  ]

private def h0 : Array UInt32 :=
  #[
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
  ]

private def pad (input : ByteArray) : ByteArray := Id.run do
  let lenBytes := input.size
  let bitLen : Nat := lenBytes * 8
  let mut arr : Array UInt8 := input.data
  -- append 0x80
  arr := arr.push (UInt8.ofNat 0x80)
  -- pad with zeros until length ≡ 56 mod 64
  let total1 := lenBytes + 1
  let rem := total1 % 64
  let padZeros :=
    if rem ≤ 56 then
      56 - rem
    else
      64 - (rem - 56)
  for _ in [0:padZeros] do
    arr := arr.push (UInt8.ofNat 0)
  -- append 64-bit big-endian bit length
  for i in [0:8] do
    let shift := (7 - i) * 8
    let byteVal : Nat := (bitLen / (2 ^ shift)) % 256
    arr := arr.push (UInt8.ofNat byteVal)
  return ByteArray.mk arr

private def bytesToWord (arr : Array UInt8) (off : Nat) : UInt32 :=
  let b0 := UInt32.ofNat (arr[off]!.toNat)
  let b1 := UInt32.ofNat (arr[off + 1]!.toNat)
  let b2 := UInt32.ofNat (arr[off + 2]!.toNat)
  let b3 := UInt32.ofNat (arr[off + 3]!.toNat)
  (b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3

private def processChunk (state : Array UInt32) (block : ByteArray) (off : Nat) : Array UInt32 := Id.run do
  let data := block.data
  -- message schedule
  let mut w : Array UInt32 := Array.replicate 64 0
  for i in [0:16] do
    w := w.set! i (bytesToWord data (off + 4 * i))
  for i in [16:64] do
    let x := w[(i - 15)]!
    let s0 := rotr x 7 ^^^ rotr x 18 ^^^ shr x 3
    let y := w[(i - 2)]!
    let s1 := rotr y 17 ^^^ rotr y 19 ^^^ shr y 10
    let wi := w[(i - 16)]! + s0 + w[(i - 7)]! + s1
    w := w.set! i wi
  -- working variables
  let mut a := state[0]!
  let mut b := state[1]!
  let mut c := state[2]!
  let mut d := state[3]!
  let mut e := state[4]!
  let mut f := state[5]!
  let mut g := state[6]!
  let mut h := state[7]!
  for i in [0:64] do
    let S1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
    let ch := (e &&& f) ^^^ ((~~~ e) &&& g)
    let temp1 := h + S1 + ch + k[i]! + w[i]!
    let S0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let temp2 := S0 + maj
    h := g
    g := f
    f := e
    e := d + temp1
    d := c
    c := b
    b := a
    a := temp1 + temp2
  -- update state
  let mut out := state
  out := out.set! 0 (out[0]! + a)
  out := out.set! 1 (out[1]! + b)
  out := out.set! 2 (out[2]! + c)
  out := out.set! 3 (out[3]! + d)
  out := out.set! 4 (out[4]! + e)
  out := out.set! 5 (out[5]! + f)
  out := out.set! 6 (out[6]! + g)
  out := out.set! 7 (out[7]! + h)
  return out

/-- Pure SHA-256 over a byte array, returning the 32-byte digest. -/
def sha256Bytes (input : ByteArray) : ByteArray := Id.run do
  let msg := pad input
  let total := msg.size
  let mut state := h0
  let mut off : Nat := 0
  while off < total do
    state := processChunk state msg off
    off := off + 64
  -- convert state words to big-endian bytes
  let mut out : Array UInt8 := Array.mkEmpty 32
  for i in [0:8] do
    let w := state[i]!
    let b0 := UInt8.ofNat ((UInt32.shiftRight w 24).toNat % 256)
    let b1 := UInt8.ofNat ((UInt32.shiftRight w 16).toNat % 256)
    let b2 := UInt8.ofNat ((UInt32.shiftRight w 8).toNat % 256)
    let b3 := UInt8.ofNat (w.toNat % 256)
    out := out.push b0
    out := out.push b1
    out := out.push b2
    out := out.push b3
  return ByteArray.mk out

private def hexDigit (n : Nat) : Char :=
  if n < 10 then
    Char.ofNat (n + '0'.toNat)
  else
    Char.ofNat (n - 10 + 'a'.toNat)

/-- Hex-encode a byte array (lowercase, 2 chars per byte). -/
def toHex (ba : ByteArray) : String := Id.run do
  let mut out : List Char := []
  for b in ba.data do
    let v := b.toNat
    let hi := v / 16
    let lo := v % 16
    -- We build the list in reverse for efficiency; reverse at the end restores byte order.
    -- Note: consing `lo` then `hi` ensures each byte prints as `hi lo` after the final reverse.
    out := hexDigit lo :: hexDigit hi :: out
  String.mk out.reverse

/-- Convenience helper: SHA-256 hex digest of a byte array. -/
def sha256Hex (ba : ByteArray) : String :=
  toHex (sha256Bytes ba)

end SHA256

private def findHashutil? : IO (Option System.FilePath) := do
  match (← IO.getEnv "LOF_RUST_BIN_DIR") with
  | some dir =>
      let p := (System.FilePath.mk dir) / "hashutil"
      try
        if (← p.pathExists) then return some p else return none
      catch _ => return none
  | none => return none

private def getShaMode : IO String := do
  return (← IO.getEnv "LOF_SHA_MODE").getD "pure"

private def sha256HexOfStringExternal (s : String) : IO (Option String) := do
  match (← findHashutil?) with
  | none => return none
  | some exe =>
      let cwd ← IO.currentDir
      let dir := cwd / System.FilePath.mk ".tmp/hash"
      (do IO.FS.createDirAll dir) |> (fun _ => pure ())
      let path := dir / "payload.txt"
      IO.FS.writeFile path s
      let out ← IO.Process.output { cmd := exe.toString, args := #[path.toString] }
      if out.exitCode != 0 then
        return none
      else
        match Json.parse out.stdout with
        | .ok j =>
            match j.getObjVal? "hex" with
            | .ok (.str hex) => return some hex
            | _ => return none
        | .error _ => return none

private def sha256HexOfFileExternal (p : System.FilePath) : IO (Option String) := do
  match (← findHashutil?) with
  | none => return none
  | some exe =>
      let out ← IO.Process.output { cmd := exe.toString, args := #[p.toString] }
      if out.exitCode != 0 then
        return none
      else
        match Json.parse out.stdout with
        | .ok j =>
            match j.getObjVal? "hex" with
            | .ok (.str hex) => return some hex
            | _ => return none
        | .error _ => return none

/-- SHA-256 hex digest of a string. Uses pure Lean SHA-256 by default;
    if `LOF_SHA_MODE=external` and `hashutil` is available, it uses the
    external tool and falls back to the pure implementation on error. -/
def sha256HexOfStringIO (s : String) : IO String := do
  let mode ← getShaMode
  if mode == "external" then
    match (← sha256HexOfStringExternal s) with
    | some hex => return hex
    | none => return SHA256.sha256Hex s.toUTF8
  else
    return SHA256.sha256Hex s.toUTF8

/-- SHA-256 hex digest of a file's contents. Mirrors `sha256HexOfStringIO`. -/
def sha256HexOfFileIO (p : System.FilePath) : IO String := do
  let mode ← getShaMode
  if mode == "external" then
    match (← sha256HexOfFileExternal p) with
    | some hex => return hex
    | none =>
        let bytes ← IO.FS.readBinFile p
        return SHA256.sha256Hex bytes
  else
    let bytes ← IO.FS.readBinFile p
    return SHA256.sha256Hex bytes

end Util
end HeytingLean
