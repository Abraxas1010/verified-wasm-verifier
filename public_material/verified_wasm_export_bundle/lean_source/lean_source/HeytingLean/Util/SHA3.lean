import HeytingLean.Util.SHA

namespace HeytingLean
namespace Util
namespace SHA3

private def rol64 (x : UInt64) (n : Nat) : UInt64 :=
  let n := n % 64
  if n = 0 then
    x
  else
    let s := UInt64.ofNat n
    let s' := UInt64.ofNat (64 - n)
    UInt64.shiftLeft x s ||| UInt64.shiftRight x s'

private def laneIdx (x y : Nat) : Nat :=
  x + 5 * y

private def roundConstants : Array UInt64 :=
  #[
    0x0000000000000001, 0x0000000000008082,
    0x800000000000808A, 0x8000000080008000,
    0x000000000000808B, 0x0000000080000001,
    0x8000000080008081, 0x8000000000008009,
    0x000000000000008A, 0x0000000000000088,
    0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B,
    0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080,
    0x000000000000800A, 0x800000008000000A,
    0x8000000080008081, 0x8000000000008080,
    0x0000000080000001, 0x8000000080008008
  ]

private def rhoOffsets : Array Nat :=
  #[
    0, 1, 62, 28, 27,
    36, 44, 6, 55, 20,
    3, 10, 43, 25, 39,
    41, 45, 15, 21, 8,
    18, 2, 61, 56, 14
  ]

private def loadLaneLE (bytes : Array UInt8) (off : Nat) : UInt64 := Id.run do
  let mut lane : UInt64 := 0
  for i in [0:8] do
    let b := UInt64.ofNat (bytes[off + i]!.toNat)
    lane := lane ||| UInt64.shiftLeft b (UInt64.ofNat (8 * i))
  return lane

private def appendLaneLE (out : Array UInt8) (lane : UInt64) : Array UInt8 := Id.run do
  let mut acc := out
  for i in [0:8] do
    let byte : UInt8 := UInt8.ofNat ((UInt64.shiftRight lane (UInt64.ofNat (8 * i))).toNat % 256)
    acc := acc.push byte
  return acc

private def theta (state : Array UInt64) : Array UInt64 := Id.run do
  let mut c : Array UInt64 := Array.replicate 5 0
  for x in [0:5] do
    c := c.set! x
      (state[laneIdx x 0]! ^^^ state[laneIdx x 1]! ^^^ state[laneIdx x 2]! ^^^
       state[laneIdx x 3]! ^^^ state[laneIdx x 4]!)
  let mut d : Array UInt64 := Array.replicate 5 0
  for x in [0:5] do
    d := d.set! x (c[(x + 4) % 5]! ^^^ rol64 c[(x + 1) % 5]! 1)
  let mut out := state
  for y in [0:5] do
    for x in [0:5] do
      let idx := laneIdx x y
      out := out.set! idx (out[idx]! ^^^ d[x]!)
  return out

private def rhoPi (state : Array UInt64) : Array UInt64 := Id.run do
  let mut out : Array UInt64 := Array.replicate 25 0
  for y in [0:5] do
    for x in [0:5] do
      let idx := laneIdx x y
      let newX := y
      let newY := (2 * x + 3 * y) % 5
      out := out.set! (laneIdx newX newY) (rol64 state[idx]! rhoOffsets[idx]!)
  return out

private def chi (state : Array UInt64) : Array UInt64 := Id.run do
  let mut out : Array UInt64 := Array.replicate 25 0
  for y in [0:5] do
    for x in [0:5] do
      let idx := laneIdx x y
      let a := state[idx]!
      let b := state[laneIdx ((x + 1) % 5) y]!
      let c := state[laneIdx ((x + 2) % 5) y]!
      out := out.set! idx (a ^^^ ((~~~ b) &&& c))
  return out

private def iota (state : Array UInt64) (round : Nat) : Array UInt64 :=
  state.set! 0 (state[0]! ^^^ roundConstants[round]!)

/-- The Keccak-f[1600] permutation on the 25-lane state. -/
def keccakF1600 (state : Array UInt64) : Array UInt64 := Id.run do
  let mut st := state
  for round in [0:24] do
    st := theta st
    st := rhoPi st
    st := chi st
    st := iota st round
  return st

private def absorbRate (state : Array UInt64) (block : Array UInt8) (rate : Nat) : Array UInt64 := Id.run do
  let mut st := state
  for lane in [0:(rate / 8)] do
    let off := 8 * lane
    st := st.set! lane (st[lane]! ^^^ loadLaneLE block off)
  return st

private def stateBytes (state : Array UInt64) (rate : Nat) : Array UInt8 := Id.run do
  let mut out : Array UInt8 := #[]
  for lane in [0:(rate / 8)] do
    out := appendLaneLE out state[lane]!
  return out

private def sponge (rate : Nat) (domain : UInt8) (input : ByteArray) (outLen : Nat) : ByteArray := Id.run do
  let bytes := input.data
  let mut state : Array UInt64 := Array.replicate 25 0
  let mut off := 0
  while off + rate ≤ bytes.size do
    let block := bytes.extract off (off + rate)
    state := absorbRate state block rate
    state := keccakF1600 state
    off := off + rate
  let remaining := bytes.size - off
  let mut finalBlock : Array UInt8 := Array.replicate rate 0
  for i in [0:remaining] do
    finalBlock := finalBlock.set! i bytes[off + i]!
  finalBlock := finalBlock.set! remaining domain
  finalBlock := finalBlock.set! (rate - 1) (finalBlock[rate - 1]! ^^^ UInt8.ofNat 0x80)
  state := absorbRate state finalBlock rate
  state := keccakF1600 state
  let mut out : Array UInt8 := #[]
  while out.size < outLen do
    let block := stateBytes state rate
    let take := min rate (outLen - out.size)
    for i in [0:take] do
      out := out.push block[i]!
    if out.size < outLen then
      state := keccakF1600 state
  return ByteArray.mk out

def sha3_256 (input : ByteArray) : ByteArray :=
  sponge 136 (UInt8.ofNat 0x06) input 32

def sha3_512 (input : ByteArray) : ByteArray :=
  sponge 72 (UInt8.ofNat 0x06) input 64

def shake128 (input : ByteArray) (outLen : Nat) : ByteArray :=
  sponge 168 (UInt8.ofNat 0x1F) input outLen

def shake256 (input : ByteArray) (outLen : Nat) : ByteArray :=
  sponge 136 (UInt8.ofNat 0x1F) input outLen

def sha3_256Hex (input : ByteArray) : String :=
  SHA256.toHex (sha3_256 input)

def sha3_512Hex (input : ByteArray) : String :=
  SHA256.toHex (sha3_512 input)

def shake128Hex (input : ByteArray) (outLen : Nat) : String :=
  SHA256.toHex (shake128 input outLen)

def shake256Hex (input : ByteArray) (outLen : Nat) : String :=
  SHA256.toHex (shake256 input outLen)

end SHA3
end Util
end HeytingLean
