namespace HeytingLean.Util.Base64

private def b64Char (n : Nat) : Char :=
  if h1 : n < 26 then
    Char.ofNat (("A".get! 0).toNat + n)
  else if h2 : n < 52 then
    Char.ofNat (("a".get! 0).toNat + (n - 26))
  else if h3 : n < 62 then
    Char.ofNat (("0".get! 0).toNat + (n - 52))
  else if n = 62 then '+'
  else '/'

def encode (bs : ByteArray) : String :=
  let sz := bs.size
  let c03 : UInt8 := UInt8.ofNat 3
  let c0F : UInt8 := UInt8.ofNat 15
  let c3F : UInt8 := UInt8.ofNat 63
  let rec loop (i : Nat) (acc : List Char) : String :=
    if i < sz then
      let b0 := bs.get! i
      if i + 1 < sz then
        let b1 := bs.get! (i+1)
        if i + 2 < sz then
          let b2 := bs.get! (i+2)
          -- 3 bytes -> 4 chars
          let i0 : Nat := (b0 >>> 2).toNat
          let i1 : Nat := (((b0 &&& c03) <<< 4) ||| (b1 >>> 4)).toNat
          let i2 : Nat := (((b1 &&& c0F) <<< 2) ||| (b2 >>> 6)).toNat
          let i3 : Nat := (b2 &&& c3F).toNat
          loop (i+3) (b64Char i3 :: b64Char i2 :: b64Char i1 :: b64Char i0 :: acc)
        else
          -- 2 bytes -> 3 chars + '='
          let i0 : Nat := (b0 >>> 2).toNat
          let i1 : Nat := (((b0 &&& c03) <<< 4) ||| (b1 >>> 4)).toNat
          let i2 : Nat := ((b1 &&& c0F) <<< 2).toNat
          loop (i+2) ('=' :: b64Char i2 :: b64Char i1 :: b64Char i0 :: acc)
      else
        -- 1 byte -> 2 chars + '=='
        let i0 : Nat := (b0 >>> 2).toNat
        let i1 : Nat := ((b0 &&& c03) <<< 4).toNat
        loop (i+1) ('=' :: '=' :: b64Char i1 :: b64Char i0 :: acc)
    else
      String.mk acc.reverse
  loop 0 []

end HeytingLean.Util.Base64
