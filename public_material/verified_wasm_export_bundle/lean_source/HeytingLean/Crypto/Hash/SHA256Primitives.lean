import Std.Tactic.BVDecide
import Init.Data.UInt.Basic
import Init.Data.BitVec

namespace HeytingLean
namespace Crypto
namespace Hash

namespace SHA256Primitives

abbrev Word32 := BitVec 32

@[inline] def u32ToWord32 (x : UInt32) : Word32 := x.toBitVec
@[inline] def word32ToU32 (x : Word32) : UInt32 := UInt32.ofBitVec x

@[inline] def rotr32 (x : Word32) (n : Nat) : Word32 :=
  BitVec.rotateRight x n

@[inline] def shr32 (x : Word32) (n : Nat) : Word32 :=
  BitVec.ushiftRight x n

@[inline] def ch (x y z : Word32) : Word32 :=
  (x &&& y) ^^^ ((~~~x) &&& z)

@[inline] def maj (x y z : Word32) : Word32 :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

@[inline] def Sigma0 (x : Word32) : Word32 :=
  rotr32 x 2 ^^^ rotr32 x 13 ^^^ rotr32 x 22

@[inline] def Sigma1 (x : Word32) : Word32 :=
  rotr32 x 6 ^^^ rotr32 x 11 ^^^ rotr32 x 25

@[inline] def sigma0 (x : Word32) : Word32 :=
  rotr32 x 7 ^^^ rotr32 x 18 ^^^ shr32 x 3

@[inline] def sigma1 (x : Word32) : Word32 :=
  rotr32 x 17 ^^^ rotr32 x 19 ^^^ shr32 x 10

@[inline] def Sigma0_u32 (x : UInt32) : UInt32 :=
  word32ToU32 (Sigma0 (u32ToWord32 x))

@[inline] def Sigma1_u32 (x : UInt32) : UInt32 :=
  word32ToU32 (Sigma1 (u32ToWord32 x))

@[inline] def sigma0_u32 (x : UInt32) : UInt32 :=
  word32ToU32 (sigma0 (u32ToWord32 x))

@[inline] def sigma1_u32 (x : UInt32) : UInt32 :=
  word32ToU32 (sigma1 (u32ToWord32 x))

@[inline] def ch_u32 (x y z : UInt32) : UInt32 :=
  word32ToU32 (ch (u32ToWord32 x) (u32ToWord32 y) (u32ToWord32 z))

@[inline] def maj_u32 (x y z : UInt32) : UInt32 :=
  word32ToU32 (maj (u32ToWord32 x) (u32ToWord32 y) (u32ToWord32 z))

theorem rotr32_zero (x : Word32) : rotr32 x 0 = x := by
  simp [rotr32]
  bv_decide

theorem maj_swap12 (x y z : Word32) : maj x y z = maj y x z := by
  simp [maj]
  bv_decide

theorem maj_swap23 (x y z : Word32) : maj x y z = maj x z y := by
  simp [maj]
  bv_decide

theorem maj_idem_left (x z : Word32) : maj x x z = x := by
  simp [maj]
  bv_decide

theorem ch_eq_or (x y z : Word32) : ch x y z = (x &&& y) ||| ((~~~x) &&& z) := by
  simp [ch]
  bv_decide

theorem Sigma0_xor_linear (x y : Word32) : Sigma0 (x ^^^ y) = Sigma0 x ^^^ Sigma0 y := by
  simp [Sigma0, rotr32]
  bv_decide

theorem Sigma1_xor_linear (x y : Word32) : Sigma1 (x ^^^ y) = Sigma1 x ^^^ Sigma1 y := by
  simp [Sigma1, rotr32]
  bv_decide

theorem sigma0_xor_linear (x y : Word32) : sigma0 (x ^^^ y) = sigma0 x ^^^ sigma0 y := by
  simp [sigma0, rotr32, shr32]
  bv_decide

theorem sigma1_xor_linear (x y : Word32) : sigma1 (x ^^^ y) = sigma1 x ^^^ sigma1 y := by
  simp [sigma1, rotr32, shr32]
  bv_decide

end SHA256Primitives

end Hash
end Crypto
end HeytingLean
