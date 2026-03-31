import HeytingLean.Crypto.Hash.SHA256Primitives
 
namespace HeytingLean
namespace Tests
namespace Crypto

open HeytingLean.Crypto.Hash.SHA256Primitives

example : rotr32 (0x80000000 : Word32) 1 = (0x40000000 : Word32) := by
  simp [rotr32]

example (y z : Word32) : ch (0xFFFFFFFF : Word32) y z = y := by
  simp [ch]
  bv_decide

example (y z : Word32) : ch (0 : Word32) y z = z := by
  simp [ch]
  bv_decide

example (x z : Word32) : maj x x z = x := by
  simpa using maj_idem_left (x := x) (z := z)

end Crypto
end Tests
end HeytingLean
