import HeytingLean.Crypto.KEM.MLKEMStandardRuntime

namespace HeytingLean.Tests.Crypto.MLKEMStandardRuntimeSanity

open HeytingLean.Crypto.KEM.FIPS203

private def zeroBytes (n : Nat) : ByteArray :=
  ByteArray.mk (Array.replicate n 0)

example : ByteCodec.checkCiphertext mlkem512 (zeroBytes mlkem512.ctSize) = true := by
  native_decide

example : ByteCodec.checkCiphertext mlkem512 ByteArray.empty = false := by
  native_decide

example : (ByteCodec.byteDecode 3329 12 (ByteCodec.byteEncode 12 #[0, 1, 3328])).size = 3 := by
  native_decide

#check StandardRuntime.keygen
#check StandardRuntime.encaps
#check StandardRuntime.decaps
#check StandardRuntime.roundtrip

end HeytingLean.Tests.Crypto.MLKEMStandardRuntimeSanity
