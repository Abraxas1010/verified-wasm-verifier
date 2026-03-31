import HeytingLean.Crypto.KEM.MLKEMCompressBounds

namespace HeytingLean.Tests.Crypto.PQCLatticeCompressBoundsSanity

open HeytingLean.Crypto.KEM.FIPS203
open HeytingLean.Crypto.KEM.FIPS203.Compress
open HeytingLean.Crypto.KEM.FIPS203.CompressBounds

abbrev F : Type := ZMod 3329

example : compressionError (q := 3329) (d := 10) (0 : F) ≤ 2 :=
  compressionError_du10_le2 (x := (0 : F))

example : compressionError (q := 3329) (d := 4) (0 : F) ≤ 105 :=
  compressionError_dv4_le105 (x := (0 : F))

example : compressionError (q := 3329) (d := 11) (0 : F) ≤ 1 :=
  compressionError_du11_le1 (x := (0 : F))

example : compressionError (q := 3329) (d := 5) (0 : F) ≤ 53 :=
  compressionError_dv5_le53 (x := (0 : F))

end HeytingLean.Tests.Crypto.PQCLatticeCompressBoundsSanity

