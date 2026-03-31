import HeytingLean.Physics.String.QSeries

/-
Worldsheet CFT scaffold: finite partitions and minimal metadata.
`Partition` is a small coefficient array intended for demos; no heavy
math is required, but the definitions are fully honest.
-/

namespace HeytingLean
namespace Physics
namespace String

abbrev Partition := Array Float

structure WorldsheetCFT where
  name        : String
  centralCharge : Float
  partitionZ : Partition
deriving Repr

namespace WorldsheetCFT

@[simp] def coeff (C : WorldsheetCFT) (i : Nat) : Float :=
  if i < C.partitionZ.size then C.partitionZ[i]! else 0.0

@[simp] def toQSeries (C : WorldsheetCFT) :
    HeytingLean.Physics.String.QSeries :=
  { coeffs := C.partitionZ }

@[simp] def coeff_q (C : WorldsheetCFT) (i : Nat) : Float :=
  C.toQSeries.coeffAt i

end WorldsheetCFT

end String
end Physics
end HeytingLean
