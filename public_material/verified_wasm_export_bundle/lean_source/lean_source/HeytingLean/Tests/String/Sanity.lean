import HeytingLean.Physics.String.CFT
import HeytingLean.Physics.String.Modular

/-
Compile-only sanity: define a small CFT partition and compute a tiny modular closure.
-/

namespace HeytingLean
namespace Tests
namespace String

open HeytingLean.Physics.String

def freeBoson : HeytingLean.Physics.String.WorldsheetCFT :=
  { name := "FreeBosonDemo"
  , centralCharge := 1.0
  , partitionZ := #[1.0, 24.0, 324.0, 3200.0] }

def Z0 : Partition := freeBoson.partitionZ

def orbit : Array Partition := HeytingLean.Physics.String.closure Z0 3

end String
end Tests
end HeytingLean
