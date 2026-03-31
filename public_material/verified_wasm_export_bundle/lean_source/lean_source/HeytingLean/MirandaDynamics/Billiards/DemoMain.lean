import HeytingLean.MirandaDynamics.Billiards.CantorEncoding

/-!
# miranda_billiards_demo

This runtime demo is intentionally **computable-only**:

* it exercises the integer-index interleaving `tapeIndex/indexNat`,
* it prints a few tape indices and digits.

The real-analysis parts (`encodeTape`, `cantorEncode`, etc.) are noncomputable by design, so we do
not attempt to evaluate them at runtime.

No file IO is performed; this should not crash under hostile env/PATH QA tests.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Billiards

namespace Demo

def showList {α : Type} [ToString α] (xs : List α) : String :=
  "[" ++ String.intercalate ", " (xs.map toString) ++ "]"

def sampleTape : Tape :=
  fun z => z = 0

def main (_argv : List String) : IO UInt32 := do
  IO.println "[miranda_billiards_demo] tape index interleaving"
  let ns : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]
  let zs : List Int := ns.map tapeIndex
  IO.println s!"[demo] tapeIndex 0..7 = {showList zs}"

  IO.println "[miranda_billiards_demo] inverse check tapeIndex(indexNat z)=z"
  let ztest : List Int := [0, 1, -1, 2, -2, 3, -3]
  let ok : List Bool := ztest.map (fun z => decide (tapeIndex (indexNat z) = z))
  IO.println s!"[demo] z samples = {showList ztest}"
  IO.println s!"[demo] checks    = {showList ok}"

  IO.println "[miranda_billiards_demo] digit stream for sampleTape (first 8 digits)"
  let ds : List Bool := ns.map (digits sampleTape)
  IO.println s!"[demo] digits(sampleTape)[0..7] = {showList ds}"

  return 0

end Demo

end Billiards
end MirandaDynamics
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.MirandaDynamics.Billiards.Demo.main args

