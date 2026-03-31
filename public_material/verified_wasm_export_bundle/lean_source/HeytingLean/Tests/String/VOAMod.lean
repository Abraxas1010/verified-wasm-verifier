import HeytingLean.Physics.String.VOA
import HeytingLean.Physics.String.VOAGraded
import HeytingLean.Physics.String.CFT

/-
Compile-only: relate graded VOA truncation, CFT partitions,
and the VOA-based character field.
-/

namespace HeytingLean
namespace Tests
namespace String

open HeytingLean.Physics.String

structure DemoState where val : Nat

/-- A tiny graded VOA with weights 0,1,1. -/
def gradedDemo : VOAGraded DemoState :=
  { weights := #[0, 1, 1] }

/-- The truncated character of `gradedDemo` as a q-series. -/
def gradedChar : QSeries :=
  VOAGraded.charTrunc gradedDemo

/-- Package `gradedDemo` as a worldsheet CFT via `toCFT`. -/
def gradedCFT : WorldsheetCFT :=
  VOAGraded.toCFT gradedDemo "DemoVOA-graded" 0.5

/-!
Compile-only executable check (via #eval) tying together:
- the graded VOA truncated character,
- the induced CFT partition,
- and the VOA-style character field on a minimal VOA record.
-/

def voaDemo : HeytingLean.Physics.String.VOA DemoState :=
  { name := "DemoVOA"
  , vacuum := ⟨0⟩
  , character? := none
  , charTrunc? := some gradedChar }

-- A tiny compile-only print to exercise the link.
#eval
  let q := gradedChar
  let C := gradedCFT
  (q.coeffs, C.partitionZ)

end String
end Tests
end HeytingLean
