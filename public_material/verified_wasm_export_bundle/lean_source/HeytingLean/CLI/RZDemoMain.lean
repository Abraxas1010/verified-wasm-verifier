import Lean
import HeytingLean.Analysis.RZ

open Lean
open HeytingLean.Analysis.RZ
open HeytingLean.Analysis.RZ.Interval
open HeytingLean.Analysis.RZ.ExactReal

private def ratStr (q : ℚ) : String :=
  toString q

private def intervalJson (I : Interval) : Json :=
  let width : ℚ := I.hi - I.lo
  Json.mkObj
    [ ("lo", Json.str (ratStr I.lo))
    , ("hi", Json.str (ratStr I.hi))
    , ("width", Json.str (ratStr width))
    ]

private def exactRealSampleJson (x : ExactReal) (n : Nat) : Json :=
  let I := x.approx n
  Json.mkObj
    [ ("n", Json.num n)
    , ("interval", intervalJson I)
    , ("sample", Json.str (ratStr (sample x n)))
    , ("bound", Json.str (ratStr ((1 : ℚ) / pow2 n)))
    ]

/-! ## A tiny “headline” demo: `sqrt 2` bounds via bisection -/

private def sqrt2Step (I : Interval) : Interval :=
  let m := midpoint I
  if m * m ≤ (2 : ℚ) then
    { lo := m
      hi := I.hi
      lo_le_hi := (midpoint_mem I).2 }
  else
    { lo := I.lo
      hi := m
      lo_le_hi := (midpoint_mem I).1 }

private def sqrt2Interval : Nat → Interval
  | 0 => Interval.make (1 : ℚ) 2
  | Nat.succ n => sqrt2Step (sqrt2Interval n)

private def sqrt2SampleJson (n : Nat) : Json :=
  let I := sqrt2Interval n
  let lo2 : ℚ := I.lo * I.lo
  let hi2 : ℚ := I.hi * I.hi
  let ok : Bool := decide ((0 : ℚ) ≤ I.lo ∧ lo2 ≤ (2 : ℚ) ∧ (2 : ℚ) ≤ hi2)
  Json.mkObj
    [ ("n", Json.num n)
    , ("interval", intervalJson I)
    , ("lo2", Json.str (ratStr lo2))
    , ("hi2", Json.str (ratStr hi2))
    , ("invariant_ok", Json.bool ok)
    ]

def main (argv : List String) : IO Unit := do
  let _ := argv -- reserved for future flags

  let p : Nat := 8
  let q : ℚ := (1 : ℚ) / 3
  let qDown := roundDown p q
  let qUp := roundUp p q

  let I : Interval := Interval.make (1 : ℚ) 2
  let J : Interval := Interval.make (3 : ℚ) 4

  have hI : Interval.IsNonneg I := by
    simp [Interval.IsNonneg, I, Interval.make]
  have hJ : Interval.IsNonneg J := by
    simp [Interval.IsNonneg, J, Interval.make]

  let addIJ : Interval := Interval.add p I J
  let mulIJ : Interval := Interval.mulNonneg p I J hI hJ

  -- ExactReal demo: midpoint samples of a dyadic-rounded sum.
  let ex : ExactReal := ExactReal.ofRat (1 : ℚ)
  let ey : ExactReal := ExactReal.ofRat (2 : ℚ)
  let ez : ExactReal := ExactReal.add ex ey
  let sampleNs : List Nat := [0, 1, 2, 3, 4, 8, 12]
  let sampleArr : Array Json := sampleNs.map (exactRealSampleJson ez) |>.toArray
  let cauchyDiff : ℚ := |sample ez 0 - sample ez 10|

  let sqrtNs : List Nat := [0, 1, 2, 3, 4, 8, 12, 20]
  let sqrtArr : Array Json := sqrtNs.map sqrt2SampleJson |>.toArray

  let payload : Json :=
    Json.mkObj
      [ ("precisionPow", Json.num p)
      , ("q", Json.str (ratStr q))
      , ("roundDown", Json.str (ratStr qDown))
      , ("roundUp", Json.str (ratStr qUp))
      , ("I", intervalJson I)
      , ("J", intervalJson J)
      , ("I_plus_J", intervalJson addIJ)
      , ("I_mul_J_nonneg", intervalJson mulIJ)
      , ("exactRealDemo",
          Json.mkObj
            [ ("expr", Json.str "1 + 2")
            , ("samples", Json.arr sampleArr)
            , ("cauchyCheck_m0_n10_absDiff", Json.str (ratStr cauchyDiff))
            , ("cauchyBound_m0", Json.str (ratStr ((1 : ℚ) / pow2 0)))
            ])
      , ("sqrt2Bisection",
          Json.mkObj
            [ ("expr", Json.str "sqrt(2)")
            , ("intervals", Json.arr sqrtArr)
            ])
      ]
  IO.println payload.pretty
