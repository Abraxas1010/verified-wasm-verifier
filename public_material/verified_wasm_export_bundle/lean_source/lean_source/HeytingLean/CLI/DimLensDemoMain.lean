import Lean

/-
Executable demo for finite dimensional lenses and their SKY / multiway
correspondence (static finite snapshot).

This CLI presents a small JSON payload describing the finite Boolean
and `Set (Fin 2)` state spaces together with their SKY codes and
two-branch multiway successors.  The structure of the data mirrors the
HoTT / SKY / Dimensional layer, but the payload is computed from a
finite, explicit table so that it is fully executable via the C
backend without relying on noncomputable constructions.
-/

open Lean

structure LensStateSummary where
  omegaR     : String
  code       : String
  successors : List String

private def lensStateToJson (s : LensStateSummary) : Json :=
  let succArr : Array Json := s.successors.map Json.str |>.toArray
  Json.mkObj
    [ ("omegaR",    Json.str s.omegaR)
    , ("code",      Json.str s.code)
    , ("successors", Json.arr succArr) ]

/-- Static summary for the Boolean dimensional lens. -/
def boolDimLensSummary : Json :=
  let states : List LensStateSummary :=
    [ { omegaR := "false", code := "K", successors := ["false"] }
    , { omegaR := "true",  code := "S", successors := ["true"] } ]
  let entries : Array Json :=
    states.map lensStateToJson |>.toArray
  Json.mkObj
    [ ("lens",   Json.str "bool")
    , ("states", Json.arr entries) ]

/-- Static summary for the `Set (Fin 2)` dimensional lens. -/
def fin2DimLensSummary : Json :=
  let states : List LensStateSummary :=
    [ { omegaR := "∅",     code := "K·S", successors := ["∅"] }
    , { omegaR := "{0}",   code := "K",   successors := ["{0}"] }
    , { omegaR := "{1}",   code := "Y",   successors := ["{1}"] }
    , { omegaR := "{0,1}", code := "S",   successors := ["{0,1}"] } ]
  let entries : Array Json :=
    states.map lensStateToJson |>.toArray
  Json.mkObj
    [ ("lens",   Json.str "fin2")
    , ("states", Json.arr entries) ]

/-- JSON payload combining all dimensional lenses exposed by this demo. -/
def payloadJson : Json :=
  Json.mkObj
    [ ("bool", boolDimLensSummary)
    , ("fin2", fin2DimLensSummary) ]

/-- Top-level CLI entry point for `dimlens_demo`. -/
def main (argv : List String) : IO Unit := do
  let _ := argv -- currently unused; reserved for future flags
  IO.println payloadJson.pretty

