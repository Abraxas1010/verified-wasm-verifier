import Lean
import Lean.Data.Json
import HeytingLean.Topology.Knot.Braid
import HeytingLean.Topology.Knot.LaurentPoly

/-!
# Knot CLI common utilities

Shared JSON parsing and rendering helpers for knot-related executables.
Keeps CLI input/output schemas consistent across invariants.
-/

namespace HeytingLean.CLI.KnotCommon

open Lean
open Lean.Json
open HeytingLean.Topology.Knot

namespace Parse

private def orErr {α} : Option α → String → Except String α
  | some a, _ => .ok a
  | none, msg => .error msg

def parseSign (s : String) : Except String Reidemeister.CurlKind :=
  if s = "pos" then
    .ok .pos
  else if s = "neg" then
    .ok .neg
  else
    .error s!"invalid sign '{s}' (expected pos|neg)"

def genFromJson (j : Json) : Except String Braid.Gen := do
  let obj ← j.getObj?
  let iJ ← orErr (obj.get? "i") "missing generator field 'i'"
  let sJ ← orErr (obj.get? "sign") "missing generator field 'sign'"
  let i ← iJ.getNat?
  let s ← sJ.getStr?
  let sign ← parseSign s
  pure { i, sign }

def braidInputFromJson (expectedVersion : String) (j : Json) : Except String (Nat × List Braid.Gen) := do
  let obj ← j.getObj?
  let version :=
    match obj.get? "version" with
    | some v =>
        match v.getStr? with
        | .ok s => s
        | .error _ => ""
    | none => ""
  if version != "" && version != expectedVersion then
    throw s!"unexpected version '{version}'"
  let strandsJ ← orErr (obj.get? "strands") "missing field 'strands'"
  let gensJ ← orErr (obj.get? "generators") "missing field 'generators'"
  let strands ← strandsJ.getNat?
  let gensArr ← gensJ.getArr?
  let mut gens : List Braid.Gen := []
  for g in gensArr do
    gens := gens.concat (← genFromJson g)
  pure (strands, gens)

end Parse

namespace Render

def laurentPolyToJson (p : LaurentPoly) : Json :=
  let terms :=
    p.toList.map (fun (e, c) =>
      Json.mkObj
        [("exp", Json.num (e : JsonNumber)), ("coeff", Json.num (c : JsonNumber))])
  Json.mkObj
    [ ("terms", Json.arr terms.toArray)
    , ("pretty", Json.str (toString p))
    ]

end Render

structure Args where
  useStdin : Bool := false
  inputFile : Option String := none
deriving Inhabited

def parseArgs (xs : List String) : Args :=
  let rec go (st : Args) (ys : List String) : Args :=
    match ys with
    | [] => st
    | "--stdin" :: ys' => go { st with useStdin := true } ys'
    | "--input" :: f :: ys' => go { st with inputFile := some f } ys'
    | _ :: ys' => go st ys'
  go ({} : Args) xs

def readPayload (args : Args) (defaultInput : Json) : IO (Except String String) := do
  try
    let payload ←
      match args.inputFile with
      | some f => IO.FS.readFile f
      | none =>
          if args.useStdin then
            (← IO.getStdin).readToEnd
          else
            pure (defaultInput.compress)
    pure (Except.ok payload)
  catch e =>
    pure (Except.error e.toString)

end HeytingLean.CLI.KnotCommon

