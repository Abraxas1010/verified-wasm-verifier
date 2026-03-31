import Lean
import Lean.Data.Json
import HeytingLean.Topology.Knot.Bracket

/-!
# Kauffman bracket demo CLI

Input JSON (from `--stdin` or `--input <file>`):
```json
{
  "version": "KauffmanBracketInput.v1",
  "freeLoops": 1,
  "crossings": [[0,1,0,1]]
}
```

Output JSON:
- `bracket.terms`: list of `{exp, coeff}` (Laurent polynomial `∑ coeff · A^exp`)
- `bracket.pretty`: human-readable string

No args: prints a tiny default example and exits 0.
-/

namespace HeytingLean.CLI.KauffmanBracketMain

open Lean
open Lean.Json
open HeytingLean.Topology.Knot

namespace Parse

private def orErr {α} : Option α → String → Except String α
  | some a, _ => .ok a
  | none, msg => .error msg

private def nat4FromArr (arr : Array Json) : Except String (Nat × Nat × Nat × Nat) := do
  match arr.toList with
  | ja :: jb :: jc :: jd :: [] =>
      let a ← ja.getNat?
      let b ← jb.getNat?
      let c ← jc.getNat?
      let d ← jd.getNat?
      pure (a, b, c, d)
  | _ =>
      .error "expected crossing as array [a,b,c,d]"

def crossingFromJson (j : Json) : Except String Crossing := do
  let arr ← j.getArr?
  let (a, b, c, d) ← nat4FromArr arr
  pure { a, b, c, d }

private def crossingsFromJsonArray (arr : Array Json) : Except String (Array Crossing) := do
  let mut out : Array Crossing := #[]
  for j in arr do
    let c ← crossingFromJson j
    out := out.push c
  pure out

def diagramFromJson (j : Json) : Except String PlanarDiagram := do
  let obj ← j.getObj?
  let version :=
    match obj.get? "version" with
    | some v =>
        match v.getStr? with
        | .ok s => s
        | .error _ => ""
    | none => ""
  if version != "" && version != "KauffmanBracketInput.v1" then
    throw s!"unexpected version '{version}'"

  let freeLoops :=
    match obj.get? "freeLoops" with
    | some v =>
        match v.getNat? with
        | .ok n => n
        | .error _ => 0
    | none => 0

  let crossingsJ ← orErr (obj.get? "crossings") "missing field 'crossings'"
  let crossingsArr ← crossingsJ.getArr?
  let crossings ← crossingsFromJsonArray crossingsArr
  pure { freeLoops, crossings }

end Parse

namespace Render

def polyToJson (p : LaurentPoly) : Json :=
  let terms :=
    p.toList.map (fun (e, c) =>
      Json.mkObj [("exp", Json.num (e : JsonNumber)), ("coeff", Json.num (c : JsonNumber))])
  Json.mkObj
    [ ("terms", Json.arr terms.toArray)
    , ("pretty", Json.str (toString p))
    ]

end Render

structure Args where
  useStdin : Bool := false
  inputFile : Option String := none
deriving Inhabited

private def parseArgs (xs : List String) : Args :=
  let rec go (st : Args) (ys : List String) : Args :=
    match ys with
    | [] => st
    | "--stdin" :: ys' => go { st with useStdin := true } ys'
    | "--input" :: f :: ys' => go { st with inputFile := some f } ys'
    | _ :: ys' => go st ys'
  go ({} : Args) xs

private def defaultInput : Json :=
  Json.mkObj
    [ ("version", Json.str "KauffmanBracketInput.v1")
    , ("freeLoops", Json.num (1 : JsonNumber))
    , ("crossings", Json.arr #[])
    ]

def main (argv : List String) : IO UInt32 := do
  let args := parseArgs argv
  let payloadE ←
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
  match payloadE with
  | .error e =>
      IO.eprintln s!"input error: {e}"
      pure 1
  | .ok payload =>
      match Json.parse payload with
      | .error e =>
          IO.eprintln s!"json error: {e}"
          pure 1
      | .ok j =>
          match Parse.diagramFromJson j with
          | .error e =>
              IO.eprintln s!"input error: {e}"
              pure 1
          | .ok dgm =>
              match Kauffman.bracket dgm with
              | .error e =>
                  IO.eprintln s!"bracket error: {e}"
                  pure 1
              | .ok poly =>
                  let out :=
                    Json.mkObj
                      [ ("version", Json.str "KauffmanBracketOutput.v1")
                      , ("freeLoops", Json.num (dgm.freeLoops : JsonNumber))
                      , ("crossings", Json.num (dgm.crossings.size : JsonNumber))
                      , ("bracket", Render.polyToJson poly)
                      ]
                  IO.println out.pretty
                  pure 0

end HeytingLean.CLI.KauffmanBracketMain

open HeytingLean.CLI.KauffmanBracketMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.KauffmanBracketMain.main args
