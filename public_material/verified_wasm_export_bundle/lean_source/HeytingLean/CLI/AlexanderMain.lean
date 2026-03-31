import Lean
import Lean.Data.Json
import HeytingLean.CLI.KnotCommon
import HeytingLean.Topology.Knot.Alexander
import HeytingLean.Topology.Knot.Burau
import HeytingLean.Topology.Knot.Braid

/-!
# Alexander polynomial demo CLI

Input JSON:
```json
{
  "version": "AlexanderInput.v1",
  "strands": 2,
  "generators": [{"i":0,"sign":"pos"}, {"i":0,"sign":"pos"}]
}
```
-/

namespace HeytingLean.CLI.AlexanderMain

open Lean
open Lean.Json
open HeytingLean.CLI.KnotCommon
open HeytingLean.Topology.Knot
open HeytingLean.Topology.Knot.Kauffman

private def defaultInput : Json :=
  Json.mkObj
    [ ("version", Json.str "AlexanderInput.v1")
    , ("strands", Json.num (2 : JsonNumber))
    , ("generators", Json.arr #[
        Json.mkObj [("i", Json.num (0 : JsonNumber)), ("sign", Json.str "pos")],
        Json.mkObj [("i", Json.num (0 : JsonNumber)), ("sign", Json.str "pos")]
      ])
    ]

def main (argv : List String) : IO UInt32 := do
  let args := KnotCommon.parseArgs argv
  let payloadE ← KnotCommon.readPayload args defaultInput
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
          match Parse.braidInputFromJson "AlexanderInput.v1" j with
          | .error e =>
              IO.eprintln s!"input error: {e}"
              pure 1
          | .ok (strands, gens) =>
              -- Prefer Burau-based Alexander for braid closures (computationally meaningful).
              match Burau.alexanderOfClosedBraid strands gens with
              | .error e =>
                  IO.eprintln s!"alexander error: {e}"
                  pure 1
              | .ok p =>
                  let out :=
                    Json.mkObj
                      [ ("version", Json.str "AlexanderOutput.v1")
                      , ("strands", Json.num (strands : JsonNumber))
                      , ("generators", Json.num (gens.length : JsonNumber))
                      , ("alexander", Render.laurentPolyToJson p)
                      ]
                  IO.println out.pretty
                  pure 0

end HeytingLean.CLI.AlexanderMain

open HeytingLean.CLI.AlexanderMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.AlexanderMain.main args
