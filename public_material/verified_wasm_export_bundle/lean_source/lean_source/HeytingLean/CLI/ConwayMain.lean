import Lean
import Lean.Data.Json
import HeytingLean.CLI.KnotCommon
import HeytingLean.Topology.Knot.Conway
import HeytingLean.Topology.Knot.Braid

/-!
# Conway polynomial demo CLI

Input JSON:
```json
{
  "version": "ConwayInput.v1",
  "strands": 2,
  "generators": [{"i":0,"sign":"pos"}, {"i":0,"sign":"pos"}]
}
```
-/

namespace HeytingLean.CLI.ConwayMain

open Lean
open Lean.Json
open HeytingLean.CLI.KnotCommon
open HeytingLean.Topology.Knot
open HeytingLean.Topology.Knot.Kauffman

private def defaultInput : Json :=
  Json.mkObj
    [ ("version", Json.str "ConwayInput.v1")
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
          match Parse.braidInputFromJson "ConwayInput.v1" j with
          | .error e =>
              IO.eprintln s!"input error: {e}"
              pure 1
          | .ok (strands, gens) =>
              match Braid.closureSignedPDGraph strands gens with
              | .error e =>
                  IO.eprintln s!"diagram error: {e}"
                  pure 1
              | .ok s =>
                  match SignedPDGraph.conway s with
                  | .error e =>
                      IO.eprintln s!"conway error: {e}"
                      pure 1
                  | .ok p =>
                      let out :=
                        Json.mkObj
                          [ ("version", Json.str "ConwayOutput.v1")
                          , ("strands", Json.num (strands : JsonNumber))
                          , ("generators", Json.num (gens.length : JsonNumber))
                          , ("conway", Render.laurentPolyToJson p)
                          ]
                      IO.println out.pretty
                      pure 0

end HeytingLean.CLI.ConwayMain

open HeytingLean.CLI.ConwayMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.ConwayMain.main args
