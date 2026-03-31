import Lean
import Lean.Data.Json
import HeytingLean.PDE.Examples.Heat1D

open Lean
open HeytingLean.PDE.Examples

namespace HeytingLean.CLI

private def jsonOfStringList (items : List String) : Json :=
  Json.arr <| (items.map Json.str).toArray

def run (_argv : List String) : IO UInt32 := do
  let payload := Json.mkObj
    [ ("id", Json.str heat1DSpec.id)
    , ("smtlib2", Json.str heat1DSMTQuery)
    , ("tptp_fof", jsonOfStringList heat1DArtifact.toTPTPFOF)
    , ("tags", jsonOfStringList heat1DArtifact.tags)
    ]
  IO.println (toString payload)
  pure 0

end HeytingLean.CLI

def main (argv : List String) : IO UInt32 :=
  HeytingLean.CLI.run argv
