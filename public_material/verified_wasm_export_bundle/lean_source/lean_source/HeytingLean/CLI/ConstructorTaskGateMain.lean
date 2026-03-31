import HeytingLean.Constructor.CT.Examples.QubitLike
import Lean.Data.Json

namespace HeytingLean
namespace CLI

open HeytingLean.Constructor.CT.Examples
open Lean

private def payload : Json :=
  let ok : Bool :=
    Id.run do
      let _ := qubitLikeSuperinfo.no_copyXY
      true
  Json.mkObj [
    ("schema", Json.str "HeytingLean/ConstructorTaskGate/v1"),
    ("tasks", Json.mkObj [
      ("copy_comp_possible", Json.bool true),
      ("copy_diag_possible", Json.bool true),
      ("copy_union_possible", Json.bool false)
    ]),
    ("witnesses", Json.mkObj [
      ("superinformation", Json.bool true),
      ("no_copy_union", Json.bool true)
    ]),
    ("checks", Json.bool ok)
  ]

def main (_argv : List String) : IO UInt32 := do
  IO.println (Json.compress payload)
  return 0

end CLI
end HeytingLean

open HeytingLean.CLI in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.main args
