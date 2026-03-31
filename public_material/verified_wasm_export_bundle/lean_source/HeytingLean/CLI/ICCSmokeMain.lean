import Lean
import Lean.Data.Json
import HeytingLean.LoF.ICC.Reduction
import HeytingLean.LoF.ICC.Encodings
import HeytingLean.LoF.ICC.Workloads
import HeytingLean.Bridge.INet.ICCLowering

open Lean

namespace HeytingLean.CLI.ICCSmokeMain

open HeytingLean.LoF.ICC
open HeytingLean.Bridge.INet.ICC

def main (_args : List String) : IO UInt32 := do
  let reduced := reduceFuel 8 sampleTerm
  let net := lower sampleTerm
  let payload :=
    Json.mkObj
      [ ("sample_size", Json.num sampleTerm.size)
      , ("reduced_size", Json.num reduced.size)
      , ("y_free_after_8", Json.bool (checkYFree 8 sampleTerm))
      , ("net", emitJson net)
      ]
  IO.println (Json.compress payload)
  pure 0

end HeytingLean.CLI.ICCSmokeMain

def main := HeytingLean.CLI.ICCSmokeMain.main
