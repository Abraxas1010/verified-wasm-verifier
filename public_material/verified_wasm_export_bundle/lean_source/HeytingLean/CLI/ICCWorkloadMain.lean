import Lean
import Lean.Data.Json
import HeytingLean.LoF.ICC.Workloads

open Lean

namespace HeytingLean.CLI.ICCWorkloadMain

open HeytingLean.LoF.ICC

def main (_args : List String) : IO UInt32 := do
  IO.println (Json.compress (workloadReportJson 8))
  pure 0

end HeytingLean.CLI.ICCWorkloadMain

def main := HeytingLean.CLI.ICCWorkloadMain.main
