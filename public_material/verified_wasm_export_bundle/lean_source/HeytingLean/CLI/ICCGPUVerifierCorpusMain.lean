import Lean
import Lean.Data.Json
import HeytingLean.LoF.ICC.GPUVerifierCorpus

open Lean

namespace HeytingLean.CLI.ICCGPUVerifierCorpusMain

open HeytingLean.LoF.ICC

def main (_args : List String) : IO UInt32 := do
  IO.println corpusReportJson.compress
  pure 0

end HeytingLean.CLI.ICCGPUVerifierCorpusMain

def main := HeytingLean.CLI.ICCGPUVerifierCorpusMain.main
