import Lean
import Lean.Data.Json
import HeytingLean.LoF.ICC.GPUVerifierCorpus
import HeytingLean.LoF.ICC.WitnessFormat

open Lean

namespace HeytingLean.CLI.ICCWitnessExport

open HeytingLean.LoF.ICC

def witnessFuel : Nat := 8

def canonicalWitnessRows : Except String (List ICCCanonicalWitness) :=
  corpusWitnessRows.mapM (fun
    | (row, .ok witness) =>
        buildCanonicalWitness witnessFuel row.expectedAccepted row.sourceWitness witness
    | (row, .error err) =>
        .error s!"failed to build canonical witness for {row.sourceWitness.sourceId}: {err}")

def exportJson : Except String Json := do
  let rows ← canonicalWitnessRows
  pure (canonicalWitnessBundleJson rows)

def main (_args : List String) : IO UInt32 := do
  match exportJson with
  | .ok payload =>
      IO.println payload.compress
      pure 0
  | .error err =>
      IO.eprintln err
      pure 1

end HeytingLean.CLI.ICCWitnessExport

def main := HeytingLean.CLI.ICCWitnessExport.main
