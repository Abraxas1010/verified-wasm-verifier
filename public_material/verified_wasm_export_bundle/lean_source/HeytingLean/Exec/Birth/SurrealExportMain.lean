import Lean
import Lean.Data.Json

/-
Surreal Birth Export CLI
========================

This executable emits a `BirthTPMInput.v1` JSON object encoding a
finite surreal interior‑nucleus universe. It is intended to align with
the `SurrealInterior` example in
`HeytingLean.Tests.AIT.BirthBridgeSmoke`:

  * states   : s0 = `S_good`, s1 = `S_bad`,
  * birth    : [0, 1]  (interior birthdays under `surrealIntReentry`),
  * codeLen  : [1, 2]  (code lengths from `surrealModelFamily`).

The birth and code length values are justified by the Lean proofs in
the tests; this CLI simply serialises them for use by
`tools/birth/birth_tpm.py` and the Emergence selector.
-/
namespace HeytingLean.Exec.Birth.SurrealExportMain

open Lean
open Lean.Json

/-- States for the surreal interior example. -/
def surrealStates : List String := ["S_good", "S_bad"]

/-- Birth indices for the surreal interior example: `S_good` has
birth 0, `S_bad` has birth 1. -/
def surrealBirth : List Nat := [0, 1]

/-- Code lengths for the surreal interior example: models interpreting
to `S_good` and `S_bad` have code lengths 1 and 2 respectively in the
finite `surrealModelFamily`. -/
def surrealCodeLen : List Nat := [1, 2]

/-- Encode the surreal interior example as a `BirthTPMInput.v1` JSON
object, ready for ingestion by `tools/birth/birth_tpm.py`. -/
def surrealBirthInputJson : Json :=
  let statesJson :=
    Json.arr <| (surrealStates.map Json.str).toArray
  let birthJson :=
    Json.arr <| (surrealBirth.map (fun n : Nat => (n : Json))).toArray
  let codeLenJson :=
    Json.arr <| (surrealCodeLen.map (fun n : Nat => (n : Json))).toArray
  Json.mkObj
    [ ("version", Json.str "BirthTPMInput.v1")
    , ("tau", Json.num (5 : Nat))
    , ("states", statesJson)
    , ("birth", birthJson)
    , ("codeLen", codeLenJson)
    ]

/-- CLI entry point: print the surreal interior BirthTPMInput to stdout. -/
def main (_args : List String) : IO UInt32 := do
  let j := surrealBirthInputJson
  IO.println j.compress
  return 0

end HeytingLean.Exec.Birth.SurrealExportMain

open HeytingLean.Exec.Birth.SurrealExportMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.Exec.Birth.SurrealExportMain.main args
