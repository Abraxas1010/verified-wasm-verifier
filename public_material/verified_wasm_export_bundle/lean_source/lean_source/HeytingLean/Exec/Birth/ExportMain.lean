import Lean
import Lean.Data.Json

/-
Birth Export CLI
================

This executable emits a tiny `BirthTPMInput.v1` JSON object encoding a
finite Birth / interior nucleus universe. It is designed to be
consumed by `tools/birth/birth_tpm.py`, which in turn constructs a TPM
and feeds it into the Emergence selector.

For now we expose a Bool‑interior example aligned with the
`BoolInterior` tests in `HeytingLean.Tests.AIT.BirthBridgeSmoke`:

  * models  : m0 = `false`, m1 = `true`,
  * birth   : [0, 1],
  * codeLen : [1, 2].

The numerical values are chosen to match the Lean proofs about
`boolIntReentryModelFamily` in the tests, but the CLI itself does not
recompute birth indices.
-/

namespace HeytingLean.Exec.Birth.ExportMain

open Lean
open Lean.Json

/-- States for the Bool interior example. -/
def boolStates : List String := ["m0", "m1"]

/-- Birth indices for the Bool interior example: `m0` has birth 0,
`m1` has birth 1. -/
def boolBirth : List Nat := [0, 1]

/-- Code lengths for the Bool interior example: `m0` has a code of
length 1, `m1` has length 2. -/
def boolCodeLen : List Nat := [1, 2]

/-- Encode the Bool interior example as a `BirthTPMInput.v1` JSON
object, ready for ingestion by `tools/birth/birth_tpm.py`. -/
def boolBirthInputJson : Json :=
  let statesJson :=
    Json.arr <| (boolStates.map Json.str).toArray
  let birthJson :=
    Json.arr <| (boolBirth.map (fun n : Nat => (n : Json))).toArray
  let codeLenJson :=
    Json.arr <| (boolCodeLen.map (fun n : Nat => (n : Json))).toArray
  Json.mkObj
    [ ("version", Json.str "BirthTPMInput.v1")
    , ("tau", Json.num (5 : Nat))
    , ("states", statesJson)
    , ("birth", birthJson)
    , ("codeLen", codeLenJson)
    ]

/-- CLI entry point: print the Bool interior BirthTPMInput to stdout. -/
def main (_args : List String) : IO UInt32 := do
  let j := boolBirthInputJson
  IO.println j.compress
  return 0

end HeytingLean.Exec.Birth.ExportMain

open HeytingLean.Exec.Birth.ExportMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.Exec.Birth.ExportMain.main args
