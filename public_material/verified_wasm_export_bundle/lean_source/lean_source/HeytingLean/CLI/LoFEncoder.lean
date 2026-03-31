import Lean
import HeytingLean.LoF.Core
import HeytingLean.LoF.PrimaryAlgebra

open Lean
open System

/-- Command-line tool for encoding distinctions into Laws of Form representation -/
def main (args : List String) : IO Unit := do
  -- Check arguments
  if args.length != 1 then
    IO.eprintln "Usage: lof_encoder <distinction_file.json>"
    IO.Process.exit 1

  let inputFile := args.head!

  -- Read input file
  let inputContent ← IO.FS.readFile inputFile

  -- Parse JSON input
  let inputJson : Json ← match Json.parse inputContent with
    | Except.ok json => pure json
    | Except.error e => do
      IO.eprintln s!"Failed to parse JSON: {e}"
      IO.Process.exit 1

  -- Extract distinction pattern
  let distinction := inputJson.getObjValAs? String "input" |>.toOption.getD ""
  let distType := inputJson.getObjValAs? String "type" |>.toOption.getD "mark_void"

  -- Process distinction into LoF representation
  let lofForm := processDistinction distinction
  let booleanForm := toBooleanAlgebra lofForm
  let nucleusForm := applyNucleus lofForm

  -- Create output JSON
  let output := Json.mkObj [
    ("ok", Json.bool true),
    ("input", Json.str distinction),
    ("lof", Json.str lofForm),
    ("boolean", Json.str booleanForm),
    ("nucleus", Json.str nucleusForm),
    ("type", Json.str distType)
  ]

  -- Write output
  IO.println output.compress

where
  /-- Process a distinction pattern into LoF representation -/
  processDistinction (d : String) : String :=
    if d.isEmpty then
      "∅"  -- Void
    else if d.startsWith "(" && d.endsWith ")" then
      s!"⊙{d}"  -- Crossed distinction
    else if d.contains '(' then
      -- Complex pattern with nested distinctions
      let parts := d.split (· == '(')
      s!"⊙({String.intercalate "⊙" parts})"
    else
      s!"⊙{d}"  -- Simple mark

  /-- Convert LoF to Boolean algebra -/
  toBooleanAlgebra (lof : String) : String :=
    if lof == "∅" then
      "false"
    else if lof.startsWith "⊙⊙" then
      -- Law of Calling: ⊙⊙ = ⊙
      toBooleanAlgebra (lof.drop 1)
    else if lof.startsWith "⊙(" then
      -- Negation
      s!"¬{lof.drop 2 |>.dropRight 1}"
    else if lof.startsWith "⊙" then
      -- Simple mark
      lof.drop 1
    else
      lof
  termination_by lof.length

  /-- Apply nucleus operator for Heyting algebra -/
  applyNucleus (lof : String) : String :=
    if lof == "∅" then
      "j(void)"
    else if lof.startsWith "⊙" then
      let content := lof.drop 1
      s!"j({content})"
    else
      s!"j({lof})"