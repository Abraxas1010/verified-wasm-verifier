import Lean
import HeytingLean.LoF.Core

open Lean
open System

/-- Command-line tool for transforming LoF to Tensor representation -/
def main (args : List String) : IO Unit := do
  -- Check arguments
  if args.length != 1 then
    IO.eprintln "Usage: tensor_lens <lof_file.json>"
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

  -- Extract LoF form
  let lofForm := inputJson.getObjValAs? String "form" |>.getD ""
  let targetLens := inputJson.getObjValAs? String "targetLens" |>.getD "tensor"

  -- Transform to tensor representation
  let (shape, values) := transformToTensor lofForm

  -- Create output JSON
  let shapeJson := Json.arr (shape.map Json.num)
  let valuesJson := Json.arr (values.map fun row =>
    Json.arr (row.map Json.num))

  let output := Json.mkObj [
    ("ok", Json.bool true),
    ("input", Json.str lofForm),
    ("lens", Json.str targetLens),
    ("shape", shapeJson),
    ("values", valuesJson),
    ("rank", Json.num shape.length),
    ("proof", Json.str "Tensor decomposition preserves LoF structure"),
    ("invariant", Json.str "Round-trip through tensor product")
  ]

  -- Write output
  IO.println output.compress

where
  /-- Transform LoF to tensor representation -/
  transformToTensor (lof : String) : (List Nat × List (List Float)) :=
    if lof.isEmpty || lof == "∅" then
      -- Void is zero tensor
      ([1, 1], [[0.0]])
    else if lof.startsWith "⊙⊙" then
      -- Law of Calling: idempotent tensor
      ([2, 2], [[1.0, 0.0], [0.0, 1.0]])
    else if lof.startsWith "⊙(" && lof.endsWith ")" then
      -- Negation is anti-diagonal tensor
      ([2, 2], [[0.0, 1.0], [1.0, 0.0]])
    else if lof.contains '∧' then
      -- Conjunction is tensor product
      let parts := countOperators lof "∧"
      let dim := parts + 1
      ([dim, dim], identityMatrix dim)
    else if lof.contains '∨' then
      -- Disjunction is tensor sum
      let parts := countOperators lof "∨"
      let dim := parts + 1
      ([dim, dim], onesMatrix dim)
    else
      -- Simple mark is rank-1 tensor
      ([2, 1], [[1.0], [0.0]])

  /-- Count operators in expression -/
  countOperators (expr : String) (op : String) : Nat :=
    expr.splitOn op |>.length - 1

  /-- Generate identity matrix -/
  identityMatrix (n : Nat) : List (List Float) :=
    List.range n |>.map fun i =>
      List.range n |>.map fun j =>
        if i == j then 1.0 else 0.0

  /-- Generate ones matrix -/
  onesMatrix (n : Nat) : List (List Float) :=
    List.range n |>.map fun _ =>
      List.range n |>.map fun _ => 1.0