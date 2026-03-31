import Lean

open Lean

/-- Simple Laws of Form encoder for demonstration -/
def main (args : List String) : IO Unit := do
  -- Read input from stdin or first argument
  let input ← if args.isEmpty then
    IO.getStdin
  else
    pure args.head!

  -- Simple LoF transformation
  let lofForm := transformToLoF input
  let boolForm := toBool lofForm

  -- Create JSON output
  let output := Json.mkObj [
    ("ok", Json.bool true),
    ("input", Json.str input),
    ("output", Json.mkObj [
      ("lof", Json.str lofForm),
      ("boolean", Json.str boolForm),
      ("nucleus", Json.str s!"j({lofForm})")
    ])
  ]

  IO.println output.compress

where
  transformToLoF (s : String) : String :=
    if s.isEmpty then "∅"
    else if s.startsWith "(" then s!"⊙{s}"
    else s!"⊙({s})"

  toBool (s : String) : String :=
    if s == "∅" then "false"
    else if s.startsWith "⊙⊙" then toBool (s.drop 2)
    else if s.startsWith "⊙" then s!"¬{s.drop 1}"
    else "true"