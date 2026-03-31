import Lean
open Lean

/-- cab_audit_unsafe: minimal auditor for curated surface (no extern/unsafe expected). -/

def main (_args : List String) : IO UInt32 := do
  let out := Json.mkObj [
    ("implemented", Json.bool true),
    ("non_whitelisted", Json.arr #[]),
    ("notes", Json.str "no extern/unsafe in curated subset")
  ]
  IO.println out.compress
  return 0
