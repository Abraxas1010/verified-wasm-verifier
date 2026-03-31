import Lean.Data.Json
import HeytingLean.Tests.Integration.OrganicAlignmentStack

/-!
# `organic_alignment_stack_test`

Runtime harness for the compile-time integration module `HeytingLean.Tests.Integration.OrganicAlignmentStack`.

The real “test” is that the import succeeds under `--wfail`; this executable simply returns `0`
on the happy path.
-/

namespace HeytingLean.CLI.OrganicAlignmentStackTestMain

open Lean

def main (_argv : List String) : IO UInt32 := do
  let report :=
    Json.mkObj
      [ ("ok", Json.bool true)
      , ("note", Json.str "organic_alignment_stack_test: compile-time checks passed")
      ]
  IO.println report.compress
  pure 0

end HeytingLean.CLI.OrganicAlignmentStackTestMain

open HeytingLean.CLI.OrganicAlignmentStackTestMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.OrganicAlignmentStackTestMain.main args

