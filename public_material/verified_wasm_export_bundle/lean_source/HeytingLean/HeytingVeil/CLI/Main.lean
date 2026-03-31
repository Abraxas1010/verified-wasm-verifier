/-
Copyright (c) 2026 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

import Init

/-!
# Unified HeytingVeil CLI wrapper

Delegates subcommand execution to `scripts/heytingveil_cli.py` while providing
a stable `lake exe heytingveil` binary entry point.
-/

namespace HeytingLean
namespace HeytingVeil
namespace CLI

private def findScriptPath : IO (Option String) := do
  let candidates : List System.FilePath :=
    [ System.FilePath.mk "scripts/heytingveil_cli.py"
    , System.FilePath.mk "../scripts/heytingveil_cli.py"
    , System.FilePath.mk "../../scripts/heytingveil_cli.py"
    ]
  for path in candidates do
    if (← path.pathExists) then
      return some path.toString
  return none

def run (argv : List String) : IO UInt32 := do
  let some scriptPath ← findScriptPath
    | do
      IO.eprintln "heytingveil: unable to locate scripts/heytingveil_cli.py"
      return 2
  try
    let proc ← IO.Process.output
      { cmd := "python3"
      , args := #[scriptPath] ++ argv.toArray
      }
    if !proc.stdout.isEmpty then
      IO.print proc.stdout
    if !proc.stderr.isEmpty then
      IO.eprint proc.stderr
    return proc.exitCode
  catch e =>
    IO.eprintln s!"heytingveil wrapper failure: {e.toString}"
    return 2

end CLI
end HeytingVeil
end HeytingLean

def main (argv : List String) : IO UInt32 := do
  HeytingLean.HeytingVeil.CLI.run argv
