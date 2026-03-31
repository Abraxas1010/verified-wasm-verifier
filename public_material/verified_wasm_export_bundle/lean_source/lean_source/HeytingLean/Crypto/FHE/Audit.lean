import Lean

open IO

private def runBash (cmd : String) : IO IO.Process.Output :=
  IO.Process.output { cmd := "/bin/bash", args := #["-lc", cmd], cwd := none }

def main (args : List String) : IO UInt32 := do
  let distArg := match args with | d :: _ => d | _ => "dist/apmt_fhe"
  let dist := if distArg.startsWith "../" then distArg.drop 3 else distArg
  let cmd := s!"if [ -x ./scripts/fhe_audit.sh ]; then ./scripts/fhe_audit.sh '{dist}'; elif [ -x ../scripts/fhe_audit.sh ]; then (cd .. && ./scripts/fhe_audit.sh '{dist}'); elif [ -x ../../scripts/fhe_audit.sh ]; then (cd ../.. && ./scripts/fhe_audit.sh '{dist}'); else echo 'fhe_audit.sh not found' >&2; exit 1; fi"
  let output? : Option IO.Process.Output ←
    try
      some <$> runBash cmd
    catch e =>
      IO.eprintln s!"apmt_fhe_audit: failed to run bash: {e.toString}"
      pure none
  let output := output?.getD { exitCode := 1, stdout := "", stderr := "" }
  if output.exitCode == 0 then
    let out := output.stdout.trim
    if !out.isEmpty then
      IO.println out
    return (0 : UInt32)
  else
    let err := output.stderr.trim
    if err.isEmpty then
      IO.eprintln s!"apmt_fhe_audit: audit failed (exit={output.exitCode})"
    else
      IO.eprintln err
    return (1 : UInt32)
