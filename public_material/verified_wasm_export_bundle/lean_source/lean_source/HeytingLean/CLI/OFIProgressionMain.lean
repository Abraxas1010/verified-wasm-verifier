import HeytingLean.CLI.OFIProgression

noncomputable def main (argv : List String) : IO Unit := do
  let code ← HeytingLean.CLI.OFIProgression.runWithArgs argv
  if code ≠ 0 then
    IO.Process.exit code.toUInt8
