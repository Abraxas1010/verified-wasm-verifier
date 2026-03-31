import HeytingLean.CLI.OFIProgression

/-- CLI entrypoint that runs the existing runner while keeping `IO Unit` type. -/
noncomputable def _root_.main (argv : List String) : IO Unit := do
  let code ← HeytingLean.CLI.OFIProgression.runWithArgs argv
  if code ≠ 0 then
    IO.Process.exit code.toUInt8
