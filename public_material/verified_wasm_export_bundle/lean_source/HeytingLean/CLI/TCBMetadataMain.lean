import HeytingLean.TCB.Metadata

/-- Path (from the `lean` directory) where the metadata JSON is written. -/
def outputPath : System.FilePath :=
  System.FilePath.mk ".." / "artifacts" / "tcb_metadata.json"

/-- CLI entry point that dumps trusted computing base metadata as JSON. -/
def main : IO UInt32 := do
  let snapshot ← HeytingLean.TCB.current
  let json := HeytingLean.TCB.Metadata.toPrettyJson snapshot
  let some dir := outputPath.parent
    | throw <|
        IO.userError s!"could not compute parent directory for {outputPath}"
  IO.FS.createDirAll dir
  IO.FS.writeFile outputPath json
  IO.println s!"wrote {outputPath}"
  pure 0
