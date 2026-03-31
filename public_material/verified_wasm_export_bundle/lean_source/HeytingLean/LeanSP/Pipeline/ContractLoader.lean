import HeytingLean.LeanSP.Pipeline.SolcInterface

/-!
# LeanSP.Pipeline.ContractLoader

End-to-end pipeline: `.sol` file → solc → Yul text → YulUnit.
-/

namespace LeanSP.Pipeline

/-- Load a Solidity contract: compile to Yul via solc, then parse to YulUnit. -/
def loadContract (solPath : System.FilePath) : IO Yul.YulUnit := do
  let yulText ← compileSolToYulClean solPath
  match parseYulText yulText with
  | .ok unit => pure unit
  | .error msg => throw (IO.userError s!"Yul parse failed: {msg}")

end LeanSP.Pipeline
