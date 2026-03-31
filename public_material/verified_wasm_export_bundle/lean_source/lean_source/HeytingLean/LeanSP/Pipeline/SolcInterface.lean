import HeytingLean.LeanSP.Lang.YulParser

/-!
# LeanSP.Pipeline.SolcInterface

Invoke `solc` to compile Solidity source to optimized Yul IR.
-/

namespace LeanSP.Pipeline

/-- Invoke `solc --ir-optimized` on a Solidity source file.
    Returns the raw Yul IR text (object syntax). -/
def compileSolToYul (solPath : System.FilePath) : IO String := do
  let output ← IO.Process.output {
    cmd := "solc"
    args := #["--ir-optimized", "--optimize", solPath.toString]
  }
  if output.exitCode != 0 then
    throw (IO.userError s!"solc failed (exit {output.exitCode}): {output.stderr}")
  pure output.stdout

/-- Strip solc preamble: find "object" keyword and return from there. -/
def stripSolcPreamble (raw : String) : Option String := do
  let chars := raw.data
  let objectChars := "object".data
  for i in [:chars.length] do
    if i + objectChars.length ≤ chars.length then
      let slice := chars.drop i |>.take objectChars.length
      if slice == objectChars then
        return String.mk (chars.drop i)
  none

/-- Compile and strip preamble. -/
def compileSolToYulClean (solPath : System.FilePath) : IO String := do
  let raw ← compileSolToYul solPath
  match stripSolcPreamble raw with
  | some clean => pure clean
  | none => throw (IO.userError "solc output does not contain an object declaration")

end LeanSP.Pipeline
