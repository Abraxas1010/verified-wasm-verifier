import Lean
import Lean.Data.Json
import HeytingLean.ProofState.Snapshot
import HeytingLean.LoF.ICCKernel.ProofState

namespace HeytingLean
namespace CLI
namespace ICCKernelProofStateMain

open HeytingLean.ProofState
open HeytingLean.LoF.ICCKernel

structure CliArgs where
  inPath : Option System.FilePath := none
  outPath : System.FilePath := "icc_kernel_proof_state.json"
  deriving Inhabited

private def usage : String :=
  String.intercalate "\n"
    [ "icc_kernel_proof_state - lower typed proof-state envelopes into ICC proof-node rows"
    , ""
    , "Usage:"
    , "  lake exe icc_kernel_proof_state -- --in proof_state_extract.json --out icc_kernel_proof_state.json"
    , ""
    , "Options:"
    , "  --in <path>"
    , "  --out <path>"
    ]

private partial def parseArgs (args : List String) (cfg : CliArgs := default) : Except String CliArgs := do
  match args with
  | [] => pure cfg
  | "--" :: rest => parseArgs rest cfg
  | "--help" :: _ => throw "help"
  | "--in" :: path :: rest => parseArgs rest { cfg with inPath := some path }
  | "--out" :: path :: rest => parseArgs rest { cfg with outPath := path }
  | bad :: _ => throw s!"unknown arg: {bad}"

def main (args : List String) : IO UInt32 := do
  let cfg ←
    match parseArgs args with
    | .ok cfg => pure cfg
    | .error "help" =>
        IO.println usage
        return 0
    | .error err =>
        IO.eprintln s!"error: {err}\n\n{usage}"
        return 1
  let some inPath := cfg.inPath
    | IO.eprintln s!"error: missing --in\n\n{usage}"
      return 1
  let envelope ← readExtractionEnvelopeFile inPath
  let row := ProofStateCorpusRow.ofEnvelope envelope
  IO.FS.writeFile cfg.outPath (Lean.toJson row).pretty
  return 0

end ICCKernelProofStateMain
end CLI
end HeytingLean

open HeytingLean.CLI.ICCKernelProofStateMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.ICCKernelProofStateMain.main args
