import Lean
import Lean.Data.Json

namespace HeytingLean
namespace Payments
namespace CLI
namespace PMSnarkProve

open IO

private def findExe? (name : String) : IO (Option System.FilePath) := do
  match (← IO.getEnv "LOF_RUST_BIN_DIR") with
  | some dir =>
      let p := (System.FilePath.mk dir) / name
      if (← p.pathExists) then return some p else return none
  | none => return none

def main (args : List String) : IO UInt32 := do
  match args with
  | outDir :: opts =>
      let some exe ← findExe? "lof_prover"
        | do eprintln "lof_prover not found; set LOF_RUST_BIN_DIR"; return 2
      let pk := (System.FilePath.mk outDir) / "pk.bin"
      -- Adapt payments public.json to SNARK expected shape
      let payPub := (System.FilePath.mk outDir) / "public.json"
      let raw ← IO.FS.readFile payPub
      let j := match Lean.Json.parse raw with
        | .ok v => v
        | .error _ => Lean.Json.null
      let getStr (k : String) : String :=
        match j.getObjVal? k with
        | .ok (.str s) => s
        | _ => "0"
      let formC := getStr "policyCommitment"
      let initS := getStr "stateCommitment_pre"
      let finalS := getStr "stateCommitment_post"
      let lensS := "0"
      let snarkPub := Lean.Json.mkObj
        [ ("form_commitment", Lean.Json.str formC)
        , ("initial_state", Lean.Json.str initS)
        , ("final_state", Lean.Json.str finalS)
        , ("lens_selector", Lean.Json.str lensS) ]
      let pubPath := (System.FilePath.mk outDir) / "public_snark.json"
      IO.FS.writeFile pubPath (snarkPub.compress)
      let proof := (System.FilePath.mk outDir) / "proof.bin"
      let args := #[pk.toString, pubPath.toString, proof.toString]
      let out ← IO.Process.output { cmd := exe.toString, args := args ++ opts.toArray } 
      if out.exitCode == 0 then
        println out.stdout; return 0
      else
        eprintln out.stderr; return 1
  | _ =>
      eprintln "Usage: lake exe pm_snark_prove <outdir> [--witness path|--form path|--trace path]"; return 1

end PMSnarkProve
end CLI
end Payments
end HeytingLean

open HeytingLean.Payments.CLI.PMSnarkProve in
def main (args : List String) : IO UInt32 :=
  HeytingLean.Payments.CLI.PMSnarkProve.main args
