import Lean

namespace HeytingLean
namespace Payments
namespace CLI
namespace PMSnarkSetup

open IO

private def findExe? (name : String) : IO (Option System.FilePath) := do
  match (← IO.getEnv "LOF_RUST_BIN_DIR") with
  | some dir =>
      let p := (System.FilePath.mk dir) / name
      if (← p.pathExists) then return some p else return none
  | none => return none

def main (args : List String) : IO UInt32 := do
  match args with
  | outDir :: _ =>
      let some exe ← findExe? "lof_setup"
        | do eprintln "lof_setup not found; set LOF_RUST_BIN_DIR"; return 2
      let pk := (System.FilePath.mk outDir) / "pk.bin"
      let vk := (System.FilePath.mk outDir) / "vk.bin"
      let out ← IO.Process.output { cmd := exe.toString, args := #[pk.toString, vk.toString] }
      if out.exitCode == 0 then
        println out.stdout; return 0
      else
        eprintln out.stderr; return 1
  | _ =>
      eprintln "Usage: lake exe pm_snark_setup <outdir>"; return 1

end PMSnarkSetup
end CLI
end Payments
end HeytingLean

open HeytingLean.Payments.CLI.PMSnarkSetup in
def main (args : List String) : IO UInt32 :=
  HeytingLean.Payments.CLI.PMSnarkSetup.main args

