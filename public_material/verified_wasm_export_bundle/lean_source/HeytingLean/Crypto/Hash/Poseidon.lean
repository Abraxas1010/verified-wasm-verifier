import Lean
import Lean.Data.Json
import HeytingLean.Crypto.Commit

/-!
Poseidon commitment API boundary (compatibility layer).

- Domain separation follows `POSEIDON:<TAG>` where `<TAG>` ∈ {FORM, TENSOR, GRAPH, CLIFFORD}.
- Current implementation reuses `commitString` so that commitments are stable
  across Lean/Rust by treating the textual commitment as the public field element
  (Rust maps the UTF‑8 bytes of the commitment string to a field element).
- Future: replace with a real Poseidon hash (fixed params) and update Rust to
  use the same parameters, keeping JSON format stable.
-/

namespace HeytingLean
namespace Crypto
namespace Hash

def poseidonCommit (domain : String) (payload : String) : String :=
  HeytingLean.Crypto.commitString (s!"POSEIDON:{domain}") payload

def commitForm (payload : String) : String := poseidonCommit "FORM" payload
def commitTensor (payload : String) : String := poseidonCommit "TENSOR" payload
def commitGraph (payload : String) : String := poseidonCommit "GRAPH" payload
def commitClifford (payload : String) : String := poseidonCommit "CLIFFORD" payload

/-! Gated IO path to compute Poseidon digests via external binary when available.
    Controlled by `LOF_COMMIT_MODE` env var:
    - "poseidon": try external `lof_poseidon`; on error, fallback to string mode
    - default/other: string mode (commitString)
    The external tool is discovered via `LOF_RUST_BIN_DIR/lof_poseidon`.
-/

private def getCommitMode : IO String := do
  return (← IO.getEnv "LOF_COMMIT_MODE").getD "string"

private def poseidonExe? : IO (Option System.FilePath) := do
  match (← IO.getEnv "LOF_RUST_BIN_DIR") with
  | some dir =>
      let p := (System.FilePath.mk dir) / "lof_poseidon"
      try
        if (← p.pathExists) then return some p else return none
      catch _ => return none
  | none => return none

private def commitPoseidonIO (tag : String) (payload : String) : IO (Option String) := do
  match (← poseidonExe?) with
  | none => return none
  | some exe =>
      let cwd ← IO.currentDir
      let outDir := cwd / System.FilePath.mk ".tmp/poseidon"
      (do IO.FS.createDirAll outDir) |> (fun _ => pure ())
      let inPath := outDir / "payload.txt"
      IO.FS.writeFile inPath payload
      let out ← IO.Process.output { cmd := exe.toString, args := #[tag, inPath.toString] }
      if out.exitCode != 0 then
        return none
      else
        match Lean.Json.parse out.stdout with
        | .ok j =>
            match j.getObjVal? "hex" with
            | .ok (.str hex) => return some hex
            | _ => return none
        | .error _ => return none

def commitFormIO (payload : String) : IO String := do
  let mode ← getCommitMode
  if mode == "poseidon" then
    match (← commitPoseidonIO "FORM" payload) with
    | some hex => return hex
    | none => return commitForm payload
  else
    return commitForm payload

def commitTensorIO (payload : String) : IO String := do
  let mode ← getCommitMode
  if mode == "poseidon" then
    match (← commitPoseidonIO "TENSOR" payload) with
    | some hex => return hex
    | none => return commitTensor payload
  else
    return commitTensor payload

def commitGraphIO (payload : String) : IO String := do
  let mode ← getCommitMode
  if mode == "poseidon" then
    match (← commitPoseidonIO "GRAPH" payload) with
    | some hex => return hex
    | none => return commitGraph payload
  else
    return commitGraph payload

def commitCliffordIO (payload : String) : IO String := do
  let mode ← getCommitMode
  if mode == "poseidon" then
    match (← commitPoseidonIO "CLIFFORD" payload) with
    | some hex => return hex
    | none => return commitClifford payload
  else
    return commitClifford payload

end Hash
end Crypto
end HeytingLean
