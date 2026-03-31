import Lean
import Lean.Data.Json
import HeytingLean.Crypto.Commit
import HeytingLean.Payments.Types

/-!
Commitment helpers for Payments using Poseidon boundary via external binary when
requested; default fallback uses string-tag commitments for stability.

Env controls:
- LOF_COMMIT_MODE=poseidon → try external binary `lof_poseidon`
- LOF_RUST_BIN_DIR=/path/to/bin contains `lof_poseidon`
- Tags used: POLICY, STATE, NULLIFIER
-/ 

namespace HeytingLean
namespace Payments
namespace Commit

open Lean
open Payments
open Payments.JsonCodec

def commitPolicy (p : Policy) : String :=
  let payload := (policyToCanonicalJson p).compress
  HeytingLean.Crypto.commitString "POSEIDON:POLICY" payload

def commitState (s : State) : String :=
  let payload := (stateToCanonicalJson s).compress
  HeytingLean.Crypto.commitString "POSEIDON:STATE" payload

def computeNullifier (hashedId : String) (stateCommitPre : String) (epoch : Nat) : String :=
  let payload := s!"{hashedId}:{stateCommitPre}:{epoch}"
  HeytingLean.Crypto.commitString "POSEIDON:NULLIFIER" payload

/- External commit helpers (IO): replicate the gated call used elsewhere. -/
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
      let outDir := cwd / System.FilePath.mk ".tmp/pay_poseidon"
      let _ ← IO.FS.createDirAll outDir
      let inPath := outDir / s!"{tag}_payload.txt"
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

def commitPolicyIO (p : Policy) : IO String := do
  let mode ← getCommitMode
  let payload := (policyToCanonicalJson p).compress
  if mode == "poseidon" then
    match (← commitPoseidonIO "POLICY" payload) with
    | some hex => return hex
    | none => return commitPolicy p
  else
    return commitPolicy p

def commitStateIO (s : State) : IO String := do
  let mode ← getCommitMode
  let payload := (stateToCanonicalJson s).compress
  if mode == "poseidon" then
    match (← commitPoseidonIO "STATE" payload) with
    | some hex => return hex
    | none => return commitState s
  else
    return commitState s

def computeNullifierIO (hashedId : String) (stateCommitPre : String) (epoch : Nat) : IO String := do
  let mode ← getCommitMode
  let payload := s!"{hashedId}:{stateCommitPre}:{epoch}"
  if mode == "poseidon" then
    match (← commitPoseidonIO "NULLIFIER" payload) with
    | some hex => return hex
    | none => return computeNullifier hashedId stateCommitPre epoch
  else
    return computeNullifier hashedId stateCommitPre epoch

end Commit
end Payments
end HeytingLean
