import Lean
import Lean.Data.Json

namespace HeytingLean
namespace Payments
namespace Merkle

open Lean

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

private def commitIO (tag : String) (payload : String) : IO String := do
  let mode ← getCommitMode
  if mode == "poseidon" then
    match (← poseidonExe?) with
    | some exe =>
        let cwd ← IO.currentDir
        let outDir := cwd / System.FilePath.mk ".tmp/pay_merkle"
        let _ ← IO.FS.createDirAll outDir
        let inPath := outDir / s!"{tag}_payload.txt"
        IO.FS.writeFile inPath payload
        let out ← IO.Process.output { cmd := exe.toString, args := #[tag, inPath.toString] }
        if out.exitCode == 0 then
          match Json.parse out.stdout with
          | .ok j =>
              match j.getObjVal? "hex" with
              | .ok (.str hex) => return hex
              | _ => return s!"ps:{tag}:{payload}"
          | .error _ => return s!"ps:{tag}:{payload}"
        else
          return s!"ps:{tag}:{payload}"
    | none => return s!"ps:{tag}:{payload}"
  else
    return s!"ps:{tag}:{payload}"

structure PathElem where
  side : String -- "L" or "R"
  hash : String -- hex string

structure VProof where
  root : String
  recipient : String
  path : List PathElem

open Lean (Json)

def parsePathElemE (j : Json) : Except String PathElem := do
  let side ← (j.getObjVal? "side") >>= (fun s => s.getStr?)
  let hash ← (j.getObjVal? "hash") >>= (fun s => s.getStr?)
  return { side, hash }

def parseVProofE (j : Json) : Except String VProof := do
  let root ← (j.getObjVal? "root") >>= (fun s => s.getStr?)
  let recipient ← (j.getObjVal? "recipient") >>= (fun s => s.getStr?)
  let arr ← (j.getObjVal? "path") >>= (fun s => s.getArr?)
  let elems := (← (arr.toList.mapM parsePathElemE))
  return { root, recipient, path := elems }

def computeLeafIO (recipient : String) : IO String :=
  commitIO "LEAF" recipient

def combineIO (left right : String) : IO String := do
  commitIO "MERKLE" s!"{left}:{right}"

def verifyMembershipIO (p : VProof) : IO (Bool × String) := do
  let mut acc ← computeLeafIO p.recipient
  for e in p.path do
    let side := e.side
    let sib := e.hash
    acc ← if side == "L" then combineIO sib acc else combineIO acc sib
  return (acc == p.root, acc)

/-! ## Pure (string-mode) Merkle helpers

These helpers mirror the IO versions but avoid effects by always using the
deterministic string commit fallback. They are suitable for native tests and
tools that do not require external Poseidon binaries. -/

def computeLeaf (recipient : String) : String :=
  s!"ps:LEAF:{recipient}"

def combine (left right : String) : String :=
  s!"ps:MERKLE:{left}:{right}"

def verifyMembership (p : VProof) : (Bool × String) :=
  let acc0 := computeLeaf p.recipient
  let acc := p.path.foldl (init := acc0) (fun acc e =>
    if e.side == "L" then combine e.hash acc else combine acc e.hash)
  (acc == p.root, acc)

end Merkle
end Payments
end HeytingLean
