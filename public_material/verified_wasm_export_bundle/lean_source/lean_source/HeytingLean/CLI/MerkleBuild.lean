import Lean
import Lean.Data.Json
import HeytingLean.Payments.Merkle
import HeytingLean.Util.SHA

/-!
Build a Poseidon-based Merkle tree from an address list and emit a proof-kit-like summary.
- name: deterministic label from addresses
- id: deterministic 24-char hex (first 24 of sha256)
- chain: passthrough string (optional)
- merkle_root, depth, count

Input JSON:
{ "addresses": ["0x...", ...], "chain": "84532", "depth": 20? }
If no JSON is given, pass addresses as CLI args: merkle_build --chain=84532 addr1 addr2 ...
-/

namespace HeytingLean
namespace CLI
namespace MerkleBuild

open Lean
open Payments.Merkle

private def readFileE (p : System.FilePath) : IO (Except String String) := do
  try let s ← IO.FS.readFile p; pure (.ok s) catch e => pure (.error s!"read error at {p}: {e}")

private def pairLevel : List String → List String
  | [] => []
  | [z] => [combine z z]
  | a :: b :: rest => combine a b :: pairLevel rest

private def buildRootFuel (fuel lvl : Nat) (xs : List String) : (String × Nat) :=
  match fuel with
  | 0 => ("0x", lvl)
  | fuel + 1 =>
      match xs with
      | [] => ("0x", lvl)
      | [x] => (x, lvl)
      | _ => buildRootFuel fuel (lvl + 1) (pairLevel xs)

def buildRoot (leaves : List String) : (String × Nat) :=
  buildRootFuel leaves.length 0 leaves

def toLeaves (addrs : List String) : List String :=
  addrs.map computeLeaf

def makeName (addrs : List String) : IO String := do
  let base := String.intercalate ":" addrs
  let h ← HeytingLean.Util.sha256HexOfStringIO base
  pure s!"m_{h.drop 2}" -- include suffix without 0x for readability

def makeId (addrs : List String) : IO String := do
  let base := String.intercalate ":" addrs
  let h ← HeytingLean.Util.sha256HexOfStringIO base
  let raw := if h.startsWith "0x" then h.drop 2 else h
  pure (raw.take 24)

def main (args : List String) : IO UInt32 := do
  let mut chain : String := ""
  let mut jsonPath : Option String := none
  let mut addrArgs : List String := []
  for a in args do
    if a.startsWith "--chain=" then chain := a.drop 8
    else if a.startsWith "--json=" then jsonPath := some (a.drop 7)
    else addrArgs := addrArgs.concat a
  let (addresses, chainVal) ← match jsonPath with
    | some p => do
        let raw ← match (← readFileE (System.FilePath.mk p)) with | .ok s => pure s | .error m => IO.eprintln m; return 1
        let j ← match Lean.Json.parse raw with | .ok j => pure j | .error e => IO.eprintln e; return 1
        let arr ← match j.getObjVal? "addresses" with
          | .ok v =>
              match v.getArr? with
              | .ok a => pure a
              | .error _ => do IO.eprintln "addresses not array"; return 1
          | .error _ => do IO.eprintln "missing addresses"; return 1
        let addrs := arr.toList.filterMap (fun x => x.getStr?.toOption)
        let ch := match j.getObjVal? "chain" with | .ok (.str s) => s | _ => chain
        pure (addrs, ch)
    | none => pure (addrArgs, chain)
  let leaves := toLeaves addresses
  let (root, depth) := buildRoot leaves
  let name ← makeName addresses
  let id ← makeId addresses
  let out := Lean.Json.mkObj
    [ ("name", Lean.Json.str name)
    , ("id", Lean.Json.str id)
    , ("chain", Lean.Json.str chainVal)
    , ("merkle_root", Lean.Json.str root)
    , ("depth", Lean.Json.num depth)
    , ("count", Lean.Json.num addresses.length)
    ]
  IO.println out.compress
  return 0

end MerkleBuild
end CLI
end HeytingLean

def main (args : List String) : IO UInt32 := HeytingLean.CLI.MerkleBuild.main args
