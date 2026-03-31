import Lean
import Lean.Data.Json

import HeytingLean.Blockchain.MerkleModel
import HeytingLean.CLI.Args
import HeytingLean.Crypto.Primitives.Spec
import HeytingLean.Payments.Merkle

/-!
# `merkle_demo` CLI

Modes:

1. `--proof <path>`: parse a JSON `VProof`, run `verifyMembership`, and emit JSON.
2. `--struct-demo`: build a tiny structural Merkle tree, build a path with `buildPath?`,
   then run both `verifyMembership` and `verifyMembershipIO`.

With no args, runs a small built-in demo (pure verifier only).
-/

namespace HeytingLean
namespace CLI
namespace MerkleDemo

open Lean
open HeytingLean.Blockchain.MerkleModel
open Payments.Merkle

private def readFileE (path : System.FilePath) : IO (Except String String) := do
  try
    let s ← IO.FS.readFile path
    pure (.ok s)
  catch e =>
    pure (.error s!"read error: {e}")

private def parseProof (s : String) : Except String VProof := do
  match Json.parse s with
  | .error e => .error e
  | .ok j =>
    match parseVProofE j with
    | .ok p => .ok p
    | .error m => .error m

/-! ## Structural demo -/

/-- A tiny example Merkle tree with two leaves. -/
def exampleTree : Tree :=
  Tree.node (Tree.leaf "alice") (Tree.leaf "bob")

def runStructDemo : IO UInt32 := do
  let t := exampleTree
  let x := "alice"
  match buildPath? x t with
  | none =>
      IO.eprintln "merkle_demo: buildPath? returned none for payload \"alice\""
      return 1
  | some path =>
      let rootStruct := root t
      let proof : VProof := { root := rootStruct, recipient := x, path := path }
      let (bPure, rootPure) := verifyMembership proof
      IO.println s!"merkle_demo (pure): ok={bPure}, root={rootPure}, structural_root={rootStruct}"
      let (bIO, rootIO) ← verifyMembershipIO proof
      IO.println s!"merkle_demo (IO): ok={bIO}, root={rootIO}"
      return 0

def run (argv : List String) : IO UInt32 := do
  let argv := HeytingLean.CLI.stripLakeArgs argv
  if argv.any (fun a => a == "--help" || a == "-h") then
    IO.eprintln "usage: merkle_demo [--proof path/to/proof.json] [--struct-demo]"
    return 0
  if argv.any (fun a => a == "--struct-demo") then
    return (← runStructDemo)
  let hasProofFlag :=
    argv.any (fun a => a == "--proof" || a.startsWith "--proof=")
  let rec findProof : List String → Option String
    | [] => none
    | "--proof" :: p :: _ => some p
    | a :: rest =>
        if a.startsWith "--proof=" then some (a.drop 8) else findProof rest
  match findProof argv with
  | some pstr =>
      let p := System.FilePath.mk pstr
      let raw ← match (← readFileE p) with
        | .ok s => pure s
        | .error m => IO.eprintln m; return 1
      let pr ← match parseProof raw with
        | .ok pr => pure pr
        | .error m => IO.eprintln m; return 1
      let (ok, root) := verifyMembership pr
      let out := Json.mkObj [ ("ok", Json.bool ok), ("computed_root", Json.str root) ]
      IO.println out.compress
      return (if ok then 0 else 3)
  | none =>
      if hasProofFlag then
        IO.eprintln "usage: merkle_demo --proof path/to/proof.json"
        return 2
      -- Default demo: verify an empty Merkle path (root == leaf(recipient)).
      let recipient := "alice"
      let root := computeLeaf recipient
      let pr : VProof := { root := root, recipient := recipient, path := [] }
      let (ok, computed) := verifyMembership pr
      let out := Json.mkObj
        [ ("ok", Json.bool ok)
        , ("mode", Json.str "demo")
        , ("recipient", Json.str recipient)
        , ("computed_root", Json.str computed)
        ]
      IO.println out.compress
      return (if ok then 0 else 3)

end MerkleDemo
end CLI
end HeytingLean

def main (argv : List String) : IO UInt32 :=
  HeytingLean.CLI.MerkleDemo.run argv
