import Lean
import Lean.Data.Json
import HeytingLean.Payments.Merkle

namespace Tests

open HeytingLean.Payments
open HeytingLean.Payments.Merkle

structure Tree where
  levels : List (List String)  -- level 0 = leaves
  deriving Inhabited

def buildTreeFromLeaves (leaves : List String) : Tree :=
  let rec nextLevel (xs : List String) (acc : List String) : List String :=
    match xs with
    | [] => acc.reverse
    | [a] => (combine a a) :: acc |>.reverse
    | a::b::rest => nextLevel rest ((combine a b) :: acc)
  let rec loop (lvl : List String) (acc : List (List String)) (k : Nat) : List (List String) :=
    if lvl.length ≤ 1 then (lvl :: acc).reverse else
      match k with
      | 0 => (lvl :: acc).reverse
      | Nat.succ k' =>
        let n := nextLevel lvl []
        loop n (lvl :: acc) k'
  { levels := loop leaves [] (leaves.length + 1) }

def rootOf (t : Tree) : String :=
  match t.levels.reverse with
  | [] => ""
  | top::_ => match top with | [] => "" | r::_ => r

def genProof (t : Tree) (recipient : String) (idx : Nat) : VProof :=
  let totalLevels := t.levels.length
  let rec go (level : Nat) (index : Nat) (path : List PathElem) : List PathElem :=
    if level ≥ totalLevels then path.reverse else
      match t.levels[level]? with
      | none => path.reverse
      | some lvl =>
        if lvl.length = 1 then
          path.reverse
        else if h : index < lvl.length then
          let sibIdx := if index % 2 = 0 then index + 1 else index - 1
          let side := if index % 2 = 0 then "R" else "L"
          let sib := if sibIdx < lvl.length then lvl.getD sibIdx "" else lvl.getD index ""
          let path' := { side := side, hash := sib } :: path
          let parentIdx := index / 2
          go (level + 1) parentIdx path'
        else path.reverse
  let path := go 0 idx []
  { root := rootOf t, recipient := recipient, path := path }

def run (_args : List String) : IO UInt32 := do
  IO.println "=== TEST: Merkle Tree Operations (native) ==="
  let recipients := ["0xa1", "0xa2", "0xa3", "0xa4"]
  let leaves := recipients.map computeLeaf
  let tree := buildTreeFromLeaves leaves
  let root := rootOf tree
  for idx in [0:recipients.length] do
    let proof := genProof tree recipients[idx]! idx
    let (ok, _) := verifyMembership proof
    if (!ok) || proof.root ≠ root then
      IO.eprintln s!"Valid membership failed for idx={idx}"; return 1
  let non := "0xBAD"
  let fake := genProof tree recipients[0]! 0
  let fake2 := { fake with recipient := non }
  let (ok2, _) := verifyMembership fake2
  if ok2 then IO.eprintln "Non-member verified unexpectedly"; return 1
  let good := genProof tree recipients[0]! 0
  let wrong := { good with path := good.path.reverse }
  let (ok3, _) := verifyMembership wrong
  if ok3 then IO.eprintln "Wrong path verified unexpectedly"; return 1
  let bigRecipients := (List.range 1000).map (fun i => s!"0x{i}")
  let bigLeaves := bigRecipients.map computeLeaf
  let bigTree := buildTreeFromLeaves bigLeaves
  let proofBig := genProof bigTree bigRecipients[500]! 500
  let (okB, _) := verifyMembership proofBig
  if !okB then IO.eprintln "Large tree membership failed"; return 1
  IO.println s!"✓ Merkle tree validated up to {bigRecipients.length} elements"
  return 0

def main (_args : List String) : IO UInt32 := do
  IO.println "=== TEST: Merkle Tree Operations (native) ==="
  let recipients := ["0xa1", "0xa2", "0xa3", "0xa4"]
  let leaves := recipients.map computeLeaf
  let tree := buildTreeFromLeaves leaves
  let root := rootOf tree
  -- valid memberships
  for idx in [0:recipients.length] do
    let proof := genProof tree recipients[idx]! idx
    let (ok, _) := verifyMembership proof
    if (!ok) || proof.root ≠ root then
      IO.eprintln s!"Valid membership failed for idx={idx}"; return 1
  -- non-member fails
  let non := "0xBAD"
  let fake := genProof tree recipients[0]! 0
  let fake2 := { fake with recipient := non }
  let (ok2, _) := verifyMembership fake2
  if ok2 then IO.eprintln "Non-member verified unexpectedly"; return 1
  -- wrong path fails (reverse path)
  let good := genProof tree recipients[0]! 0
  let wrong := { good with path := good.path.reverse }
  let (ok3, _) := verifyMembership wrong
  if ok3 then IO.eprintln "Wrong path verified unexpectedly"; return 1
  -- scale test
  let bigRecipients := (List.range 1000).map (fun i => s!"0x{i}")
  let bigLeaves := bigRecipients.map computeLeaf
  let bigTree := buildTreeFromLeaves bigLeaves
  let proofBig := genProof bigTree bigRecipients[500]! 500
  let (okB, _) := verifyMembership proofBig
  if !okB then IO.eprintln "Large tree membership failed"; return 1
  IO.println s!"✓ Merkle tree validated up to {bigRecipients.length} elements"
  return 0

end Tests

def main (args : List String) : IO UInt32 :=
  Tests.run args
