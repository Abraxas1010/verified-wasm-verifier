import Lean
import Lean.Data.Json
import HeytingLean.Meta.LeanTT0.Rules
import HeytingLean.Meta.LeanTT0.Hash
import HeytingLean.Meta.LeanTT0.Merkle
import HeytingLean.LoF.Foundation.Blocks
import HeytingLean.CLI.Args

/-!
  cab_mint: emit a minimal CAB JSON for TT0 replay.

  The CAB contains:
  - a foundation commitment,
  - a Merkle root over rule ids (currently BetaLamApp + DeltaPrimNatAdd),
  - optional commits of a manifest and proof-kit receipt (best-effort).
-/

namespace HeytingLean.Meta.LeanTT0.CLI
namespace CABMintMain

open HeytingLean.Meta.LeanTT0
open Lean

private def hexOfBA (ba : ByteArray) : String :=
  let parts := ba.toList.map (fun b =>
    let s := (Nat.toDigits 16 b.toNat).asString
    if s.length = 1 then "0" ++ s else s)
  "0x" ++ String.intercalate "" parts

private def catBA (a b : ByteArray) : ByteArray :=
  ByteArray.mk (a.data ++ b.data)

private def mkRoot (leaves : List ByteArray) : ByteArray := HeytingLean.Meta.LeanTT0.merkleRoot leaves

def main (args : List String) : IO UInt32 := do
  let args := HeytingLean.CLI.stripLakeArgs args
  -- parse output dir, optional manifest + proofkit receipt + physical crypto snapshot
  let rec parse (xs : List String) (out : String) (manifest : Option String)
      (pk : Option String) (physCrypto : Option String) :=
    match xs with
    | [] => (out, manifest, pk, physCrypto)
    | "--out"::p::xs' => parse xs' p manifest pk physCrypto
    | "--manifest"::p::xs' => parse xs' out (some p) pk physCrypto
    | "--proofkit"::p::xs' => parse xs' out manifest (some p) physCrypto
    | "--physical-crypto"::p::xs' => parse xs' out manifest pk (some p)
    | _::xs' => parse xs' out manifest pk physCrypto
  let (outDir, manifestPath?, pkPath?, physCryptoPath?) := parse args "out" none none none
  -- ensure dir exists (robust to missing permissions)
  try
    IO.FS.createDirAll outDir
  catch e =>
    IO.eprintln s!"E-CAB-OUTDIR {e}"
    return (UInt32.ofNat 2)
  let ruleB := KernelRule.BetaLamApp
  let ruleD := KernelRule.DeltaPrimNatAdd
  let ridB  := ruleId ruleB
  let ridD  := ruleId ruleD
  let rulesRoot := mkRoot [ridB.hash, ridD.hash]
  let rulesRootPoseidon := HeytingLean.Meta.LeanTT0.transcriptRootPoseidon [] |> (fun _ =>
    -- derive poseidon-style root over rule ids for dual roots
    HeytingLean.Meta.LeanTT0.poseidonRoot [ridB.hash, ridD.hash])
  let witnessB := HeytingLean.LoF.Foundation.betaLamAppBlock.witness.digest
  let witnessD := HeytingLean.LoF.Foundation.deltaPrimNatAddBlock.witness.digest
  let fnd :=
    H "LoF.CAB.Foundation|"
      (catBA (catBA (catBA witnessB witnessD) (serializeRule ruleB)) (serializeRule ruleD))
  -- optional manifest commit
  let mCommit ← match manifestPath? with
    | some p =>
        try
          let s ← IO.FS.readFile p
          pure (H "LoF.Manifest|" s.toUTF8)
        catch _ =>
          IO.eprintln s!"warning: manifest read failed at '{p}', using empty commit"
          pure (H "LoF.Manifest|" "".toUTF8)
    | none => pure (H "LoF.Manifest|" "".toUTF8)
  -- optional proof-kit receipt commit
  let pkCommit? ← match pkPath? with
    | some p =>
        try
          let s ← IO.FS.readFile p
          pure (some (H "ProofKit.Receipt|" s.toUTF8))
        catch _ =>
          IO.eprintln s!"warning: proofkit read failed at '{p}', skipping provenance"
          pure none
    | none => pure none
  -- optional physical-system crypto context commit (PUF/TRNG evidence snapshot)
  let physicalCrypto? ← match physCryptoPath? with
    | some p =>
        try
          let s ← IO.FS.readFile p
          let commit := H "LoF.PhysicalCrypto|" s.toUTF8
          pure (some (p, s, commit))
        catch _ =>
          IO.eprintln s!"warning: physical crypto snapshot read failed at '{p}', skipping physical provenance"
          pure none
    | none => pure none
  let cab := Json.mkObj [
    ("version", Json.str "cab-1"),
    ("algo", Json.str "sha256"),
    ("foundationCommitment", Json.str (hexOfBA fnd)),
    ("rulesRoot", Json.str (hexOfBA rulesRoot)),
    ("rulesRoot_poseidon", Json.str (hexOfBA rulesRootPoseidon)),
    ("manifestCommit", Json.str (hexOfBA mCommit)),
    ("rules", Json.arr #[
      Json.mkObj [
        ("name", Json.str "BetaLamApp"),
        ("ruleId", Json.str (hexOfBA ridB.hash)),
        ("lofWitness", Json.str (hexOfBA witnessB)),
        ("spec", Json.mkObj [
          ("premises", Json.str "((λx. b) a) ⇒ b[x:=a]"),
          ("domain", Json.str "LeanTT0 terms"),
          ("side", Json.str "well-typed beta")
        ])
      ],
      Json.mkObj [
        ("name", Json.str "DeltaPrimNatAdd"),
        ("ruleId", Json.str (hexOfBA ridD.hash)),
        ("lofWitness", Json.str (hexOfBA witnessD)),
        ("spec", Json.mkObj [
          ("premises", Json.str "((add n) m) ⇒ (n + m)"),
          ("domain", Json.str "TT0 nat terms"),
          ("side", Json.str "delta primitive")
        ])
      ]
    ])
  ]
  -- attach provenance if provided
  let mut provFields : List (String × Json) := []
  match pkCommit? with
  | some pk =>
      provFields := ("proofKitReceiptCommit", Json.str (hexOfBA pk)) :: provFields
  | none => pure ()
  match physicalCrypto? with
  | some (path, contents, commit) =>
      provFields := ("physicalCryptoPath", Json.str path) :: provFields
      provFields := ("physicalCryptoBytes", toJson contents.length) :: provFields
      provFields := ("physicalCryptoCommit", Json.str (hexOfBA commit)) :: provFields
  | none => pure ()
  let cab := if provFields.isEmpty then cab
    else
      let prov := Json.mkObj provFields.reverse
      cab.mergeObj (Json.mkObj [("provenance", prov)])
  let cabPath := s!"{outDir}/cab.json"
  try
    IO.FS.writeFile cabPath (Json.compress cab)
  catch e =>
    IO.eprintln s!"E-CAB-WRITE {e}"
    return (UInt32.ofNat 3)
  -- also emit convenience files (best-effort)
  try
    IO.FS.writeFile s!"{outDir}/cab.hash" (hexOfBA fnd)
  catch _ =>
    IO.eprintln s!"warning: failed to write {outDir}/cab.hash"
  try
    IO.FS.writeFile s!"{outDir}/cab.merkle" (hexOfBA rulesRoot)
  catch _ =>
    IO.eprintln s!"warning: failed to write {outDir}/cab.merkle"
  IO.println s!"Wrote {cabPath}"
  return (UInt32.ofNat 0)

end CABMintMain
end HeytingLean.Meta.LeanTT0.CLI

def main (args : List String) : IO UInt32 :=
  HeytingLean.Meta.LeanTT0.CLI.CABMintMain.main args
