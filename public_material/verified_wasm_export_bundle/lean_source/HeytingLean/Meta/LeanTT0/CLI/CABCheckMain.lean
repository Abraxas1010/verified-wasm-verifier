import Lean
import Lean.Data.Json
import HeytingLean.CLI.Args
import HeytingLean.Meta.LeanTT0.Hash
import HeytingLean.Meta.LeanTT0.Rules
import HeytingLean.Meta.LeanTT0.Merkle
import HeytingLean.LoF.Foundation.Blocks

/-!
  cab_check: sanity-check a CAB JSON by re-deriving rulesRoot and
  foundationCommitment with local logic.
-/

namespace HeytingLean.Meta.LeanTT0.CLI
namespace CABCheckMain

open HeytingLean.Meta.LeanTT0
open Lean

private def hexOfBA (ba : ByteArray) : String :=
  let parts := ba.toList.map (fun b =>
    let s := (Nat.toDigits 16 b.toNat).asString
    if s.length = 1 then "0" ++ s else s)
  "0x" ++ String.intercalate "" parts

private def hexToBA (s : String) : ByteArray := Id.run do
  let ss := if s.startsWith "0x" then s.drop 2 else s
  let val (c : Char) : Nat :=
    if c.isDigit then c.toNat - '0'.toNat
    else if c ≥ 'a' && c ≤ 'f' then 10 + (c.toNat - 'a'.toNat)
    else if c ≥ 'A' && c ≤ 'F' then 10 + (c.toNat - 'A'.toNat)
    else 0
  let rec loop (xs : List Char) (acc : Array UInt8) : Array UInt8 :=
    match xs with
    | c1::c2::rest => loop rest (acc.push (UInt8.ofNat (val c1 * 16 + val c2)))
    | _ => acc
  ByteArray.mk (loop ss.toList #[])

def main (args : List String) : IO UInt32 := do
  let args := HeytingLean.CLI.stripLakeArgs args
  let rec parse (xs : List String) (cabPath : String) (physPath : Option String)
      (requirePhysical : Bool) :=
    match xs with
    | [] => (cabPath, physPath, requirePhysical)
    | "--cab" :: p :: xs' => parse xs' p physPath requirePhysical
    | "--physical-crypto" :: p :: xs' => parse xs' cabPath (some p) requirePhysical
    | "--require-physical" :: xs' => parse xs' cabPath physPath true
    | x :: xs' =>
        if x.startsWith "--" then
          parse xs' cabPath physPath requirePhysical
        else
          -- Backward compatible positional cab path.
          parse xs' x physPath requirePhysical
  let (cabPath, physPath?, requirePhysical) := parse args "out/cab.json" none false
  let raw? : Option String ← do
    try
      let s ← IO.FS.readFile cabPath
      pure (some s)
    catch e =>
      IO.eprintln s!"E-CAB-OPEN {e}"
      pure none
  let raw ← match raw? with
    | some s => pure s
    | none => return 2
  let j ← match Json.parse raw with | .ok j => pure j | .error e => IO.eprintln e; return 2
  let obj ← match j.getObj? with | .ok o => pure o | .error _ => IO.eprintln "cab: not object"; return 2
  let rulesArr ← match obj.get? "rules" with | some (.arr a) => pure a | _ => IO.eprintln "cab: rules not array"; return 2
  -- Gather ruleIds from JSON array
  let mut leaves : Array ByteArray := #[]
  for i in [0:rulesArr.size] do
    let ri := rulesArr[i]!
    let rid ←
      match ri.getObj? with
      | .ok o =>
          match o.get? "ruleId" with
          | some (.str hx) => pure (hexToBA hx)
          | _ => IO.eprintln s!"cab: rules[{i}] missing ruleId"; return 2
      | .error _ => IO.eprintln s!"cab: rules[{i}] not object"; return 2
    leaves := leaves.push rid
  let rootExp := merkleRoot leaves.toList
  let rootGot ← match obj.get? "rulesRoot" with | some (.str s) => pure (hexToBA s) | _ => IO.eprintln "cab: rulesRoot missing"; return 2
  if rootExp ≠ rootGot then
    IO.eprintln s!"rulesRoot mismatch: expected {hexOfBA rootExp}, got {hexOfBA rootGot}"; return 3
  -- optional manifestCommit check exists (no content verification here)
  match obj.get? "manifestCommit" with
  | some (.str _h) => pure ()
  | _ => IO.eprintln "[WARN] cab: manifestCommit missing"
  -- Foundation commitment: recompute using the same domain separation as cab_mint
  let witnessB := HeytingLean.LoF.Foundation.betaLamAppBlock.witness.digest
  let witnessD := HeytingLean.LoF.Foundation.deltaPrimNatAddBlock.witness.digest
  let payload :=
    ByteArray.mk
      (witnessB.data ++ witnessD.data ++ (serializeRule .BetaLamApp).data ++
        (serializeRule .DeltaPrimNatAdd).data)
  let fndExp := H "LoF.CAB.Foundation|" payload
  let fndGot ← match obj.get? "foundationCommitment" with | some (.str s) => pure (hexToBA s) | _ => IO.eprintln "cab: foundationCommitment missing"; return 2
  if fndExp ≠ fndGot then
    IO.eprintln s!"foundationCommitment mismatch: expected {hexOfBA fndExp}, got {hexOfBA fndGot}"; return 4
  -- Optional physical-system crypto provenance verification.
  let physicalCommitInCab? : Option ByteArray :=
    match obj.get? "provenance" with
    | some (.obj prov) =>
        match prov.get? "physicalCryptoCommit" with
        | some (.str s) => some (hexToBA s)
        | _ => none
    | _ => none
  if requirePhysical && physicalCommitInCab?.isNone then
    IO.eprintln "cab: required physicalCryptoCommit missing in provenance"
    return 5
  match physPath? with
  | some p =>
      let content? : Option String ← do
        try
          pure (some (← IO.FS.readFile p))
        catch _ =>
          pure none
      match content? with
      | none =>
          if requirePhysical then
            IO.eprintln s!"cab: required physical crypto snapshot unreadable at {p}"
            return 6
          else
            IO.eprintln s!"[WARN] cab: physical crypto snapshot unreadable at {p}"
      | some content =>
          let expected := H "LoF.PhysicalCrypto|" content.toUTF8
          match physicalCommitInCab? with
          | some got =>
              if expected ≠ got then
                IO.eprintln s!"physicalCryptoCommit mismatch: expected {hexOfBA expected}, got {hexOfBA got}"
                return 7
          | none =>
              if requirePhysical then
                IO.eprintln "cab: physical snapshot provided but cab lacks physicalCryptoCommit"
                return 8
              else
                IO.eprintln "[WARN] cab: physical snapshot provided but cab has no physicalCryptoCommit"
  | none =>
      if requirePhysical then
        IO.eprintln "cab: --require-physical requires --physical-crypto <path>"
        return 9
      else
        match physicalCommitInCab? with
        | some _ => IO.eprintln "[WARN] cab: physicalCryptoCommit present but no --physical-crypto snapshot provided; skipping physical verification"
        | none => pure ()
  IO.println s!"cab_check ok for {cabPath}"
  return 0

end CABCheckMain
end HeytingLean.Meta.LeanTT0.CLI

def main (args : List String) : IO UInt32 :=
  HeytingLean.Meta.LeanTT0.CLI.CABCheckMain.main args
