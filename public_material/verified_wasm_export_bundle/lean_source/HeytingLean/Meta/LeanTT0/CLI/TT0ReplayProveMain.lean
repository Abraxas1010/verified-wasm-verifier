import Lean
import Lean.Data.Json
import HeytingLean.Meta.LeanTT0.Hash
import HeytingLean.Meta.LeanTT0.Rules
import HeytingLean.Meta.LeanTT0.Trace
import HeytingLean.Meta.LeanTT0.Checker
import HeytingLean.Meta.LeanTT0.Core
import HeytingLean.Meta.LeanTT0.Merkle
import HeytingLean.Meta.LeanTT0.Parse
import HeytingLean.Util.CanonJson
import HeytingLean.CLI.Args

/-!
  tt0_replay_prove: replay a small TT0 transcript and emit a certificate.

  This tool is executable-first: it is primarily a robust IO surface that
  exercises transcript generation, Merkle membership proofs for rule ids, and
  deterministic hashing for certificate commitments.
-/

namespace HeytingLean.Meta.LeanTT0.CLI
namespace TT0ReplayProveMain

open HeytingLean.Meta.LeanTT0
open Lean

private def hexOfBA (ba : ByteArray) : String :=
  let parts := ba.toList.map (fun b =>
    let s := (Nat.toDigits 16 b.toNat).asString
    if s.length = 1 then "0" ++ s else s)
  "0x" ++ String.intercalate "" parts

private def hexToBA (s : String) : ByteArray := Id.run do
  let ss := if s.startsWith "0x" then s.drop 2 else s
  let chars := ss.toList
  let val (c : Char) : Nat :=
    if c.isDigit then c.toNat - '0'.toNat
    else if c ≥ 'a' && c ≤ 'f' then 10 + (c.toNat - 'a'.toNat)
    else if c ≥ 'A' && c ≤ 'F' then 10 + (c.toNat - 'A'.toNat)
    else 0
  let rec loop (xs : List Char) (acc : Array UInt8) : Array UInt8 :=
    match xs with
    | c1::c2::rest =>
        let b := UInt8.ofNat (val c1 * 16 + val c2)
        loop rest (acc.push b)
    | _ => acc
  ByteArray.mk (loop chars #[])


private def readKernelE (p : String) : IO (Except String KernelInfo) := do
  try
    let s ← IO.FS.readFile p
    match Json.parse s with
    | .error e => pure (.error s!"invalid kernel.json: {e}")
    | .ok j =>
        let kc := match j.getObjVal? "kernelCommitment" with | .ok (.str h) => h | _ => "0x"
        pure (.ok { kernelCommitment := hexToBA kc })
  catch e =>
    pure (.error s!"kernel read error at {p}: {e}")

/-
  Minimal term parser supporting:
  - variables: identifiers [A-Za-z_][A-Za-z0-9_]*
  - (lam x. body)
  - (app f a)
  - atoms can be nested using parentheses
-/
-- parser imported from Parse module

private def readCabE (p : String) : IO (Except String CAB) := do
  try
    let s ← IO.FS.readFile p
    match Json.parse s with
    | .error e => pure (.error s!"invalid cab.json: {e}")
    | .ok j =>
        let fnd := match j.getObjVal? "foundationCommitment" with
          | .ok (.str h) => h
          | _ => "0x"
        let root := match j.getObjVal? "rulesRoot" with
          | .ok (.str h) => h
          | _ => "0x"
        pure (.ok { version := "cab-1", foundationCommitment := hexToBA fnd, rulesRoot := hexToBA root })
  catch e =>
    pure (.error s!"cab read error at {p}: {e}")

def main (args : List String) : IO UInt32 := do
  let args := HeytingLean.CLI.stripLakeArgs args
  -- Args: --cab <path> --kernel <path> --out <dir> [--example] [--term <file>] [--manifest <path>] [--proofkit <path>]
  let rec parse (xs : List String) (cab : Option String) (kerP : Option String) (out : String) (ex : Bool) (termP : Option String) (manP : Option String) (pkP : Option String) :=
    match xs with
    | [] => (cab, kerP, out, ex, termP, manP, pkP)
    | "--cab"::p::xs' => parse xs' (some p) kerP out ex termP manP pkP
    | "--kernel"::p::xs' => parse xs' cab (some p) out ex termP manP pkP
    | "--out"::d::xs' => parse xs' cab kerP d ex termP manP pkP
    | "--example"::xs' => parse xs' cab kerP out true termP manP pkP
    | "--term"::p::xs' => parse xs' cab kerP out ex (some p) manP pkP
    | "--manifest"::p::xs' => parse xs' cab kerP out ex termP (some p) pkP
    | "--proofkit"::p::xs' => parse xs' cab kerP out ex termP manP (some p)
    | _::xs' => parse xs' cab kerP out ex termP manP pkP
  let (cabPath?, kernelPath?, outDir, useEx, termPath?, manifestPath?, proofkitPath?) := parse args none none "out" false none none none
  IO.FS.createDirAll outDir
  let ridB := ruleId KernelRule.BetaLamApp
  let ridD := ruleId KernelRule.DeltaPrimNatAdd
  let defaultRulesLeaves : List ByteArray := [ridB.hash, ridD.hash]
  let defaultRulesRoot : ByteArray := merkleRoot defaultRulesLeaves

  let die {α} (msg : String) : ExceptT UInt32 IO α := do
    ExceptT.lift (IO.eprintln msg)
    throw 2

  let readFileE (label path : String) : ExceptT UInt32 IO String := do
    try
      ExceptT.lift (IO.FS.readFile path)
    catch e =>
      die s!"{label} read error at {path}: {e}"

  let readCab (p : String) : ExceptT UInt32 IO CAB := do
    match (← ExceptT.lift (readCabE p)) with
    | .ok c => pure c
    | .error msg => die msg

  let readKernel (p : String) : ExceptT UInt32 IO KernelInfo := do
    match (← ExceptT.lift (readKernelE p)) with
    | .ok k => pure k
    | .error msg => die msg

  let job : ExceptT UInt32 IO Unit := do
    let cab : CAB ←
      match cabPath? with
      | some p => readCab p
      | none =>
          pure
            { version := "cab-1"
            , foundationCommitment := sha256 "fnd".toUTF8
            , rulesRoot := defaultRulesRoot }

    let ker : KernelInfo ←
      match kernelPath? with
      | some kp => readKernel kp
      | none => pure { kernelCommitment := sha256 "kernel-v0".toUTF8 }

    -- Build term: from --term file if given, else example when requested, fallback to tau
    let t0 : Tm ←
      match termPath? with
      | some p =>
          let raw ← readFileE "term" p
          match parseTerm raw with
          | .ok t => pure t
          | .error e => die e
      | none =>
          if useEx then pure (Tm.app (Tm.lam "x" (Tm.var "x")) (Tm.var "tau")) else pure (Tm.var "tau")

    let tr := runWithTrace 4 t0

    -- attach Merkle proofs using rules in CAB (best-effort parse of cab.json)
    let rulesLeaves : List ByteArray ←
      match cabPath? with
      | none => pure defaultRulesLeaves
      | some p => do
          let raw? : Option String ←
            try
              pure (some (← ExceptT.lift (IO.FS.readFile p)))
            catch _ =>
              pure none
          match raw? with
          | none => pure defaultRulesLeaves
          | some raw =>
              let j := (Json.parse raw).toOption.getD Json.null
              let arr := match j.getObjVal? "rules" with | .ok (.arr a) => a | _ => #[]
              let mut acc : Array ByteArray := #[]
              for i in [0:arr.size] do
                match arr[i]! |>.getObj? with
                | .ok o =>
                    match o.get? "ruleId" with
                    | some (.str h) => acc := acc.push (hexToBA h)
                    | _ => pure ()
                | .error _ => pure ()
              let leaves := acc.toList
              pure (if leaves = [] then defaultRulesLeaves else leaves)

    let proofFor (r : KernelRule) : List ByteArray :=
      let h := (ruleId r).hash
      mkProof rulesLeaves h |>.getD []

    -- enrich transcript with per-step proof paths
    let tr' : Transcript :=
      { tr with steps := tr.steps.map (fun s =>
          let path := proofFor s.rule
          { s with pathToRule := path }) }

    -- verify transcript against CAB and kernel
    if !verifyTranscript cab t0 tr' then
      die "verifyTranscript failed"

    let stepsJson :=
      tr'.steps.toArray.map (fun s => Json.mkObj [
        ("rule", Json.str (match s.rule with | KernelRule.BetaLamApp => "BetaLamApp" | KernelRule.DeltaPrimNatAdd => "DeltaPrimNatAdd")),
        ("ruleId", Json.str (hexOfBA (ruleId s.rule).hash)),
        ("before", Json.str (hexOfBA s.before)),
        ("after",  Json.str (hexOfBA s.after)),
        ("ruleMerkleProof", Json.arr ((s.pathToRule.toArray.map (fun sib => Json.str (hexOfBA sib)))))
      ])
    let trRoot := transcriptRoot tr'.steps
    -- Poseidon-tagged root: internal domain-separated variant only (no external hooks)
    let trRootPoseidon := transcriptRootPoseidon tr'.steps

    -- optional manifest + proofkit commits
    let manCommit ←
      ExceptT.lift <|
        match manifestPath? with
        | some p =>
            try
              let s ← IO.FS.readFile p
              pure (H "LoF.Manifest|" s.toUTF8)
            catch _ =>
              IO.eprintln s!"warning: manifest read failed at '{p}', using empty commit"
              pure (H "LoF.Manifest|" "".toUTF8)
        | none => pure (H "LoF.Manifest|" "".toUTF8)

    let pkCommit? ←
      ExceptT.lift <|
        match proofkitPath? with
        | some p =>
            try
              let s ← IO.FS.readFile p
              pure (some (H "ProofKit.Receipt|" s.toUTF8))
            catch _ =>
              IO.eprintln s!"warning: proofkit read failed at '{p}', skipping provenance"
              pure none
        | none => pure none

    let cabObj := HeytingLean.Util.CanonJson.mkCanonObj [
      ("foundationCommitment", Json.str (hexOfBA cab.foundationCommitment)),
      ("manifestCommit", Json.str (hexOfBA manCommit)),
      ("rulesRoot", Json.str (hexOfBA cab.rulesRoot))
    ]
    let certCommit := Hcat "LoF.Cert|" [cab.rulesRoot, ker.kernelCommitment, tr'.initialDigest, tr'.finalDigest, trRoot]
    let baseCert := HeytingLean.Util.CanonJson.mkCanonObj [
      ("algo", Json.str "sha256"),
      ("cab", cabObj),
      ("certificateCommit", Json.str (hexOfBA certCommit)),
      ("finalDigest", Json.str (hexOfBA tr'.finalDigest)),
      ("initialDigest", Json.str (hexOfBA tr'.initialDigest)),
      ("kernelCommitment", Json.str (hexOfBA ker.kernelCommitment)),
      ("steps", Json.arr stepsJson),
      ("term", Json.str (serializeTerm t0)),
      ("transcriptRoot", Json.str (hexOfBA trRoot)),
      ("transcriptRoot_poseidon", Json.str (hexOfBA trRootPoseidon)),
      ("version", Json.str "cert-1")
    ]
    let certObj := match pkCommit? with
      | some pk =>
          let prov := HeytingLean.Util.CanonJson.mkCanonObj [("proofKitReceiptCommit", Json.str (hexOfBA pk))]
          baseCert.mergeObj (HeytingLean.Util.CanonJson.mkCanonObj [("provenance", prov)])
      | none => baseCert

    let runId := hexOfBA (sha256 tr'.finalDigest) |>.drop 2 |>.take 16
    let outPath := s!"{outDir}/certs/{runId}.json"
    let outDir2 := s!"{outDir}/certs"
    ExceptT.lift (IO.FS.createDirAll outDir2)
    ExceptT.lift (IO.FS.writeFile outPath (Json.compress certObj))
    ExceptT.lift (IO.println s!"Wrote {outPath}")

  match (← job.run) with
  | .ok _ => pure 0
  | .error c => pure c

end TT0ReplayProveMain
end HeytingLean.Meta.LeanTT0.CLI

def main (args : List String) : IO UInt32 :=
  HeytingLean.Meta.LeanTT0.CLI.TT0ReplayProveMain.main args
