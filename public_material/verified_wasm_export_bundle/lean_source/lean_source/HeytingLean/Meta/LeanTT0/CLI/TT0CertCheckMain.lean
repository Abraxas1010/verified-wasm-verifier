import Lean
import Lean.Data.Json
import HeytingLean.Meta.LeanTT0.Hash
import HeytingLean.Meta.LeanTT0.Rules
import HeytingLean.Meta.LeanTT0.Trace
import HeytingLean.Meta.LeanTT0.Checker
import HeytingLean.Meta.LeanTT0.Core
import HeytingLean.Meta.LeanTT0.Merkle
import HeytingLean.Meta.LeanTT0.Parse

/-!
  tt0_cert_check: verify a TT0 certificate JSON against a CAB and kernel JSON.
-/

namespace HeytingLean.Meta.LeanTT0.CLI
namespace TT0CertCheckMain

open HeytingLean.Meta.LeanTT0
open Lean

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

private def readCab (p : String) : IO CAB := do
  let s ← IO.FS.readFile p
  match Json.parse s with
  | .error e => throw <| IO.userError s!"invalid cab.json: {e}"
  | .ok j =>
    let fnd := match j.getObjVal? "foundationCommitment" with | .ok (.str h) => h | _ => "0x"
    let root := match j.getObjVal? "rulesRoot" with | .ok (.str h) => h | _ => "0x"
    pure { version := "cab-1", foundationCommitment := hexToBA fnd, rulesRoot := hexToBA root }

private def readKernel (p : String) : IO KernelInfo := do
  let s ← IO.FS.readFile p
  match Json.parse s with
  | .error e => throw <| IO.userError s!"invalid kernel.json: {e}"
  | .ok j =>
    let kc := match j.getObjVal? "kernelCommitment" with | .ok (.str h) => h | _ => "0x"
    pure { kernelCommitment := hexToBA kc }

def main (args : List String) : IO UInt32 := do
  -- Args: --cab <file> --kernel <file> --cert <file>
  let rec parse (xs : List String) (cab : String) (ker : String) (cert : Option String) :=
    match xs with
    | [] => (cab, ker, cert)
    | "--cab"::p::xs' => parse xs' p ker cert
    | "--kernel"::p::xs' => parse xs' cab p cert
    | "--cert"::p::xs' => parse xs' cab ker (some p)
    | _::xs' => parse xs' cab ker cert
  let (cabPath, kerPath, certPath?) := parse args "out/cab.json" "out/kernel.json" none
  let some certPath := certPath? | IO.eprintln "usage: lake exe tt0_cert_check --cab <cab.json> --kernel <kernel.json> --cert <cert.json>"; return 2
  let cab ← readCab cabPath
  let ker ← readKernel kerPath
  let s ← IO.FS.readFile certPath
  let j ← match Json.parse s with | .ok j => pure j | .error e => IO.eprintln e; return 2
  let o ← match j.getObj? with | .ok o => pure o | .error _ => IO.eprintln "cert: not object"; return 2
  -- new nested cab object
  let cabO ← match o.get? "cab" with | some (.obj co) => pure co | _ => IO.eprintln "cert: cab object missing"; return 2
  let fnd ← match cabO.get? "foundationCommitment" with | some (.str h) => pure (hexToBA h) | _ => IO.eprintln "cert.cab: foundationCommitment missing"; return 2
  let _mCommit ← match cabO.get? "manifestCommit" with | some (.str h) => pure (hexToBA h) | _ => IO.eprintln "cert.cab: manifestCommit missing"; return 2
  let rulesRoot ← match cabO.get? "rulesRoot" with | some (.str h) => pure (hexToBA h) | _ => IO.eprintln "cert.cab: rulesRoot missing"; return 2
  let kc ← match o.get? "kernelCommitment" with | some (.str h) => pure (hexToBA h) | _ => IO.eprintln "cert: kernelCommitment missing"; return 2
  let initD ← match o.get? "initialDigest" with | some (.str h) => pure (hexToBA h) | _ => IO.eprintln "cert: initialDigest missing"; return 2
  let finD ← match o.get? "finalDigest" with | some (.str h) => pure (hexToBA h) | _ => IO.eprintln "cert: finalDigest missing"; return 2
  let trRootGot ← match o.get? "transcriptRoot" with | some (.str h) => pure (hexToBA h) | _ => IO.eprintln "cert: transcriptRoot missing"; return 2
  let termS ← match o.get? "term" with | some (.str s) => pure s | _ => IO.eprintln "cert: term missing"; return 2
  let steps ← match o.get? "steps" with | some (.arr a) => pure a | _ => IO.eprintln "cert: steps missing"; return 2
  let t0 ← match parseTerm termS with | .ok t => pure t | .error e => IO.eprintln e; return 2
  -- Build transcript
  let mut trs : List TraceStep := []
  for i in [0:steps.size] do
    let si := steps[i]!
    let so ← match si.getObj? with | .ok o => pure o | .error _ => IO.eprintln s!"steps[{i}]: not object"; return 2
    let rule ← match so.get? "rule" with
      | some (.str "BetaLamApp") => pure KernelRule.BetaLamApp
      | some (.str "DeltaPrimNatAdd") => pure KernelRule.DeltaPrimNatAdd
      | _ => IO.eprintln s!"steps[{i}]: unknown rule"; return 2
    let before ← match so.get? "before" with | some (.str h) => pure (hexToBA h) | _ => IO.eprintln s!"steps[{i}]: before missing"; return 2
    let after ← match so.get? "after" with | some (.str h) => pure (hexToBA h) | _ => IO.eprintln s!"steps[{i}]: after missing"; return 2
    let proof ← match so.get? "ruleMerkleProof" with | some (.arr arr) => pure (arr.toList.map (fun j => match j with | .str h => hexToBA h | _ => ByteArray.empty)) | _ => pure []
    let step : TraceStep := { rule := rule, before := before, after := after, pathToRule := proof }
    trs := trs.concat step
  let tr : Transcript := { steps := trs, initialDigest := initD, finalDigest := finD }
  -- quick field checks
  if fnd ≠ cab.foundationCommitment then IO.eprintln "foundationCommitment mismatch"; return 3
  if rulesRoot ≠ cab.rulesRoot then IO.eprintln "rulesRoot mismatch"; return 3
  if kc ≠ ker.kernelCommitment then IO.eprintln "kernelCommitment mismatch"; return 3
  if !verifyTranscript cab t0 tr then IO.eprintln "verifyTranscript failed"; return 4
  -- transcriptRoot check
  let trRootExp := transcriptRoot tr.steps
  if trRootExp ≠ trRootGot then IO.eprintln "transcriptRoot mismatch"; return 4
  -- optional certificateCommit
  let certCommitGot ← match o.get? "certificateCommit" with | some (.str h) => pure (hexToBA h) | _ => pure (ByteArray.mk #[])
  if certCommitGot.size != 0 then
    let certCommitExp := Hcat "LoF.Cert|" [cab.rulesRoot, ker.kernelCommitment, initD, finD, trRootGot]
    if certCommitExp ≠ certCommitGot then IO.eprintln "certificateCommit mismatch"; return 4
  IO.println s!"tt0_cert_check ok for {certPath}"
  return 0

end TT0CertCheckMain
end HeytingLean.Meta.LeanTT0.CLI

def main (args : List String) : IO UInt32 :=
  HeytingLean.Meta.LeanTT0.CLI.TT0CertCheckMain.main args
