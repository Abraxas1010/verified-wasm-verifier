import Lean
import HeytingLean.Crypto.KEM.MLKEM
import HeytingLean.Crypto.KAT.RSP

namespace HeytingLean
namespace CLI

open System

private def katRoot : FilePath := FilePath.mk ".." / "WIP" / "pqc_lattice" / "kat" / "kyber"

private def shQuote (s : String) : String :=
  "'" ++ (s.replace "'" "'\"'\"'") ++ "'"

private def runBash (cmd : String) : IO IO.Process.Output :=
  IO.Process.output { cmd := "/bin/bash", args := #["-c", cmd], cwd := none }

private def parseKVLines (txt : String) : List (String × String) :=
  let step (acc : List (String × String)) (raw : String) :=
    let line := raw.trim
    match line.splitOn "=" with
    | k :: v :: _ => (k.trim, v.trim) :: acc
    | _ => acc
  (txt.splitOn "\n").foldl step []

private def kvGet? (k : String) (kvs : List (String × String)) : Option String :=
  (kvs.find? (fun (k', _) => k' == k)).map (fun (_, v) => v)

private def getFlagValue? (flag : String) (args : List String) : Option String :=
  let rec go : List String → Option String
    | [] => none
    | x :: y :: xs => if x == flag then some y else go (y :: xs)
    | _ :: [] => none
  go args

private def hasFlag (flag : String) (args : List String) : Bool :=
  args.any (fun x => x == flag)

private def parityEncap (rsp cli : FilePath) : IO UInt32 := do
  if !(← rsp.pathExists) then
    IO.eprintln s!"KEM encap parity: .rsp not found at {rsp}"
    return 2
  if !(← cli.pathExists) then
    IO.eprintln s!"KEM encap parity: CLI not found at {cli}"
    return 2
  let cases ← HeytingLean.Crypto.KAT.parseKEMRSPFile rsp
  if cases.isEmpty then
    IO.eprintln s!"KEM encap parity: no cases parsed from {rsp}"
    return 2
  let mut ok : Nat := 0
  for c in cases do
    let seed := HeytingLean.Crypto.KAT.normHex c.seedHex
    let cmd := s!"RNG_SEED={shQuote seed} {shQuote cli.toString}"
    let out? ←
      try
        let out ← runBash cmd
        pure (some out)
      catch _ =>
        pure none
    match out? with
    | none =>
        IO.eprintln s!"FAIL count={c.count} spawn_error"
        continue
    | some out =>
        if out.exitCode != 0 then
          IO.eprintln s!"FAIL count={c.count} rc={out.exitCode} err={out.stderr.trim}"
        else
          let kvs := parseKVLines out.stdout
          let gotPk := (kvGet? "pk" kvs).getD ""
          let gotSk := (kvGet? "sk" kvs).getD ""
          let gotCt := (kvGet? "ct" kvs).getD ""
          let gotSs := (kvGet? "ss" kvs).getD ""
          let mism :=
            [ ("pk", gotPk, c.pkHex)
            , ("sk", gotSk, c.skHex)
            , ("ct", gotCt, c.ctHex)
            , ("ss", gotSs, c.ssHex)
            ].filter (fun (_, g, e) => HeytingLean.Crypto.KAT.normHex g != HeytingLean.Crypto.KAT.normHex e)
          if mism.isEmpty then
            ok := ok + 1
          else
            let keys := mism.map (fun (k, _, _) => k)
            IO.eprintln s!"FAIL count={c.count} mismatch={keys}"
  IO.println s!"kem-encap-parity: {ok}/{cases.size} cases matched"
  return (if ok == cases.size then 0 else 1)

private def parityDecap (rsp cli : FilePath) : IO UInt32 := do
  if !(← rsp.pathExists) then
    IO.eprintln s!"KEM decap parity: .rsp not found at {rsp}"
    return 2
  if !(← cli.pathExists) then
    IO.eprintln s!"KEM decap parity: CLI not found at {cli}"
    return 2
  let cases ← HeytingLean.Crypto.KAT.parseKEMRSPFile rsp
  if cases.isEmpty then
    IO.eprintln s!"KEM decap parity: no cases parsed from {rsp}"
    return 2
  let tmpDir : FilePath := FilePath.mk ".tmp" / "kem_kat_runner"
  let dirOk ←
    try
      IO.FS.createDirAll tmpDir
      pure true
    catch _ =>
      pure false
  if !dirOk then
    IO.eprintln s!"KEM decap parity: failed to create tmp dir {tmpDir}"
    return 2
  let inPath := tmpDir / "case.in"
  let mut ok : Nat := 0
  for c in cases do
    let payload := s!"ct = {c.ctHex}\nsk = {c.skHex}\nss = {c.ssHex}\n"
    let wrote ←
      try
        IO.FS.writeFile inPath payload
        pure true
      catch _ =>
        pure false
    if !wrote then
      IO.eprintln s!"KEM decap parity: failed to write temp file {inPath}"
      return 2
    let cmd := s!"{shQuote cli.toString} < {shQuote inPath.toString}"
    let out? ←
      try
        let out ← runBash cmd
        pure (some out)
      catch _ =>
        pure none
    match out? with
    | none =>
        IO.eprintln s!"FAIL count={c.count} spawn_error"
        continue
    | some out =>
        if out.exitCode == 0 then
          ok := ok + 1
        else
          IO.eprintln s!"FAIL count={c.count} rc={out.exitCode} err={out.stderr.trim}"
  IO.println s!"kem-decap-parity: {ok}/{cases.size} cases matched"
  return (if ok == cases.size then 0 else 1)

def main (args : List String) : IO UInt32 := do
  if hasFlag "--encap" args then
    match (getFlagValue? "--rsp" args), (getFlagValue? "--cli" args) with
    | some rsp, some cli => parityEncap (FilePath.mk rsp) (FilePath.mk cli)
    | _, _ =>
        IO.eprintln "usage: kem_kat_runner --encap --rsp <file.rsp> --cli <kem_kat_cli>"
        return 2
  else if hasFlag "--decap" args then
    match (getFlagValue? "--rsp" args), (getFlagValue? "--cli" args) with
    | some rsp, some cli => parityDecap (FilePath.mk rsp) (FilePath.mk cli)
    | _, _ =>
        IO.eprintln "usage: kem_kat_runner --decap --rsp <file.rsp> --cli <kem_dec_cli>"
        return 2
  else
    let base := match args.find? (fun a => !a.startsWith "--") with
      | some d => FilePath.mk d
      | none   => katRoot
    let vectors := base / "vectors"
    if !(← vectors.pathExists) then
      IO.println s!"KEM KAT runner: KAT directory not found at {vectors}; skipping"
      return 0

    let dirs := [("kats", vectors / "kats"), ("kats_pqclean", vectors / "kats_pqclean")]
    for (label, dir) in dirs do
      if (← dir.pathExists) then
        let counts ← HeytingLean.Crypto.KAT.countRSPCasesInDir dir
        let total := counts.foldl (init := 0) (fun acc (_, n) => acc + n)
        IO.println s!"KEM KAT runner: {label}: {counts.length} .rsp files totaling {total} cases in {dir}"
      else
        IO.println s!"KEM KAT runner: {label}: directory not found at {dir}"
    return 0

end CLI
end HeytingLean

open HeytingLean CLI

/-- Module entry point required by Lean executables. -/
def main (args : List String) : IO UInt32 :=
  CLI.main args
