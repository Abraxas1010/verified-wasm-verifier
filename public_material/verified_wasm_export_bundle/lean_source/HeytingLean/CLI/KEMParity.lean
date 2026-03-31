import Lean
import HeytingLean.Crypto.KEM.MLKEM
import HeytingLean.Crypto.KAT.RSP

/-!
kem_parity: convenience runner to execute Kyber/ML-KEM `.rsp` parity checks via the C CLIs.

Default invocation (no args) is a no-op and exits 0 so it is safe for generic smoke runners.
-/

open System

private def wipRoot : FilePath :=
  FilePath.mk ".." / "WIP" / "pqc_lattice"

private def katsDir : FilePath :=
  wipRoot / "kat" / "kyber" / "vectors" / "kats"

private def outDir : FilePath :=
  wipRoot / "out"

private def suffixOfKatBits (bits : Nat) : String :=
  if bits == 1632 then "512"
  else if bits == 2400 then "768"
  else if bits == 3168 then "1024"
  else toString bits

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
  IO.println s!"kem-encap-parity: {ok}/{cases.size} cases matched ({rsp.fileName.getD rsp.toString})"
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
  let tmpDir : FilePath := FilePath.mk ".tmp" / "kem_parity"
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
  IO.println s!"kem-decap-parity: {ok}/{cases.size} cases matched ({rsp.fileName.getD rsp.toString})"
  return (if ok == cases.size then 0 else 1)

def main (args : List String) : IO UInt32 := do
  if args.isEmpty || args.any (· == "--help") then
    IO.println "kem_parity: pass --all | --encap-all | --decap-all (uses WIP/pqc_lattice paths)"
    return 0

  let doEncap := args.any (· == "--all") || args.any (· == "--encap-all")
  let doDecap := args.any (· == "--all") || args.any (· == "--decap-all")
  if !(doEncap || doDecap) then
    IO.eprintln "kem_parity: no mode selected (use --all | --encap-all | --decap-all)"
    return 2

  let mut finalRc : UInt32 := 0
  for p in HeytingLean.Crypto.KEM.all do
    let suffix := suffixOfKatBits p.katBits
    let rsp := katsDir / HeytingLean.Crypto.KEM.katFileName p
    let cliEnc := outDir / s!"kem_kat_cli_{suffix}"
    let cliDec := outDir / s!"kem_dec_cli_{suffix}"
    if doEncap then
      let rc ← parityEncap rsp cliEnc
      if rc != 0 then finalRc := rc
    if doDecap then
      let rc ← parityDecap rsp cliDec
      if rc != 0 then finalRc := rc

  return finalRc

