import Lean
import HeytingLean.Crypto.DSA.MLDSA
import HeytingLean.Crypto.KAT.RSP

/-!
dsa_parity: convenience runner to execute Dilithium/ML-DSA `.rsp` signature KAT parity via the C CLIs.

Default invocation (no args) is a no-op and exits 0 so it is safe for generic smoke runners.
-/

open System

private def wipRoot : FilePath :=
  FilePath.mk ".." / "WIP" / "pqc_lattice"

private def katsDir : FilePath :=
  wipRoot / "kat" / "dilithium" / "vectors" / "kats"

private def outDir : FilePath :=
  wipRoot / "out"

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

private def parityKAT (rsp signCli : FilePath) : IO UInt32 := do
  if !(← rsp.pathExists) then
    IO.eprintln s!"DSA KAT parity: .rsp not found at {rsp}"
    return 2
  if !(← signCli.pathExists) then
    IO.eprintln s!"DSA KAT parity: signer CLI not found at {signCli}"
    return 2
  let cases ← HeytingLean.Crypto.KAT.parseDSARSPFile rsp
  if cases.isEmpty then
    IO.eprintln s!"DSA KAT parity: no cases parsed from {rsp}"
    return 2
  let tmpDir : FilePath := FilePath.mk ".tmp" / "dsa_parity"
  let dirOk ←
    try
      IO.FS.createDirAll tmpDir
      pure true
    catch _ =>
      pure false
  if !dirOk then
    IO.eprintln s!"DSA KAT parity: failed to create tmp dir {tmpDir}"
    return 2
  let inPath := tmpDir / "case.in"
  let mut ok : Nat := 0
  for c in cases do
    let seed := HeytingLean.Crypto.KAT.normHex c.seedHex
    let payload := s!"msg = {c.msgHex}\n"
    let wrote ←
      try
        IO.FS.writeFile inPath payload
        pure true
      catch _ =>
        pure false
    if !wrote then
      IO.eprintln s!"DSA KAT parity: failed to write temp file {inPath}"
      return 2
    let cmd := s!"RNG_SEED={shQuote seed} {shQuote signCli.toString} < {shQuote inPath.toString}"
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
          let gotMsg := (kvGet? "msg" kvs).getD ""
          let gotSm := (kvGet? "sm" kvs).getD ""
          let gotMlen := (kvGet? "mlen" kvs).getD ""
          let gotSmlen := (kvGet? "smlen" kvs).getD ""
          let mismHex :=
            [ ("pk", gotPk, c.pkHex)
            , ("sk", gotSk, c.skHex)
            , ("msg", gotMsg, c.msgHex)
            , ("sm", gotSm, c.smHex)
            ].filter (fun (_, g, e) => HeytingLean.Crypto.KAT.normHex g != HeytingLean.Crypto.KAT.normHex e)
          let mismNum :=
            [ ("mlen", gotMlen, c.mlen)
            , ("smlen", gotSmlen, c.smlen)
            ].filter (fun (_, g, e) => g.toNat?.getD 0 != e)
          let mismKeys := (mismHex.map (fun (k, _, _) => k)) ++ (mismNum.map (fun (k, _, _) => k))
          if mismKeys.isEmpty then
            ok := ok + 1
          else
            IO.eprintln s!"FAIL count={c.count} mismatch={mismKeys}"
  IO.println s!"dsa-kat-parity: {ok}/{cases.size} cases matched ({rsp.fileName.getD rsp.toString})"
  return (if ok == cases.size then 0 else 1)

def main (args : List String) : IO UInt32 := do
  if args.isEmpty || args.any (· == "--help") then
    IO.println "dsa_parity: pass --all (uses WIP/pqc_lattice paths)"
    return 0
  if !(args.any (· == "--all")) then
    IO.eprintln "dsa_parity: no mode selected (use --all)"
    return 2
  let mut finalRc : UInt32 := 0
  for p in HeytingLean.Crypto.DSA.all do
    let rsp := katsDir / HeytingLean.Crypto.DSA.katFileName p
    let cli := outDir / HeytingLean.Crypto.DSA.signCliName p
    let rc ← parityKAT rsp cli
    if rc != 0 then
      finalRc := rc
  return finalRc

