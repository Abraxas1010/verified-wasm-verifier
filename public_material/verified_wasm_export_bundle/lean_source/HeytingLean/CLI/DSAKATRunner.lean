import Lean
import HeytingLean.Crypto.DSA.MLDSA
import HeytingLean.Crypto.RNG.Seeded
import HeytingLean.Crypto.KAT.RSP

namespace HeytingLean
namespace CLI

open System

private def katRoot : FilePath := FilePath.mk ".." / "WIP" / "pqc_lattice" / "kat" / "dilithium"

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
  let tmpDir : FilePath := FilePath.mk ".tmp" / "dsa_kat_runner"
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
  IO.println s!"dsa-kat-parity: {ok}/{cases.size} cases matched"
  return (if ok == cases.size then 0 else 1)

def main (args : List String) : IO UInt32 := do
  if hasFlag "--kat" args then
    match (getFlagValue? "--rsp" args), (getFlagValue? "--sign-cli" args) with
    | some rsp, some cli => parityKAT (FilePath.mk rsp) (FilePath.mk cli)
    | _, _ =>
        IO.eprintln "usage: dsa_kat_runner --kat --rsp <file.rsp> --sign-cli <dsa_sign_cli>"
        return 2
  else
    let base := match args.find? (fun a => !a.startsWith "--") with
      | some d => FilePath.mk d
      | none   => katRoot
    let vectors := base / "vectors"
    if !(← vectors.pathExists) then
      IO.println s!"DSA KAT runner: KAT directory not found at {vectors}; skipping"
      return 0
    let katsDir := vectors / "kats"
    if (← katsDir.pathExists) then
      let counts ← HeytingLean.Crypto.KAT.countRSPCasesInDir katsDir
      let total := counts.foldl (init := 0) (fun acc (_, n) => acc + n)
      IO.println s!"DSA KAT runner: {counts.length} .rsp files totaling {total} cases in {katsDir}"
    else
      IO.println s!"DSA KAT runner: no kats/ directory found under {base}"
    return 0

end CLI
end HeytingLean

open HeytingLean CLI

/-- Module entry point required by Lean executables. -/
def main (args : List String) : IO UInt32 :=
  CLI.main args
