import HeytingLean.Crypto.KEM.MLKEMByteCodec
import HeytingLean.Crypto.VerifiedPQC.RuntimeBoundary

namespace HeytingLean
namespace Crypto
namespace KEM
namespace FIPS203
namespace StandardRuntime

open System

structure KeyPair where
  ek : ByteArray
  dk : ByteArray
  deriving Inhabited

structure EncapResult where
  ciphertext : ByteArray
  sharedSecret : ByteArray
  deriving Inhabited

structure RoundtripReport where
  keyPair : KeyPair
  encapsulation : EncapResult
  decapsulatedSecret : ByteArray
  decapsulationMatches : Bool
  keypairChecks : Bool
  ciphertextCheck : Bool
  deriving Inhabited

private structure ResolvedBackend where
  root : FilePath
  kem : VerifiedPQC.RuntimeKEMBackend

private def shQuote (s : String) : String :=
  "'" ++ (s.replace "'" "'\"'\"'") ++ "'"

private def repoRootCandidates (cwd : FilePath) : List FilePath :=
  let p1 := cwd.parent.getD cwd
  let p2 := p1.parent.getD p1
  [cwd, p1, p2]

private def findRepoRoot : IO (Except String FilePath) := do
  let cwd ← IO.currentDir
  let mut found : Option FilePath := none
  for candidate in repoRootCandidates cwd do
    if found.isNone then
      let pqcRoot := candidate / "WIP" / "pqc_lattice"
      if ← pqcRoot.pathExists then
        found := some candidate
  match found with
  | some root => pure (.ok root)
  | none => pure (.error s!"could not locate repo root from cwd={cwd}")

private def runBash (cmd : String) : IO IO.Process.Output :=
  IO.Process.output { cmd := "/bin/bash", args := #["-lc", cmd] }

private def parseKVLines (txt : String) : List (String × String) :=
  let step (acc : List (String × String)) (raw : String) :=
    let line := raw.trim
    match line.splitOn "=" with
    | k :: v :: _ => (k.trim, v.trim) :: acc
    | _ => acc
  (txt.splitOn "\n").foldl step []

private def kvGet? (key : String) (kvs : List (String × String)) : Option String :=
  (kvs.find? (fun (k, _) => k = key)).map Prod.snd

private def ensureBackend (p : MLKEM203Params) : IO (Except String ResolvedBackend) := do
  match ← findRepoRoot with
  | .error e => pure (.error e)
  | .ok root =>
      let kem := VerifiedPQC.runtimeKEMBackend p
      let buildCmd := s!"cd {shQuote root.toString} && bash {kem.buildScript}"
      let out ← runBash buildCmd
      if out.exitCode = 0 then
        pure (.ok { root := root, kem := kem })
      else
        pure (.error s!"backend build failed ({p.name}): {out.stderr.trim}")

private def withSeedPrefix (seedHex : String) : String :=
  if seedHex.isEmpty then "" else s!"RNG_SEED={shQuote seedHex} "

private def writeTempInput (root : FilePath) (name body : String) : IO FilePath := do
  let dir := root / ".tmp" / "mlkem_standard_runtime"
  IO.FS.createDirAll dir
  let path := dir / name
  IO.FS.writeFile path body
  pure path

private def parseHexField (field : String) (kvs : List (String × String)) : Except String ByteArray := do
  let hex ←
    match kvGet? field kvs with
    | some hex => .ok hex
    | none => .error s!"missing field: {field}"
  match ByteCodec.hexToBytes? hex with
  | some bytes => .ok bytes
  | none => .error s!"invalid hex for field: {field}"

def keygen (p : MLKEM203Params) (seedHex : String := "") : IO (Except String KeyPair) := do
  match ← ensureBackend p with
  | .error e => pure (.error e)
  | .ok resolved =>
      let exe := resolved.root / resolved.kem.keygenCli
      let cmd := s!"cd {shQuote resolved.root.toString} && {withSeedPrefix seedHex}{shQuote exe.toString}"
      let out ← runBash cmd
      if out.exitCode != 0 then
        pure (.error s!"keygen failed ({p.name}): {out.stderr.trim}")
      else
        let kvs := parseKVLines out.stdout
        match parseHexField "pk" kvs, parseHexField "sk" kvs with
        | .ok ek, .ok dk =>
            if ByteCodec.checkStoredKeypair p ek dk then
              pure (.ok { ek := ek, dk := dk })
            else
              pure (.error s!"generated keypair failed local FIPS checks ({p.name})")
        | .error e, _ => pure (.error e)
        | _, .error e => pure (.error e)

def encaps (p : MLKEM203Params) (ek : ByteArray) (seedHex : String := "") :
    IO (Except String EncapResult) := do
  if !ByteCodec.checkEncapsulationKey p ek then
    return .error s!"encapsulation key failed local check ({p.name})"
  match ← ensureBackend p with
  | .error e => pure (.error e)
  | .ok resolved =>
      let exe := resolved.root / resolved.kem.encapCli
      let input ← writeTempInput resolved.root s!"encap_{p.k}.in" s!"pk = {ByteCodec.bytesToHex ek}\n"
      let cmd :=
        s!"cd {shQuote resolved.root.toString} && {withSeedPrefix seedHex}{shQuote exe.toString} < {shQuote input.toString}"
      let out ← runBash cmd
      if out.exitCode != 0 then
        pure (.error s!"encapsulation failed ({p.name}): {out.stderr.trim}")
      else
        let kvs := parseKVLines out.stdout
        match parseHexField "ct" kvs, parseHexField "ss" kvs with
        | .ok ciphertext, .ok sharedSecret =>
            if ByteCodec.checkCiphertext p ciphertext && sharedSecret.size = 32 then
              pure (.ok { ciphertext := ciphertext, sharedSecret := sharedSecret })
            else
              pure (.error s!"encapsulation output failed size checks ({p.name})")
        | .error e, _ => pure (.error e)
        | _, .error e => pure (.error e)

def decaps (p : MLKEM203Params) (dk ciphertext : ByteArray) : IO (Except String ByteArray) := do
  if !ByteCodec.checkDecapsulationKey p dk then
    return .error s!"decapsulation key failed local check ({p.name})"
  if !ByteCodec.checkCiphertext p ciphertext then
    return .error s!"ciphertext failed local size check ({p.name})"
  match ← ensureBackend p with
  | .error e => pure (.error e)
  | .ok resolved =>
      let exe := resolved.root / resolved.kem.decapDumpCli
      let input ←
        writeTempInput resolved.root s!"decap_{p.k}.in"
          s!"ct = {ByteCodec.bytesToHex ciphertext}\nsk = {ByteCodec.bytesToHex dk}\n"
      let cmd := s!"cd {shQuote resolved.root.toString} && {shQuote exe.toString} < {shQuote input.toString}"
      let out ← runBash cmd
      if out.exitCode != 0 then
        pure (.error s!"decapsulation failed ({p.name}): {out.stderr.trim}")
      else
        let kvs := parseKVLines out.stdout
        match parseHexField "ss" kvs with
        | .ok ss =>
            if ss.size = 32 then
              pure (.ok ss)
            else
              pure (.error s!"decapsulation shared secret had wrong size ({p.name})")
        | .error e => pure (.error e)

def roundtrip (p : MLKEM203Params) (keySeed encapSeed : String) :
    IO (Except String RoundtripReport) := do
  match ← keygen p keySeed with
  | .error e => pure (.error e)
  | .ok keyPair =>
      match ← encaps p keyPair.ek encapSeed with
      | .error e => pure (.error e)
      | .ok enc =>
          match ← decaps p keyPair.dk enc.ciphertext with
          | .error e => pure (.error e)
          | .ok decSs =>
              pure (.ok
                { keyPair := keyPair
                  encapsulation := enc
                  decapsulatedSecret := decSs
                  decapsulationMatches := decSs == enc.sharedSecret
                  keypairChecks := ByteCodec.checkStoredKeypair p keyPair.ek keyPair.dk
                  ciphertextCheck := ByteCodec.checkCiphertext p enc.ciphertext })

end StandardRuntime
end FIPS203
end KEM
end Crypto
end HeytingLean
