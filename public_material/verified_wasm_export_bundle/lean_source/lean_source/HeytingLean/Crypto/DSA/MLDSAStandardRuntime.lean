import HeytingLean.Crypto.KEM.MLKEMByteCodec
import HeytingLean.Crypto.VerifiedPQC.RuntimeBoundary

namespace HeytingLean
namespace Crypto
namespace DSA
namespace FIPS204
namespace StandardRuntime

open System

structure FreshSignature where
  publicKey : ByteArray
  secretKey : ByteArray
  message : ByteArray
  signedMessage : ByteArray
  deriving Inhabited

structure FreshDetachedSignature where
  publicKey : ByteArray
  secretKey : ByteArray
  message : ByteArray
  signature : ByteArray
  deriving Inhabited

private structure ResolvedBackend where
  root : FilePath
  dsa : VerifiedPQC.RuntimeDSABackend

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

private def ensureBackend (p : MLDSA204Params) : IO (Except String ResolvedBackend) := do
  match ← findRepoRoot with
  | .error e => pure (.error e)
  | .ok root =>
      let dsa := VerifiedPQC.runtimeDSABackend p
      let buildCmd := s!"cd {shQuote root.toString} && bash {dsa.buildScript}"
      let out ← runBash buildCmd
      if out.exitCode = 0 then
        pure (.ok { root := root, dsa := dsa })
      else
        pure (.error s!"backend build failed ({p.name}): {out.stderr.trim}")

private def withSeedPrefix (seedHex : String) : String :=
  if seedHex.isEmpty then "" else s!"RNG_SEED={shQuote seedHex} "

private def writeTempInput (root : FilePath) (name body : String) : IO FilePath := do
  let dir := root / ".tmp" / "mldsa_standard_runtime"
  IO.FS.createDirAll dir
  let path := dir / name
  IO.FS.writeFile path body
  pure path

private def parseHexField (field : String) (kvs : List (String × String)) : Except String ByteArray := do
  let hex ←
    match kvGet? field kvs with
    | some hex => .ok hex
    | none => .error s!"missing field: {field}"
  match KEM.FIPS203.ByteCodec.hexToBytes? hex with
  | some bytes => .ok bytes
  | none => .error s!"invalid hex for field: {field}"

private def takeBytes (bytes : ByteArray) (n : Nat) : ByteArray :=
  ByteArray.mk (bytes.data.extract 0 n)

private def dropBytes (bytes : ByteArray) (n : Nat) : ByteArray :=
  ByteArray.mk (bytes.data.extract n bytes.size)

private def appendBytes (a b : ByteArray) : ByteArray :=
  ByteArray.mk (a.data ++ b.data)

def publicKeyBytes (p : MLDSA204Params) : Nat :=
  match p.k with
  | 4 => 1312
  | 6 => 1952
  | _ => 2592

def secretKeyBytes (p : MLDSA204Params) : Nat :=
  match p.k with
  | 4 => 2560
  | 6 => 4032
  | _ => 4896

def detachedSignatureBytes (p : MLDSA204Params) : Nat :=
  match p.k with
  | 4 => 2420
  | 6 => 3309
  | _ => 4627

private def checkPublicKey (p : MLDSA204Params) (publicKey : ByteArray) : Bool :=
  publicKey.size = publicKeyBytes p

private def checkSecretKey (p : MLDSA204Params) (secretKey : ByteArray) : Bool :=
  secretKey.size = secretKeyBytes p

private def checkSignedMessage (p : MLDSA204Params) (message signedMessage : ByteArray) : Bool :=
  signedMessage.size = message.size + detachedSignatureBytes p

def checkDetachedSignature (p : MLDSA204Params) (signature : ByteArray) : Bool :=
  signature.size = detachedSignatureBytes p

def attachSignature (message signature : ByteArray) : ByteArray :=
  appendBytes signature message

def splitDetachedSignature? (p : MLDSA204Params) (message signedMessage : ByteArray) : Option ByteArray :=
  let sigLen := detachedSignatureBytes p
  if checkSignedMessage p message signedMessage then
    let signature := takeBytes signedMessage sigLen
    let recoveredMessage := dropBytes signedMessage sigLen
    if recoveredMessage = message && checkDetachedSignature p signature then
      some signature
    else
      none
  else
    none

/-- Native ML-DSA signer path currently exposed by the vendored runtime CLIs.

The signer CLI generates a keypair and an attached signature in one call; this wrapper preserves
that contract explicitly rather than pretending we already have a secret-key-only signer surface. -/
def keygenSignAttached (p : MLDSA204Params) (msg : ByteArray) (seedHex : String := "") :
    IO (Except String FreshSignature) := do
  match ← ensureBackend p with
  | .error e => pure (.error e)
  | .ok resolved =>
      let exe := resolved.root / resolved.dsa.signCli
      let input ←
        writeTempInput resolved.root s!"sign_{p.k}.in"
          s!"msg = {KEM.FIPS203.ByteCodec.bytesToHex msg}\n"
      let cmd :=
        s!"cd {shQuote resolved.root.toString} && {withSeedPrefix seedHex}{shQuote exe.toString} < {shQuote input.toString}"
      let out ← runBash cmd
      if out.exitCode != 0 then
        pure (.error s!"sign failed ({p.name}): {out.stderr.trim}")
      else
        let kvs := parseKVLines out.stdout
        match parseHexField "pk" kvs, parseHexField "sk" kvs,
            parseHexField "msg" kvs, parseHexField "sm" kvs with
        | .ok publicKey, .ok secretKey, .ok echoedMsg, .ok signedMessage =>
            if echoedMsg == msg &&
                checkPublicKey p publicKey &&
                checkSecretKey p secretKey &&
                checkSignedMessage p echoedMsg signedMessage then
              pure (.ok
                { publicKey := publicKey
                  secretKey := secretKey
                  message := echoedMsg
                  signedMessage := signedMessage })
            else
              pure (.error s!"sign output failed local size/message checks ({p.name})")
        | .error e, _, _, _ => pure (.error e)
        | _, .error e, _, _ => pure (.error e)
        | _, _, .error e, _ => pure (.error e)
        | _, _, _, .error e => pure (.error e)

/-- Native detached-signature wrapper derived from the runtime's attached-signature layout. -/
def keygenSignDetached (p : MLDSA204Params) (msg : ByteArray) (seedHex : String := "") :
    IO (Except String FreshDetachedSignature) := do
  match ← keygenSignAttached p msg seedHex with
  | .error e => pure (.error e)
  | .ok signed =>
      match splitDetachedSignature? p signed.message signed.signedMessage with
      | some signature =>
          pure (.ok
            { publicKey := signed.publicKey
              secretKey := signed.secretKey
              message := signed.message
              signature := signature })
      | none =>
          pure (.error s!"could not derive detached signature from attached output ({p.name})")

/-- Native ML-DSA attached-signature verification through the vendored runtime open CLI. -/
def openSignedMessage (p : MLDSA204Params) (publicKey signedMessage message : ByteArray) :
    IO (Except String Unit) := do
  if !checkPublicKey p publicKey then
    return .error s!"public key failed local size check ({p.name})"
  if !checkSignedMessage p message signedMessage then
    return .error s!"signed message failed local size check ({p.name})"
  match ← ensureBackend p with
  | .error e => pure (.error e)
  | .ok resolved =>
      let exe := resolved.root / resolved.dsa.openCli
      let input ←
        writeTempInput resolved.root s!"open_{p.k}.in"
          (String.intercalate "\n"
            [ s!"pk = {KEM.FIPS203.ByteCodec.bytesToHex publicKey}"
            , s!"mlen = {message.size}"
            , s!"smlen = {signedMessage.size}"
            , s!"msg = {KEM.FIPS203.ByteCodec.bytesToHex message}"
            , s!"sm = {KEM.FIPS203.ByteCodec.bytesToHex signedMessage}"
            , ""
            ])
      let cmd := s!"cd {shQuote resolved.root.toString} && {shQuote exe.toString} < {shQuote input.toString}"
      let out ← runBash cmd
      if out.exitCode = 0 then
        pure (.ok ())
      else
        pure (.error s!"open failed ({p.name}): {out.stderr.trim}")

/-- Detached verification wrapper derived from the runtime's attached-signature open path. -/
def verifyDetached (p : MLDSA204Params) (publicKey signature message : ByteArray) :
    IO (Except String Unit) := do
  if !checkDetachedSignature p signature then
    return .error s!"detached signature failed local size check ({p.name})"
  openSignedMessage p publicKey (attachSignature message signature) message

end StandardRuntime
end FIPS204
end DSA
end Crypto
end HeytingLean
