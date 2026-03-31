import Lean
import Lean.Data.Json
import HeytingLean.Theorems.Core
import HeytingLean.Meta.LeanTT0.Checker
import HeytingLean.Meta.LeanTT0.Core
import HeytingLean.Meta.LeanTT0.Hash
import HeytingLean.Meta.LeanTT0.Merkle
import HeytingLean.Meta.LeanTT0.Trace

namespace HeytingLean.Theorems

open HeytingLean.Meta.LeanTT0
open Lean

/-- Full certificate metadata associated to a theorem block. -/
structure ThmCert where
  cabVersion           : String
  foundationCommitment : String
  rulesRoot            : String
  manifestCommit       : String
  kernelCommitment     : String
  traceRoot            : String
  transcriptRoot       : String
  proofDigest          : String
  deriving Repr

/-- Theorem block paired with its certificate data. -/
structure CertifiedThm where
  block : ThmBlock
  cert  : ThmCert
  deriving Repr

/-- Canonical summary shape used by manifests and APIs. -/
structure CertifiedThmSummary where
  name                 : String
  typeStr              : String
  tags                 : List String
  category             : String
  kind                 : String
  cab_version          : String
  foundationCommitment : String
  rulesRoot            : String
  manifestCommit       : String
  kernelCommitment     : String
  proofDigest          : String
  traceRoot            : String
  transcriptRoot       : String
  deriving Repr, Lean.ToJson

structure ThmManifestEntry where
  name             : String
  type             : String
  tags             : List String
  category         : String
  kind             : String
  cabVersion       : String
  foundationCommit : String
  rulesRoot        : String
  manifestCommit   : String
  kernelCommitment : String
  traceRoot        : String
  transcriptRoot   : String
  proofDigest      : String
  deriving Repr, Lean.ToJson

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
    | c1 :: c2 :: rest =>
        let b := UInt8.ofNat (val c1 * 16 + val c2)
        loop rest (acc.push b)
    | _ => acc
  ByteArray.mk (loop ss.toList #[])

private structure CabSnapshot where
  version : String
  foundation : ByteArray
  foundationHex : String
  rulesRoot : ByteArray
  rulesRootHex : String
  manifestCommit : ByteArray
  manifestCommitHex : String

private def cabPath : System.FilePath :=
  System.FilePath.mk ".." / "artifacts" / "cab.json"

private def kernelPath : System.FilePath :=
  System.FilePath.mk ".." / "artifacts" / "kernel.json"

private def readCab : IO CabSnapshot := do
  if !(← System.FilePath.pathExists cabPath) then
    throw <|
      IO.userError
        s!"cab.json not found at {cabPath}; run `lake exe cab_mint -- --out ../artifacts` first"
  let contents ← IO.FS.readFile cabPath
  let j ← match Json.parse contents with
    | .ok j => pure j
    | .error e => throw <| IO.userError s!"Failed to parse cab.json: {e}"
  let getStr (k : String) : IO String := do
    match j.getObjVal? k with
    | .ok (.str s) => pure s
    | _ => throw <| IO.userError s!"cab.json: missing or invalid '{k}'"
  let version ← getStr "version"
  let foundationHex ← getStr "foundationCommitment"
  let rulesRootHex ← getStr "rulesRoot"
  let manifestCommitHex ← getStr "manifestCommit"
  pure {
    version
    foundation := hexToBA foundationHex
    foundationHex
    rulesRoot := hexToBA rulesRootHex
    rulesRootHex
    manifestCommit := hexToBA manifestCommitHex
    manifestCommitHex
  }

-- Canonical descriptor mirrors KernelCommitMain.
private def kernelDescriptor : String :=
  "Kernel:TT0.kernel:v1;rules=[BetaLamApp,DeltaPrimNatAdd];semantics=det"

private def kernelFallback : ByteArray :=
  sha256 kernelDescriptor.toUTF8

private def readKernelCommit : IO (String × ByteArray) := do
  if !(← System.FilePath.pathExists kernelPath) then
    return (hexOfBA kernelFallback, kernelFallback)
  let contents ← IO.FS.readFile kernelPath
  let j ← match Json.parse contents with
    | .ok j => pure j
    | .error e => throw <| IO.userError s!"Failed to parse kernel.json: {e}"
  match j.getObjVal? "kernelCommitment" with
  | .ok (.str s) => pure (s, hexToBA s)
  | _ => throw <| IO.userError "kernel.json: missing kernelCommitment"

private def theoremCertPayload (b : ThmBlock) : String :=
  let tags := (b.tags.namespaceHint ++ b.tags.lensHint)
  let tagsText := String.intercalate "|" tags
  s!"name={b.id.name};decl={b.declName};type={b.typeStr};kind={b.kind};category={b.category};tags={tagsText}"

private def theoremSeedTerm (b : ThmBlock) : Tm :=
  let digest := sha256 (theoremCertPayload b).toUTF8
  let d0 := (digest.get! 0).toNat
  let d1 := (digest.get! 1).toNat
  let d31 := (digest.get! 31).toNat
  let body := Tm.app (Tm.app Tm.primAdd (.nat (d0 + d1))) (.nat d31)
  Tm.app (Tm.lam "digest" body) (.nat digest.size)

/-- Compute the certificate for a theorem block using the LeanTT0 CAB machinery. -/
def getThmCert (b : ThmBlock) : IO ThmCert := do
  let cab ← readCab
  let (kernelHex, kernelBa) ← readKernelCommit
  let theoremDeclDigest := sha256 (theoremCertPayload b).toUTF8
  let term := theoremSeedTerm b
  let tr := runWithTrace 4 term
  let traceRoot := transcriptRoot tr.steps
  let transcriptRootPoseidon := transcriptRootPoseidon tr.steps
  let proofDigest :=
    Hcat "LoF.Cert|" [cab.rulesRoot, kernelBa, theoremDeclDigest, tr.initialDigest, tr.finalDigest, traceRoot]
  pure {
    cabVersion := cab.version
    foundationCommitment := cab.foundationHex
    rulesRoot := cab.rulesRootHex
    manifestCommit := cab.manifestCommitHex
    kernelCommitment := kernelHex
    traceRoot := hexOfBA traceRoot
    transcriptRoot := hexOfBA transcriptRootPoseidon
    proofDigest := hexOfBA proofDigest
  }

/-- Canonical manifest/API summary for a certified theorem. -/
def toSummary (ct : CertifiedThm) : CertifiedThmSummary :=
  { name                 := toString ct.block.id.name
    typeStr              := ct.block.typeStr
    tags                 := ct.block.tags.namespaceHint ++ ct.block.tags.lensHint
    category             := ct.block.category
    kind                 := HeytingLean.Theorems.kindToString ct.block.kind
    cab_version          := ct.cert.cabVersion
    foundationCommitment := ct.cert.foundationCommitment
    rulesRoot            := ct.cert.rulesRoot
    manifestCommit       := ct.cert.manifestCommit
    kernelCommitment     := ct.cert.kernelCommitment
    proofDigest          := ct.cert.proofDigest
    traceRoot            := ct.cert.traceRoot
    transcriptRoot       := ct.cert.transcriptRoot }

/-- Summarize a certified theorem into the manifest-friendly entry. -/
def summarizeCertifiedThm (ct : CertifiedThm) : ThmManifestEntry :=
  { name             := toString ct.block.id.name
    type             := ct.block.typeStr
    tags             := ct.block.tags.namespaceHint ++ ct.block.tags.lensHint
    category         := ct.block.category
    kind             := HeytingLean.Theorems.kindToString ct.block.kind
    cabVersion       := ct.cert.cabVersion
    foundationCommit := ct.cert.foundationCommitment
    rulesRoot        := ct.cert.rulesRoot
    manifestCommit   := ct.cert.manifestCommit
    kernelCommitment := ct.cert.kernelCommitment
    traceRoot        := ct.cert.traceRoot
    transcriptRoot   := ct.cert.transcriptRoot
    proofDigest      := ct.cert.proofDigest }

/-- Get a certified theorem by name, if present in the registry. -/
def getCertifiedThmByName (n : Name) : IO (Option CertifiedThm) := do
  match findThmByName n with
  | none => pure none
  | some b =>
      let cert ← getThmCert b
      pure (some { block := b, cert := cert })

/-- Enumerate all certified theorems. -/
def allCertifiedThms : IO (Array CertifiedThm) := do
  -- Try full discovery; if it fails (e.g., in minimal C runtime), fall back to seed blocks.
  let arr ← try (allThmBlocksIO : IO (Array ThmBlock)) catch _ => pure seedThmBlocks
  arr.mapM (fun b => do
    let cert ← getThmCert b
    pure { block := b, cert := cert })

end HeytingLean.Theorems
