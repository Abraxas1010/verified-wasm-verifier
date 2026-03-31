import Lean
import Lean.Data.Json
import HeytingLean.CLI.Args
import HeytingLean.KernelAssurance.ICCBridgeAttestation
import HeytingLean.KernelAssurance.ObligationCABZKManifest
import HeytingLean.LoF.LeanKernel.VerifierObligationJson

namespace HeytingLean
namespace CLI
namespace KernelObligationAssuranceMintMain

open Lean
open HeytingLean.KernelAssurance
open HeytingLean.LoF.LeanKernel

structure CliArgs where
  artifactPath : System.FilePath := "kernel_obligations.json"
  payloadPath : Option System.FilePath := none
  outPath : System.FilePath := "kernel_obligation_assurance_manifest.json"
  cabZkOutPath : Option System.FilePath := none
  iccExportPath : Option System.FilePath := none
  iccNoLossPath : Option System.FilePath := none
  iccBridgeOutPath : Option System.FilePath := none
  requested : AssuranceTier := .slice_replayed
  foundationCommitment : Option String := none
  rulesRoot : Option String := none
  kernelCommitment : Option String := none
  zkProofSystem : String := ""
  zkCircuitKind : String := ""
  zkReceiptDigest : String := ""
  zkPublicInputDigest : String := ""
  zkVerifierDigest : String := ""
  zkExecutionClaim : String := ""
  deriving Inhabited

private def usage : String :=
  String.intercalate "\n"
    [ "kernel_obligation_assurance_mint - mint a CAB-aligned manifest over verified_check SKY obligation artifacts"
    , ""
    , "Usage:"
    , "  lake exe kernel_obligation_assurance_mint -- --artifact kernel_obligations.json --claim slice_replayed"
    , ""
    , "Options:"
    , "  --artifact <path>"
    , "  --payload <path>"
    , "  --out <path>"
    , "  --claim <none|slice_replayed|slice_checker_certified>"
    , "  --foundation <hex>"
    , "  --rules-root <hex>"
    , "  --kernel <hex>"
    , "  --cab-zk-out <path>"
    , "  --icc-export <path>"
    , "  --icc-no-loss <path>"
    , "  --icc-bridge-out <path>"
    , "  --zk-proof-system <name>"
    , "  --zk-circuit-kind <name>"
    , "  --zk-receipt-digest <hex>"
    , "  --zk-public-input-digest <hex>"
    , "  --zk-verifier-digest <hex>"
    , "  --zk-execution-claim <text>"
    ]

private partial def parseArgs (args : List String) (cfg : CliArgs := default) : Except String CliArgs := do
  match args with
  | [] => pure cfg
  | "--" :: rest => parseArgs rest cfg
  | "--help" :: _ => throw "help"
  | "--artifact" :: path :: rest => parseArgs rest { cfg with artifactPath := path }
  | "--payload" :: path :: rest => parseArgs rest { cfg with payloadPath := some path }
  | "--out" :: path :: rest => parseArgs rest { cfg with outPath := path }
  | "--cab-zk-out" :: path :: rest => parseArgs rest { cfg with cabZkOutPath := some path }
  | "--icc-export" :: path :: rest => parseArgs rest { cfg with iccExportPath := some path }
  | "--icc-no-loss" :: path :: rest => parseArgs rest { cfg with iccNoLossPath := some path }
  | "--icc-bridge-out" :: path :: rest => parseArgs rest { cfg with iccBridgeOutPath := some path }
  | "--claim" :: claim :: rest =>
      match AssuranceTier.ofString? claim with
      | some requested => parseArgs rest { cfg with requested := requested }
      | none => throw s!"unknown claim tier: {claim}"
  | "--foundation" :: value :: rest => parseArgs rest { cfg with foundationCommitment := some value }
  | "--rules-root" :: value :: rest => parseArgs rest { cfg with rulesRoot := some value }
  | "--kernel" :: value :: rest => parseArgs rest { cfg with kernelCommitment := some value }
  | "--zk-proof-system" :: value :: rest => parseArgs rest { cfg with zkProofSystem := value }
  | "--zk-circuit-kind" :: value :: rest => parseArgs rest { cfg with zkCircuitKind := value }
  | "--zk-receipt-digest" :: value :: rest => parseArgs rest { cfg with zkReceiptDigest := value }
  | "--zk-public-input-digest" :: value :: rest => parseArgs rest { cfg with zkPublicInputDigest := value }
  | "--zk-verifier-digest" :: value :: rest => parseArgs rest { cfg with zkVerifierDigest := value }
  | "--zk-execution-claim" :: value :: rest => parseArgs rest { cfg with zkExecutionClaim := value }
  | bad :: _ => throw s!"unknown arg: {bad}"

private def readArtifact (path : System.FilePath) : IO VerifierArtifact := do
  let contents ← IO.FS.readFile path
  let json ←
    match Json.parse contents with
    | .ok json => pure json
    | .error err => throw <| IO.userError s!"failed to parse JSON artifact: {err}"
  match HeytingLean.LoF.LeanKernel.parseVerifierArtifact json with
  | .ok artifact => pure artifact
  | .error err => throw <| IO.userError s!"failed to decode verifier artifact: {err}"

private def readJsonFile (path : System.FilePath) : IO Json := do
  let contents ← IO.FS.readFile path
  match Json.parse contents with
  | .ok json => pure json
  | .error err => throw <| IO.userError s!"failed to parse JSON file: {err}"

private def readObjField? (path : System.FilePath) (field : String) : IO (Option String) := do
  if !(← path.pathExists) then
    return none
  let contents ← IO.FS.readFile path
  let json ←
    match Json.parse contents with
    | .ok json => pure json
    | .error _ => return none
  match json.getObjVal? field with
  | .ok (.str value) => pure (some value)
  | _ => pure none

private def readCommitments (args : CliArgs) : IO (String × String × String) := do
  let foundation ←
    match args.foundationCommitment with
    | some value => pure value
    | none => pure ((← readObjField? (System.FilePath.mk "../artifacts/cab.json") "foundationCommitment").getD "0x")
  let rulesRoot ←
    match args.rulesRoot with
    | some value => pure value
    | none => pure ((← readObjField? (System.FilePath.mk "../artifacts/cab.json") "rulesRoot").getD "0x")
  let kernelCommitment ←
    match args.kernelCommitment with
    | some value => pure value
      | none => pure ((← readObjField? (System.FilePath.mk "../artifacts/kernel.json") "kernelCommitment").getD "0x")
  pure (foundation, rulesRoot, kernelCommitment)

private def missingZKReceiptFields (args : CliArgs) : List String :=
  let missing : List String := []
  let missing := if args.zkProofSystem.isEmpty then "--zk-proof-system" :: missing else missing
  let missing := if args.zkCircuitKind.isEmpty then "--zk-circuit-kind" :: missing else missing
  let missing := if args.zkReceiptDigest.isEmpty then "--zk-receipt-digest" :: missing else missing
  let missing := if args.zkPublicInputDigest.isEmpty then "--zk-public-input-digest" :: missing else missing
  let missing := if args.zkVerifierDigest.isEmpty then "--zk-verifier-digest" :: missing else missing
  missing.reverse

private def optionalZKReceipt (base : KernelObligationAssuranceManifest) (args : CliArgs) :
    Option ZKReceiptMetadata :=
  if args.cabZkOutPath.isNone then
    none
  else
    some {
      proofSystem := args.zkProofSystem
      circuitKind := args.zkCircuitKind
      checkerDigest := checkerDigestOfManifest base
      bundleDigest := base.bundleDigest
      receiptDigest := args.zkReceiptDigest
      publicInputDigest := args.zkPublicInputDigest
      verifierDigest := args.zkVerifierDigest
      executionClaim := args.zkExecutionClaim
      claimBoundary := ""
    }

def mainImpl (argv : List String) : IO UInt32 := do
  let args ←
    match parseArgs (HeytingLean.CLI.stripLakeArgs argv) with
    | .ok a => pure a
    | .error "help" =>
        IO.println usage
        return 0
    | .error e =>
        throw <| IO.userError e
  if args.cabZkOutPath.isSome then
    let missing := missingZKReceiptFields args
    if !missing.isEmpty then
      throw <| IO.userError s!"--cab-zk-out requires concrete receipt metadata; missing: {String.intercalate ", " missing}"
  let artifact ← readArtifact args.artifactPath
  let sourcePayload? ← args.payloadPath.mapM readJsonFile
  let iccExport? ← args.iccExportPath.mapM readJsonFile
  let iccNoLoss? ← args.iccNoLossPath.mapM readJsonFile
  let bundle := ObligationSliceBundle.ofArtifact artifact
  let (foundationCommitment, rulesRoot, kernelCommitment) ← readCommitments args
  let manifest :=
    KernelObligationAssuranceManifest.ofBundle
      bundle foundationCommitment rulesRoot kernelCommitment args.requested sourcePayload?
  IO.FS.writeFile args.outPath (Lean.toJson manifest).pretty
  IO.println s!"Wrote kernel obligation assurance manifest to {args.outPath}"
  IO.println s!"Granted tier: {manifest.tierDecision.granted}"
  let iccBridgeManifest? : Option KernelObligationICCBridgeManifest :=
    match iccExport?, iccNoLoss? with
    | some iccExport, some iccNoLoss =>
        some <| KernelObligationICCBridgeManifest.ofBase manifest iccExport iccNoLoss sourcePayload?
    | _, _ => none
  match args.cabZkOutPath with
  | some cabZkOutPath =>
      let cabZkManifest :=
        let base := KernelObligationCABZKManifest.ofBase manifest (optionalZKReceipt manifest args)
        let iccAttestation? := iccBridgeManifest?.map
          fun (m : KernelObligationICCBridgeManifest) => m.bridge
        { base with iccBridgeAttestation := iccAttestation? }
      IO.FS.writeFile cabZkOutPath (Lean.toJson cabZkManifest).pretty
      IO.println s!"Wrote kernel obligation CAB-ZK manifest to {cabZkOutPath}"
      IO.println s!"CAB-ZK mode: {cabZkManifest.assuranceMode}"
  | none =>
      pure ()
  match args.iccBridgeOutPath with
  | some iccBridgeOutPath =>
      match iccBridgeManifest? with
      | some bridgeManifest =>
          IO.FS.writeFile iccBridgeOutPath (Lean.toJson bridgeManifest).pretty
          IO.println s!"Wrote kernel obligation ICC bridge manifest to {iccBridgeOutPath}"
          IO.println s!"ICC bridge attested: {bridgeManifest.bridge.attested}"
      | none =>
          if iccExport?.isNone then
            throw <| IO.userError "--icc-bridge-out requires --icc-export"
          else
            throw <| IO.userError "--icc-bridge-out requires --icc-no-loss"
  | none =>
      pure ()
  return 0

end KernelObligationAssuranceMintMain
end CLI
end HeytingLean

def main (argv : List String) : IO UInt32 :=
  HeytingLean.CLI.KernelObligationAssuranceMintMain.mainImpl argv
