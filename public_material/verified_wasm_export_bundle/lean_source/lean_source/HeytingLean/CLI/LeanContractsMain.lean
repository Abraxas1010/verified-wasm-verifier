import Std
import Lean
import Lean.Data.Json
import HeytingLean.CLI.Args
import HeytingLean.Util.SHA
import HeytingLean.Blockchain.Contracts.LeanYulDSL.Spec
import HeytingLean.Blockchain.Contracts.LeanYulDSL.ABI
import HeytingLean.Blockchain.Contracts.LeanYulDSL.Compiler
import HeytingLean.Blockchain.Contracts.LeanYulDSL.Emit
import HeytingLean.Blockchain.Contracts.LeanYulDSL.Verify

/-!
# HeytingLean.CLI.LeanContractsMain

JSON-first CLI for the restricted Lean→Solidity (via inline Yul) lane.

Input: `ContractSpec` JSON
Output: JSON bundle containing emitted Yul object text, Solidity source, hashes,
and a v0 verification report (effect-trace obligations).
-/

open Lean
open HeytingLean.Blockchain.Contracts.LeanYulDSL

private def usage : String :=
  String.intercalate "\n"
    [
      "Usage:",
      "  lean_contracts_cli --spec <spec.json> [--out-dir <dir>] [--allow-unverified]",
      "",
      "Spec format (v0):",
      "  {",
      "    \"version\": \"heyting.contract_spec.v0\",",
      "    \"template\": \"owner|bank|erc20Mini\",",
      "    \"pragma\": \"^0.8.20\",",
      "    \"contractName\": \"OptionalName\",",
      "    \"params\": { ... }",
      "  }",
      "",
      "Notes:",
      "  By default this CLI is strict: if verification fails, it returns nonzero.",
      "  Use --allow-unverified to still emit artifacts (for debugging only).",
    ]

private def getArgValue? (flag : String) (args : List String) : Option String :=
  let rec go : List String → Option String
    | [] => none
    | a :: b :: rest => if a = flag then some b else go (b :: rest)
    | [_] => none
  go args

private def hasFlag (flag : String) (args : List String) : Bool :=
  args.any (fun a => a = flag)

private def errorJson (err : String) : Json :=
  Json.mkObj [("ok", Json.bool false), ("error", Json.str err)]

private def okJson
    (spec : ContractSpec)
    (compiled : CompileResult)
    (yul solidity : String)
    (yulSha solSha : String)
    (verify : VerificationReport) : Json :=
  let abi := HeytingLean.Blockchain.Contracts.LeanYulDSL.abiToJson (HeytingLean.Blockchain.Contracts.LeanYulDSL.abiOfTemplate spec.template)
  Json.mkObj
    [
      ("ok", Json.bool true),
      ("spec", HeytingLean.Blockchain.Contracts.LeanYulDSL.JsonIO.contractSpecToJson spec),
      ("contractName", Json.str compiled.contractName),
      ("pragma", Json.str compiled.pragma),
      ("template", Json.str compiled.spec.template.slug),
      ("abi", abi),
      ("yul_bytes", Json.num yul.toUTF8.size),
      ("yul_sha256", Json.str yulSha),
      ("solidity_bytes", Json.num solidity.toUTF8.size),
      ("solidity_sha256", Json.str solSha),
      ("verify", HeytingLean.Blockchain.Contracts.LeanYulDSL.JsonIO.verificationReportToJson verify),
      ("yul", Json.str yul),
      ("solidity", Json.str solidity),
    ]

def main (argv : List String) : IO UInt32 := do
  let args := HeytingLean.CLI.stripLakeArgs argv
  if args.isEmpty || hasFlag "--help" args || hasFlag "-h" args then
    IO.println usage
    return (0 : UInt32)
  let specPath? := getArgValue? "--spec" args
  let outDir? := getArgValue? "--out-dir" args
  let allowUnverified := hasFlag "--allow-unverified" args
  match specPath? with
  | none =>
      IO.eprintln usage
      return (1 : UInt32)
  | some specPath =>
      try
        let specPath : System.FilePath := specPath
        if !(← specPath.pathExists) then
          IO.println (Json.compress (errorJson s!"spec file not found: {specPath}"))
          return (2 : UInt32)
        let contents ← IO.FS.readFile specPath
        let specJson ←
          match Json.parse contents with
          | Except.ok j => pure j
          | Except.error e =>
              IO.println (Json.compress (errorJson s!"failed to parse spec json: {e}"))
              return (2 : UInt32)
        let spec ←
          match HeytingLean.Blockchain.Contracts.LeanYulDSL.JsonIO.parseContractSpec specJson with
          | Except.ok s => pure s
          | Except.error e =>
              IO.println (Json.compress (errorJson s!"invalid spec: {e}"))
              return (2 : UInt32)
        let compiled ←
          match HeytingLean.Blockchain.Contracts.LeanYulDSL.compile spec with
          | Except.ok r => pure r
          | Except.error e =>
              IO.println (Json.compress (errorJson s!"compile failed: {e}"))
              return (2 : UInt32)
        let yul := yulObjectStringOfParts compiled.parts
        let solidity := solidityWrapperOfParts compiled.parts compiled.pragma compiled.contractName
        let verify ←
          match HeytingLean.Blockchain.Contracts.LeanYulDSL.verifyCompiled compiled with
          | Except.ok rep => pure rep
          | Except.error e =>
              IO.println (Json.compress (errorJson s!"verify failed: {e}"))
              return (2 : UInt32)
        let yulSha ← HeytingLean.Util.sha256HexOfStringIO yul
        let solSha ← HeytingLean.Util.sha256HexOfStringIO solidity

        if !verify.ok && !allowUnverified then
          -- Strict-by-default: do not emit unverified artifacts in production mode.
          IO.println (Json.compress (Json.mkObj
            [ ("ok", Json.bool false)
            , ("error", Json.str "verification_failed")
            , ("verify", HeytingLean.Blockchain.Contracts.LeanYulDSL.JsonIO.verificationReportToJson verify)
            ]))
          return (3 : UInt32)

        match outDir? with
        | none => pure ()
        | some dirStr =>
            let outDir : System.FilePath := dirStr
            IO.FS.createDirAll outDir
            IO.FS.writeFile (outDir / s!"{compiled.contractName}.yul") yul
            IO.FS.writeFile (outDir / s!"{compiled.contractName}.sol") solidity
            let bundle := okJson spec compiled yul solidity yulSha solSha verify
            IO.FS.writeFile (outDir / s!"{compiled.contractName}.bundle.json") (Json.pretty bundle)
            let abi := HeytingLean.Blockchain.Contracts.LeanYulDSL.abiToJson (HeytingLean.Blockchain.Contracts.LeanYulDSL.abiOfTemplate spec.template)
            IO.FS.writeFile (outDir / s!"{compiled.contractName}.abi.json") (Json.pretty abi)
        let bundle := okJson spec compiled yul solidity yulSha solSha verify
        IO.println (Json.compress bundle)
        return (0 : UInt32)
      catch e =>
        IO.println (Json.compress (errorJson s!"exception: {e}"))
        return (2 : UInt32)
