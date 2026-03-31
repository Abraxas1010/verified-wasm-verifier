import Lean
import Lean.Data.Json
import HeytingLean.Crypto.Form
import HeytingLean.Crypto.BoolLens
import HeytingLean.Crypto.ZK.R1CSBool
import HeytingLean.Crypto.ZK.R1CSBoolEnv
import HeytingLean.Crypto.ZK.Export
import HeytingLean.Payments.Types
import HeytingLean.Payments.Rules
import HeytingLean.Payments.Commit
import HeytingLean.Payments.Merkle
import HeytingLean.Util.SHA
import HeytingLean.CLI.Args

namespace HeytingLean
namespace Payments
namespace CLI
namespace PMProve

open IO
open Lean
open Crypto
open Crypto.BoolLens

private def readFileE (path : System.FilePath) : IO (Except String String) := do
  try let s ← FS.readFile path; pure (.ok s) catch e => pure (.error s!"read error at {path}: {e}")

private def writeFile (path : System.FilePath) (content : String) : IO Unit :=
  FS.writeFile path content

private def parseJsonE (raw : String) : Except String Json :=
  match Json.parse raw with
  | .ok j => .ok j
  | .error e => .error e

private def findOpt (opts : List String) (pref : String) : Option String :=
  match opts.find? (fun s => s.startsWith pref) with
  | none => none
  | some s =>
      let parts := s.splitOn "="
      if parts.length = 2 then some (parts[1]!) else none

/- Boolean formula over 4 variables: a ∧ b ∧ c ∧ d -/
def policyFormula4 : Crypto.Form 4 :=
  let v (i : Fin 4) := Crypto.Form.var i
  let a : Crypto.Form 4 := v ⟨0, by decide⟩
  let b : Crypto.Form 4 := v ⟨1, by decide⟩
  let c : Crypto.Form 4 := v ⟨2, by decide⟩
  let d : Crypto.Form 4 := v ⟨3, by decide⟩
  Crypto.Form.and (Crypto.Form.and a b) (Crypto.Form.and c d)

/- Build Env 4 from flags in order: [allowedRecipient, amountOkPerTx, perWindowOk, budgetOk] -/
def env4 (f0 f1 f2 f3 : Bool) : BoolLens.Env 4 := fun i =>
  match i.1 with
  | 0 => f0
  | 1 => f1
  | 2 => f2
  | 3 => f3
  | _ => false

/- Compose public.json according to the Payments schema in the repository docs. -/
def mkPublicJson
  (chainId : String)
  (paymentManager : String)
  (walletAddress : Option String)
  (req : Payments.Request)
  (policyC : String)
  (statePreC : String)
  (statePostC : String)
  (nullifier : String)
  (outputIndex : Nat)
  (envIndices : List Nat)
  : Json :=
  let envIdxsJ : Json :=
    Json.arr (envIndices.map (fun n => Json.num n)).toArray
  let base := [
    ("chainId", Json.str chainId),
    ("paymentManager", Json.str paymentManager),
    ("hashedId", Json.str req.hashedId),
    ("policyCommitment", Json.str policyC),
    ("stateCommitment_pre", Json.str statePreC),
    ("stateCommitment_post", Json.str statePostC),
    ("epoch", Json.num req.epoch),
    ("recipient", Json.str req.recipient),
    ("amount", Json.str req.amount),
    ("budget_id", Json.str req.budget_id),
    ("nullifier", Json.str nullifier),
    ("output_index", Json.num outputIndex),
    ("env_indices", envIdxsJ)
  ]
  let withWallet := match walletAddress with
    | some w => ("walletAddress", Json.str w) :: base
    | none => base
  Json.mkObj withWallet

def getEnvOr (k defv : String) : IO String := do
  return (← IO.getEnv k).getD defv

def writeCertificate (outDir : String) (policyCanon : String) (r1csJson : String) : IO Unit := do
  let canonHash ← HeytingLean.Util.sha256HexOfStringIO policyCanon
  let r1csHash ← HeytingLean.Util.sha256HexOfStringIO r1csJson
  let toolchainPath := System.FilePath.mk "lean-toolchain"
  let toolHash ← HeytingLean.Util.sha256HexOfFileIO toolchainPath
  -- Best-effort git sha
  let gitOut ← IO.Process.output { cmd := "git", args := #["rev-parse", "HEAD"] }
  let gitSha := if gitOut.exitCode == 0 then gitOut.stdout.trim else ""
  let cert := Lean.Json.mkObj
    [ ("canonical_semantics_hash", Json.str canonHash)
    , ("compiled_system_hash", Json.str r1csHash)
    , ("poseidon_params_id", Json.str "BN254-v1")
    , ("lean_toolchain_hash", Json.str toolHash)
    , ("git_sha", Json.str gitSha)
    ]
  let path := (System.FilePath.mk outDir) / "certificate.json"
  IO.FS.writeFile path (cert.compress)

def main (args : List String) : IO UInt32 := do
  let args := HeytingLean.CLI.stripLakeArgs args
  match args with
  | policyPath :: statePath :: requestPath :: outDir :: opts =>
      -- IO load
      let polRaw ← match (← readFileE policyPath) with | .ok s => pure s | .error m => eprintln m; return 1
      let stRaw  ← match (← readFileE statePath)  with | .ok s => pure s | .error m => eprintln m; return 1
      let rqRaw  ← match (← readFileE requestPath) with | .ok s => pure s | .error m => eprintln m; return 1
      -- Parse JSON
      let polJ ← match parseJsonE polRaw with | .ok j => pure j | .error e => eprintln e; return 1
      let stJ  ← match parseJsonE stRaw  with | .ok j => pure j | .error e => eprintln e; return 1
      let rqJ  ← match parseJsonE rqRaw  with | .ok j => pure j | .error e => eprintln e; return 1
      -- Decode domain models
      let pol ← match Payments.JsonCodec.parsePolicy polJ with | .ok p => pure p | .error e => eprintln e; return 1
      let st  ← match Payments.JsonCodec.parseState stJ with  | .ok s => pure s | .error e => eprintln e; return 1
      let req ← match Payments.JsonCodec.parseRequest rqJ with | .ok r => pure r | .error e => eprintln e; return 1
      -- Verified membership (optional / for mode=verified require proof)
      let envOpt ← IO.getEnv "PAY_VERIFIED_PROOF_PATH"
      let cliOpt := findOpt opts "--verified-proof="
      let verProofPath := match cliOpt with | some s => some s | none => envOpt
      let reqWithVerified ←
        if pol.allowedRecipientsMode == "verified" then
          match verProofPath with
          | some vp =>
              let raw ← match (← readFileE (System.FilePath.mk vp)) with | .ok s => pure s | .error m => eprintln m; return 1
              let j ← match Json.parse raw with | .ok j => pure j | .error e => eprintln e; return 1
              let v ← match Payments.Merkle.parseVProofE j with | .ok v => pure v | .error e => eprintln e; return 1
              let (ok, _root) ← Payments.Merkle.verifyMembershipIO v
              if ¬ ok || v.recipient != req.recipient then
                eprintln "verified membership check failed"; return 2
              else
                match pol.verifiedRoot with
                | some r => if r != v.root then eprintln "verified root mismatch vs policy"; return 2 else pure { req with verifiedOk := some true }
                | none => eprintln "policy missing verifiedRoot for verified mode"; return 2
          | none =>
              eprintln "policy mode=verified but no --verified-proof provided"; return 2
        else
          pure req
      -- Compute checks and next state
      let checks := Payments.Rules.computeChecks pol st reqWithVerified
      let st' := Payments.Rules.applyRequest pol st reqWithVerified
      -- Build commitments (prefer external Poseidon when available)
      let policyC ← Payments.Commit.commitPolicyIO pol
      let statePreC ← Payments.Commit.commitStateIO st
      let statePostC ← Payments.Commit.commitStateIO st'
      -- Build nullifier
      let nullifier ← Payments.Commit.computeNullifierIO req.hashedId statePreC req.epoch
      -- Compose boolean circuit for checks and compile to R1CS
      let φ := policyFormula4
      let ρ : BoolLens.Env 4 := env4 checks.allowedRecipient checks.amountOkPerTx checks.perWindowOk checks.budgetOk
      let compiledWithMap := Crypto.ZK.R1CSBoolEnv.compileWithEnvMap φ ρ
      let compiled := compiledWithMap.fst
      let envMap := compiledWithMap.snd
      -- Export R1CS and witness JSON
      let idxFor (i : Nat) : Nat :=
        match envMap.find? (fun p => p.fst = i) with
        | some p => p.snd
        | none => 0
      let envIdxs : List Nat := [idxFor 0, idxFor 1, idxFor 2, idxFor 3]
      let metaJ := Json.mkObj
        [ ("output_index", Json.num compiled.output)
        , ("env_indices", Json.arr (envIdxs.map (fun n => Json.num n)).toArray)
        ]
      let sysJ :=
        (Crypto.ZK.Export.systemToJson compiled.system).mergeObj
          (Json.mkObj [("meta", metaJ)])
      let r1csJson := sysJ.compress
      let maxVar := compiled.system.constraints.foldl (init := 0) (fun m c =>
        let step := fun acc (ts : List (Crypto.ZK.Var × ℚ)) => ts.foldl (fun a p => Nat.max a p.fst) acc
        let m1 := step 0 c.A.terms; let m2 := step m1 c.B.terms; let m3 := step m2 c.C.terms; Nat.max m m3)
      let numVars := maxVar + 1
      let witnessJson := Crypto.ZK.Export.assignmentToJson compiled.assignment numVars |>.compress
      -- Gather public inputs (chainId/paymentManager optional via env)
      let chainId ← getEnvOr "PAY_CHAIN_ID" "8453" -- Base mainnet default
      let pm ← getEnvOr "PAY_MANAGER_ADDR" "0x0000000000000000000000000000000000000000"
      let publicJ :=
        mkPublicJson chainId pm reqWithVerified.walletAddress reqWithVerified
          policyC statePreC statePostC nullifier compiled.output envIdxs |>.compress
      -- Write outputs and certificate
      let outR1cs := System.FilePath.mk outDir / "r1cs.json"
      let outWitness := System.FilePath.mk outDir / "witness.json"
      let outPublic := System.FilePath.mk outDir / "public.json"
      let outPolicyCanon := System.FilePath.mk outDir / "policy.canon.json"
      let outStateCanon := System.FilePath.mk outDir / "state.canon.json"
      FS.createDirAll (System.FilePath.mk outDir)
      writeFile outR1cs r1csJson
      writeFile outWitness witnessJson
      writeFile outPublic publicJ
      -- Certificate uses canonical policy JSON (compressed) and r1csJson
      let policyCanonJ := (Payments.JsonCodec.policyToCanonicalJson pol)
      let stateCanonJ := (Payments.JsonCodec.stateToCanonicalJson st)
      let policyCanon := policyCanonJ.compress
      let stateCanon := stateCanonJ.compress
      -- Emit canonicalized policy/state for third-party auditors (pm_audit)
      writeFile outPolicyCanon policyCanon
      writeFile outStateCanon stateCanon
      writeCertificate outDir policyCanon r1csJson
      println s!"wrote {outR1cs} {outWitness} {outPublic}"
      -- Happy-path: require all checks true
      if !(checks.allowedRecipient && checks.amountOkPerTx && checks.perWindowOk && checks.budgetOk) then
        eprintln "checks failed (policy non-compliance)"
        return 2
      return 0
  | _ =>
      eprintln "Usage: lake exe pm_prove <policy.json> <state.json> <request.json> <outdir>"
      return 1

end PMProve
end CLI
end Payments
end HeytingLean

open HeytingLean.Payments.CLI.PMProve in
def main (args : List String) : IO UInt32 :=
  HeytingLean.Payments.CLI.PMProve.main args
