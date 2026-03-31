import Lean
import Lean.Data.Json
import HeytingLean.Crypto.BoolLens
import HeytingLean.Crypto.ZK.R1CS
import HeytingLean.Crypto.ZK.Export
import HeytingLean.Crypto.ZK.R1CSBool
import HeytingLean.Payments.Types
import HeytingLean.Payments.Rules
import HeytingLean.Payments.Commit
import HeytingLean.Payments.Merkle
import HeytingLean.Util.SHA
import HeytingLean.CLI.Args

namespace HeytingLean
namespace Payments
namespace CLI
namespace PMVerify

open IO
open Lean
open Crypto
open Crypto.BoolLens

private def readFileE (path : System.FilePath) : IO (Except String String) := do
  try let s ← FS.readFile path; pure (.ok s) catch e => pure (.error s!"read error at {path}: {e}")

/- Boolean formula over 4 variables: a ∧ b ∧ c ∧ d -/
def policyFormula4 : Crypto.Form 4 :=
  let v (i : Fin 4) := Crypto.Form.var i
  let a : Crypto.Form 4 := v ⟨0, by decide⟩
  let b : Crypto.Form 4 := v ⟨1, by decide⟩
  let c : Crypto.Form 4 := v ⟨2, by decide⟩
  let d : Crypto.Form 4 := v ⟨3, by decide⟩
  Crypto.Form.and (Crypto.Form.and a b) (Crypto.Form.and c d)

def env4 (f0 f1 f2 f3 : Bool) : BoolLens.Env 4 := fun i =>
  match i.1 with
  | 0 => f0
  | 1 => f1
  | 2 => f2
  | 3 => f3
  | _ => false

private def findOpt (opts : List String) (pref : String) : Option String :=
  match opts.find? (fun s => s.startsWith pref) with
  | none => none
  | some s =>
      let parts := s.splitOn "="
      if parts.length = 2 then some (parts[1]!) else none

structure Public where
  chainId              : String
  paymentManager       : String
  walletAddress?       : Option String
  hashedId             : String
  policyCommitment     : String
  stateCommitment_pre  : String
  stateCommitment_post : String
  epoch                : Nat
  recipient            : String
  amount               : String
  budget_id            : String
  nullifier            : String
  deriving Repr

open Lean (Json)

def parsePublicE (j : Json) : Except String Public := do
  let getStr (k : String) : Except String String :=
    match j.getObjVal? k with
    | .ok v =>
        match v.getStr? with
        | .ok s => .ok s
        | .error _ => .error s!"public field '{k}' not string"
    | .error _ => .error s!"missing public field '{k}'"
  let chainId ← getStr "chainId"
  let payman ← getStr "paymentManager"
  let hashed ← getStr "hashedId"
  let polC ← getStr "policyCommitment"
  let preC ← getStr "stateCommitment_pre"
  let postC ← getStr "stateCommitment_post"
  let recipient ← getStr "recipient"
  let amount ← getStr "amount"
  let budget_id ← getStr "budget_id"
  let nullifier ← getStr "nullifier"
  let epoch := match j.getObjVal? "epoch" with
    | .ok v => (match v.getNat? with | .ok n => n | .error _ => 0)
    | .error _ => 0
  let wallet := match j.getObjVal? "walletAddress" with | .ok (.str s) => some s | _ => none
  return { chainId := chainId, paymentManager := payman, walletAddress? := wallet
         , hashedId := hashed, policyCommitment := polC, stateCommitment_pre := preC
         , stateCommitment_post := postC, epoch := epoch, recipient := recipient
         , amount := amount, budget_id := budget_id, nullifier := nullifier }

structure Certificate where
  canonical_semantics_hash : String
  compiled_system_hash     : String
  poseidon_params_id       : String
  lean_toolchain_hash      : String
  git_sha                  : String
  deriving Repr

def parseCertificateE (j : Json) : Except String Certificate := do
  let getStr (k : String) : Except String String :=
    match j.getObjVal? k with
    | .ok (.str s) => .ok s
    | _ => .error s!"certificate field '{k}' missing or not string"
  pure { canonical_semantics_hash := (← getStr "canonical_semantics_hash")
       , compiled_system_hash     := (← getStr "compiled_system_hash")
       , poseidon_params_id       := (← getStr "poseidon_params_id")
       , lean_toolchain_hash      := (← getStr "lean_toolchain_hash")
       , git_sha                  := (← getStr "git_sha") }

def main (args : List String) : IO UInt32 := do
  let args := HeytingLean.CLI.stripLakeArgs args
  match args with
  | policyPath :: statePath :: r1csPath :: witnessPath :: publicPath :: opts =>
      let polRaw ← match (← readFileE policyPath) with | .ok s => pure s | .error m => eprintln m; return 1
      let stRaw  ← match (← readFileE statePath)  with | .ok s => pure s | .error m => eprintln m; return 1
      let sysRaw ← match (← readFileE r1csPath)   with | .ok s => pure s | .error m => eprintln m; return 1
      let witRaw ← match (← readFileE witnessPath)with | .ok s => pure s | .error m => eprintln m; return 1
      let pubRaw ← match (← readFileE publicPath) with | .ok s => pure s | .error m => eprintln m; return 1
      -- parse
      let polJ ← match Json.parse polRaw with | .ok j => pure j | .error e => eprintln e; return 1
      let stJ  ← match Json.parse stRaw  with | .ok j => pure j | .error e => eprintln e; return 1
      let sysJ ← match Json.parse sysRaw with | .ok j => pure j | .error e => eprintln e; return 1
      let asJ  ← match Json.parse witRaw with | .ok j => pure j | .error e => eprintln e; return 1
      let pubJ ← match Json.parse pubRaw with | .ok j => pure j | .error e => eprintln e; return 1
      -- decode domain
      let pol ← match Payments.JsonCodec.parsePolicy polJ with | .ok p => pure p | .error e => eprintln e; return 1
      let st  ← match Payments.JsonCodec.parseState stJ with  | .ok s => pure s | .error e => eprintln e; return 1
      let pub ← match parsePublicE pubJ with | .ok p => pure p | .error e => eprintln e; return 1
      -- reconstruct request from public
      let req0 : Payments.Request := { hashedId := pub.hashedId, recipient := pub.recipient
                                     , amount := pub.amount, budget_id := pub.budget_id
                                     , epoch := pub.epoch, walletAddress := pub.walletAddress? }
      -- Verified membership (optional / for mode=verified require proof)
      let envOpt ← IO.getEnv "PAY_VERIFIED_PROOF_PATH"
      let cliOpt := findOpt opts "--verified-proof="
      let verProofPath := match cliOpt with | some s => some s | none => envOpt
      let req : Payments.Request ←
        if pol.allowedRecipientsMode == "verified" then
          match verProofPath with
          | some vp =>
              let raw ← match (← readFileE (System.FilePath.mk vp)) with | .ok s => pure s | .error m => eprintln m; return 1
              let j ← match Json.parse raw with | .ok j => pure j | .error e => eprintln e; return 1
              let v ← match Payments.Merkle.parseVProofE j with | .ok v => pure v | .error e => eprintln e; return 1
              let (ok, _root) ← Payments.Merkle.verifyMembershipIO v
              if ¬ ok || v.recipient != req0.recipient then
                eprintln "verified membership check failed"; return 1
              else
                match pol.verifiedRoot with
                | some r => if r != v.root then eprintln "verified root mismatch vs policy"; return 1 else pure { req0 with verifiedOk := some true }
                | none => eprintln "policy missing verifiedRoot for verified mode"; return 1
          | none =>
              eprintln "policy mode=verified but no --verified-proof provided"; return 1
        else
          pure req0
      -- recompute checks and state transitions and commitments
      let checks := Payments.Rules.computeChecks pol st req
      let st' := Payments.Rules.applyRequest pol st req
      let policyC ← Payments.Commit.commitPolicyIO pol
      let statePreC ← Payments.Commit.commitStateIO st
      let statePostC ← Payments.Commit.commitStateIO st'
      let nullifier ← Payments.Commit.computeNullifierIO req.hashedId statePreC req.epoch
      -- cross-check public bundle
      if policyC ≠ pub.policyCommitment then eprintln "policyCommitment mismatch"; return 1
      if statePreC ≠ pub.stateCommitment_pre then eprintln "stateCommitment_pre mismatch"; return 1
      if statePostC ≠ pub.stateCommitment_post then eprintln "stateCommitment_post mismatch"; return 1
      if nullifier ≠ pub.nullifier then eprintln "nullifier mismatch"; return 1
      -- decode R1CS and witness
      let some sys := Crypto.ZK.Export.jsonToSystem sysJ | do eprintln "Bad system"; return 1
      let some arr := Crypto.ZK.Export.jsonToAssignment asJ | do eprintln "Bad assignment"; return 1
      -- check satisfaction
      let maxVar := sys.constraints.foldl (init := 0) (fun m c =>
        let step := fun acc (ts : List (Crypto.ZK.Var × ℚ)) => ts.foldl (fun a p => Nat.max a p.fst) acc
        let m1 := step 0 c.A.terms; let m2 := step m1 c.B.terms; let m3 := step m2 c.C.terms; Nat.max m m3)
      if arr.size ≤ maxVar then
        eprintln s!"Witness too small, needs ≥ {maxVar+1}, got {arr.size}"; return 1
      let assign := Crypto.ZK.Export.assignmentOfArray arr
      let okSat : Bool := sys.constraints.all (fun c => ((c.A.eval assign) * (c.B.eval assign)) == (c.C.eval assign))
      if ¬ okSat then eprintln "R1CS not satisfied by witness"; return 1
      -- recompute compiled output index and value and check assignment aligns to true
      let φ := policyFormula4
      let ρ : BoolLens.Env 4 := env4 checks.allowedRecipient checks.amountOkPerTx checks.perWindowOk checks.budgetOk
      let compiled := Crypto.ZK.R1CSBool.compile φ ρ
      let outIdx := compiled.output
      let actual := assign outIdx
      if actual ≠ (1 : ℚ) then
        eprintln s!"Output mismatch: witness[{outIdx}]={actual}, expected 1"; return 1
      -- certificate: read from sibling of r1cs path
      let certPath := (System.FilePath.mk r1csPath).withFileName "certificate.json"
      let certRaw ← match (← readFileE certPath) with | .ok s => pure s | .error msg => eprintln msg; return 1
      let certJ ← match Json.parse certRaw with | .ok j => pure j | .error e => eprintln e; return 1
      let cert ← match parseCertificateE certJ with | .ok c => pure c | .error e => eprintln e; return 1
      -- recompute digests
      let policyCanon := (Payments.JsonCodec.policyToCanonicalJson pol).compress
      let canonHash ← HeytingLean.Util.sha256HexOfStringIO policyCanon
      if canonHash ≠ cert.canonical_semantics_hash then
        eprintln "certificate canonical_semantics_hash mismatch"; return 1
      let r1csHash ← HeytingLean.Util.sha256HexOfStringIO (Lean.Json.compress sysJ)
      if r1csHash ≠ cert.compiled_system_hash then
        eprintln "certificate compiled_system_hash mismatch"; return 1
      println "ok"
      return 0
  | _ =>
      eprintln "Usage: lake exe pm_verify <policy.json> <state.json> <r1cs.json> <witness.json> <public.json>"
      return 1

end PMVerify
end CLI
end Payments
end HeytingLean

open HeytingLean.Payments.CLI.PMVerify in
def main (args : List String) : IO UInt32 :=
  HeytingLean.Payments.CLI.PMVerify.main args
