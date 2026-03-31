import Lean
import Lean.Data.Json
import HeytingLean.Payments.Merkle
import HeytingLean.Crypto.ZK.Export

open Lean
open HeytingLean.Payments

namespace Tests

def writeFile (p : System.FilePath) (s : String) : IO Unit := IO.FS.writeFile p s

def mkPolicy (root : String) : Json :=
  Json.mkObj [
    ("allowedRecipientsMode", Json.str "verified"),
    ("caps", Json.mkObj [("perTx", Json.str "1000"), ("perDay", Json.str "5000")]),
    ("budgets", Json.arr #[Json.mkObj [("id", Json.str "ops"), ("cap", Json.str "10000"), ("unit", Json.str "month")]]),
    ("verifiedRoot", Json.str root)
  ]

def mkState (spent : String) (epoch : Nat) : Json :=
  Json.mkObj [ ("epoch", Json.num epoch), ("spentToday", Json.str spent), ("txCount", Json.num 0) ]

def mkRequest (recipient amount : String) (epoch : Nat) : Json :=
  Json.mkObj [
    ("hashedId", Json.str "0xWALLET"),
    ("recipient", Json.str recipient),
    ("amount", Json.str amount),
    ("budget_id", Json.str "ops"),
    ("epoch", Json.num epoch)
  ]

def mkProof (recipient : String) : Json :=
  let leaf := HeytingLean.Payments.Merkle.computeLeaf recipient
  Json.mkObj [ ("root", Json.str leaf), ("recipient", Json.str recipient), ("path", Json.arr #[]) ]

def jsonToSystemOrFail (j : Json) : IO HeytingLean.Crypto.ZK.System := do
  match HeytingLean.Crypto.ZK.Export.jsonToSystem j with
  | some sys => pure sys
  | none => throw <| IO.userError "Bad R1CS system JSON"

def jsonToAssignmentOrFail (j : Json) : IO (Array ℚ) := do
  match HeytingLean.Crypto.ZK.Export.jsonToAssignment j with
  | some arr => pure arr
  | none => throw <| IO.userError "Bad witness JSON"

def checkSatisfaction (sys : HeytingLean.Crypto.ZK.System) (assign : Nat → ℚ) : Bool :=
  sys.constraints.all (fun c => ((c.A.eval assign) * (c.B.eval assign)) == (c.C.eval assign))

def run (_args : List String) : IO UInt32 := do
  IO.println "=== TEST: Witness→Proof→Verification Pipeline ==="
  let tmp ← IO.FS.createTempDir
  let policyPath := tmp / "policy.json"
  let statePath := tmp / "state.json"
  let requestPath := tmp / "request.json"
  let proofPath := tmp / "proof.json"
  let outDir := tmp / "out"
  let recipient := "0xabc123"
  let root := HeytingLean.Payments.Merkle.computeLeaf recipient
  -- Setup
  writeFile policyPath (mkPolicy root |>.compress)
  writeFile statePath (mkState "0" 1 |>.compress)
  writeFile requestPath (mkRequest recipient "300" 1 |>.compress)
  writeFile proofPath (mkProof recipient |>.compress)
  -- Generate witness and proof artefacts via pm_prove
  let rc1 ← IO.Process.output { cmd := "lake", args := #["exe","pm_prove","--", policyPath.toString, statePath.toString, requestPath.toString, outDir.toString, s!"--verified-proof={proofPath}"] }
  if rc1.exitCode ≠ 0 then IO.eprintln "pm_prove failed"; IO.eprintln rc1.stderr; return 1
  -- Verify via pm_verify (valid path)
  let rc2 ← IO.Process.output { cmd := "lake", args := #["exe","pm_verify","--", policyPath.toString, statePath.toString, (outDir/"r1cs.json").toString, (outDir/"witness.json").toString, (outDir/"public.json").toString, s!"--verified-proof={proofPath}"] }
  if rc2.exitCode ≠ 0 then IO.eprintln "pm_verify failed on valid witness"; return 1
  IO.println "✓ Valid witness produces accepted verification"
  -- Preserve original public.json for mismatch test later
  let origPublic := tmp / "public_orig.json"
  let pOrig ← IO.FS.readFile (outDir / "public.json")
  writeFile origPublic pOrig
  -- Load R1CS + witness and check satisfaction directly
  let sysJ ← IO.FS.readFile (outDir / "r1cs.json")
  let witJ ← IO.FS.readFile (outDir / "witness.json")
  let sys ← jsonToSystemOrFail (match Json.parse sysJ with | .ok j => j | .error _ => Json.null)
  let arr ← jsonToAssignmentOrFail (match Json.parse witJ with | .ok j => j | .error _ => Json.null)
  let assign := HeytingLean.Crypto.ZK.Export.assignmentOfArray arr
  if !checkSatisfaction sys assign then IO.eprintln "Constraint satisfaction failed on valid witness"; return 1
  -- Tamper witness and expect verification to fail
  let witTam := witJ.modify 0 (fun c => if c = '0' then '1' else '0')
  writeFile (outDir / "witness.json") witTam
  let rc3 ← IO.Process.output { cmd := "lake", args := #["exe","pm_verify","--", policyPath.toString, statePath.toString, (outDir/"r1cs.json").toString, (outDir/"witness.json").toString, (outDir/"public.json").toString, s!"--verified-proof={proofPath}"] }
  if rc3.exitCode = 0 then IO.eprintln "Tampered witness accepted unexpectedly"; return 1
  IO.println "✓ Tampered witness rejected"
  -- Restore original witness and public for subsequent checks
  writeFile (outDir / "witness.json") witJ
  writeFile (outDir / "public.json") pOrig
  -- Wrong statement: verify with wrong state (should fail)
  let wrongState := tmp / "state_wrong.json"
  writeFile wrongState (mkState "9999" 1 |>.compress)
  let rc4 ← IO.Process.output { cmd := "lake", args := #["exe","pm_verify","--", policyPath.toString, wrongState.toString, (outDir/"r1cs.json").toString, (outDir/"witness.json").toString, (outDir/"public.json").toString, s!"--verified-proof={proofPath}"] }
  if rc4.exitCode = 0 then IO.eprintln "Wrong statement accepted unexpectedly"; return 1
  IO.println "✓ Wrong statement rejected by verifier"
  -- Mutate public: wrong recipient must fail (verified membership check)
  let pubWrongRecipient := (pOrig.replace s!"\"recipient\":\"{recipient}\"" "\"recipient\":\"0xdeadbeef\"")
  writeFile (outDir / "public.json") pubWrongRecipient
  let rc5 ← IO.Process.output { cmd := "lake", args := #["exe","pm_verify","--", policyPath.toString, statePath.toString, (outDir/"r1cs.json").toString, (outDir/"witness.json").toString, (outDir/"public.json").toString, s!"--verified-proof={proofPath}"] }
  if rc5.exitCode = 0 then IO.eprintln "Wrong recipient accepted unexpectedly"; return 1
  IO.println "✓ Wrong recipient rejected by verifier"
  -- Restore original public
  writeFile (outDir / "public.json") pOrig
  -- Mutate public: wrong budget_id must fail (nullifier binding)
  let pubWrongBudget := (pOrig.replace "\"budget_id\":\"ops\"" "\"budget_id\":\"opsX\"")
  writeFile (outDir / "public.json") pubWrongBudget
  let rc6 ← IO.Process.output { cmd := "lake", args := #["exe","pm_verify","--", policyPath.toString, statePath.toString, (outDir/"r1cs.json").toString, (outDir/"witness.json").toString, (outDir/"public.json").toString, s!"--verified-proof={proofPath}"] }
  if rc6.exitCode = 0 then IO.eprintln "Wrong budget_id accepted unexpectedly"; return 1
  IO.println "✓ Wrong budget_id rejected by verifier"
  IO.println "=== WITNESS VERIFICATION COMPLETE ==="
  return 0

end Tests

def main (args : List String) : IO UInt32 :=
  Tests.run args
