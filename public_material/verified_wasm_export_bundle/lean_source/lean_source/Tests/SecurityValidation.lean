import Lean
import Lean.Data.Json
import HeytingLean.Payments.Merkle
import HeytingLean.Payments.Commit

open Lean
open HeytingLean.Payments

def writeFile (p : System.FilePath) (s : String) : IO Unit := IO.FS.writeFile p s

def mkPolicy (root : String) : Json :=
  Json.mkObj [ ("allowedRecipientsMode", Json.str "verified")
             , ("caps", Json.mkObj [("perTx", Json.str "1000"), ("perDay", Json.str "1000")])
             , ("budgets", Json.arr #[Json.mkObj [("id", Json.str "ops"), ("cap", Json.str "2000"), ("unit", Json.str "month")]])
             , ("verifiedRoot", Json.str root) ]

def mkState (spent : String) (epoch : Nat) : Json :=
  Json.mkObj [ ("epoch", Json.num epoch), ("spentToday", Json.str spent), ("txCount", Json.num 0) ]

def mkRequest (recipient amount : String) (epoch : Nat) : Json :=
  Json.mkObj [ ("hashedId", Json.str "0xabc"), ("recipient", Json.str recipient), ("amount", Json.str amount), ("budget_id", Json.str "ops"), ("epoch", Json.num epoch) ]

def test_double_spend_prevention : IO UInt32 := do
  IO.println "=== TEST: Double-spend prevention ==="
  let tmp ← IO.FS.createTempDir
  let policyPath := tmp / "policy.json"
  let statePath := tmp / "state.json"
  let requestPath := tmp / "request.json"
  let proofPath := tmp / "proof.json"
  let outDir := tmp / "out"
  let recipient := "0x123"
  let root := HeytingLean.Payments.Merkle.computeLeaf recipient
  writeFile policyPath (mkPolicy root |>.compress)
  writeFile statePath (mkState "900" 1 |>.compress)
  writeFile requestPath (mkRequest recipient "200" 1 |>.compress)
  writeFile proofPath (Json.mkObj [("root", Json.str root), ("recipient", Json.str recipient), ("path", Json.arr #[])] |>.compress)
  -- Prove should fail due to perDay cap (900 + 200 > 1000)
  let rc1 ← IO.Process.output { cmd := "lake", args := #["exe","pm_prove","--", policyPath.toString, statePath.toString, requestPath.toString, outDir.toString, s!"--verified-proof={proofPath}"] }
  if rc1.exitCode = 0 then IO.eprintln "pm_prove unexpectedly succeeded for overspend"; return 1
  -- Make a valid request then attempt replay with different state
  writeFile statePath (mkState "100" 2 |>.compress)
  writeFile requestPath (mkRequest recipient "200" 2 |>.compress)
  let rc2 ← IO.Process.output { cmd := "lake", args := #["exe","pm_prove","--", policyPath.toString, statePath.toString, requestPath.toString, outDir.toString, s!"--verified-proof={proofPath}"] }
  if rc2.exitCode ≠ 0 then IO.eprintln "pm_prove failed on valid inputs"; return 1
  -- Verify with wrong state (replay): should fail
  let wrongState := tmp / "wrong_state.json"
  writeFile wrongState (mkState "0" 999 |>.compress)
  let rc3 ← IO.Process.output { cmd := "lake", args := #["exe","pm_verify","--", policyPath.toString, wrongState.toString, (outDir/"r1cs.json").toString, (outDir/"witness.json").toString, (outDir/"public.json").toString, s!"--verified-proof={proofPath}"] }
  if rc3.exitCode = 0 then IO.eprintln "pm_verify unexpectedly succeeded on replay"; return 1
  IO.println "✓ Double-spend/replay protection OK"
  return 0

def test_merkle_security : IO UInt32 := do
  IO.println "=== TEST: Merkle security ==="
  let recipient := "0x123"
  let other := "0x999"
  let root := HeytingLean.Payments.Merkle.computeLeaf recipient
  let proofGood := Json.mkObj [("root", Json.str root), ("recipient", Json.str recipient), ("path", Json.arr #[])]
  let proofBad1 := Json.mkObj [("root", Json.str root), ("recipient", Json.str other), ("path", Json.arr #[])]
  -- Direct membership check
  let parse (j : Json) := match HeytingLean.Payments.Merkle.parseVProofE j with | .ok p => p | .error _ => { root := "", recipient := "", path := [] }
  let (ok1, _) := HeytingLean.Payments.Merkle.verifyMembership (parse proofGood)
  let (ok2, _) := HeytingLean.Payments.Merkle.verifyMembership (parse proofBad1)
  if !ok1 then IO.eprintln "Valid membership rejected"; return 1
  if ok2 then IO.eprintln "Forged membership accepted"; return 1
  IO.println "✓ Merkle forgery prevented"
  return 0

def main (_args : List String) : IO UInt32 := do
  let r1 ← test_double_spend_prevention
  if r1 ≠ 0 then return r1
  let r2 ← test_merkle_security
  if r2 ≠ 0 then return r2
  return 0
