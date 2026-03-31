import Lean
import Lean.Data.Json
import HeytingLean.Payments.Merkle

open Lean
open HeytingLean.Payments

def writeFile (p : System.FilePath) (s : String) : IO Unit := IO.FS.writeFile p s

def mkPolicy (root : String) : Json :=
  Json.mkObj [ ("allowedRecipientsMode", Json.str "verified")
             , ("caps", Json.mkObj [("perTx", Json.str "1000"), ("perDay", Json.str "5000")])
             , ("budgets", Json.arr #[Json.mkObj [("id", Json.str "ops"), ("cap", Json.str "10000"), ("unit", Json.str "month")]])
             , ("verifiedRoot", Json.str root) ]

def mkState : Json := Json.mkObj [ ("epoch", Json.num 100), ("spentToday", Json.str "500"), ("txCount", Json.num 3) ]
def mkRequest (recipient amount : String) : Json :=
  Json.mkObj [ ("hashedId", Json.str "0x456...")
             , ("recipient", Json.str recipient)
             , ("amount", Json.str amount)
             , ("budget_id", Json.str "ops")
             , ("epoch", Json.num 100) ]
def mkProof (recipient : String) : Json :=
  let leaf := HeytingLean.Payments.Merkle.computeLeaf recipient
  Json.mkObj [ ("root", Json.str leaf), ("recipient", Json.str recipient), ("path", Json.arr #[]) ]

def run (_args : List String) : IO UInt32 := do
  IO.println "=== TEST: Proof Tampering Detection ==="
  let tmp ← IO.FS.createTempDir
  let policyPath := tmp / "policy.json"
  let statePath := tmp / "state.json"
  let requestPath := tmp / "request.json"
  let proofPath := tmp / "proof.json"
  let outDir := tmp / "out"
  let recipient := "0x123..."
  let root := HeytingLean.Payments.Merkle.computeLeaf recipient
  writeFile policyPath (mkPolicy root |>.compress)
  writeFile statePath mkState.compress
  writeFile requestPath (mkRequest recipient "300" |>.compress)
  writeFile proofPath (mkProof recipient |>.compress)
  -- produce valid outputs
  let _ ← IO.Process.output { cmd := "lake", args := #["exe","pm_prove","--", policyPath.toString, statePath.toString, requestPath.toString, outDir.toString, s!"--verified-proof={proofPath}"] }
  let rcOk ← IO.Process.output { cmd := "lake", args := #["exe","pm_verify","--", (policyPath.toString), (statePath.toString), (outDir / "r1cs.json").toString, (outDir / "witness.json").toString, (outDir / "public.json").toString, s!"--verified-proof={proofPath}"] }
  if rcOk.exitCode ≠ 0 then IO.eprintln "Baseline verify failed"; return 1
  -- Tamper witness
  let witPath := outDir / "witness.json"
  let w ← IO.FS.readFile witPath
  let w' := w.modify 0 (fun c => if c = '0' then '1' else '0')
  writeFile witPath w'
  let rcTam ← IO.Process.output { cmd := "lake", args := #["exe","pm_verify","--", (policyPath.toString), (statePath.toString), (outDir / "r1cs.json").toString, (outDir / "witness.json").toString, (outDir / "public.json").toString, s!"--verified-proof={proofPath}"] }
  if rcTam.exitCode = 0 then IO.eprintln "Tampered witness verified unexpectedly"; return 1
  IO.println "✓ All tampering detected successfully"
  return 0

def main (args : List String) : IO UInt32 := run args
