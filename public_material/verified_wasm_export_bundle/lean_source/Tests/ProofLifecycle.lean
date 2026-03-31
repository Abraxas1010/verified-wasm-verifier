import Lean
import Lean.Data.Json
import HeytingLean.Payments.Merkle
import HeytingLean.Crypto.PoseidonNative
import HeytingLean.Util.SHA

open Lean
open HeytingLean.Payments

def writeFile (p : System.FilePath) (s : String) : IO Unit := IO.FS.writeFile p s

def mkPolicy (root : String) : Json :=
  Json.mkObj [
    ("allowedRecipientsMode", Json.str "verified"),
    ("caps", Json.mkObj [("perTx", Json.str "1000"), ("perDay", Json.str "5000")]),
    ("budgets", Json.arr #[Json.mkObj [("id", Json.str "ops"), ("cap", Json.str "10000"), ("unit", Json.str "month")]]),
    ("verifiedRoot", Json.str root)
  ]

def mkState : Json :=
  Json.mkObj [ ("epoch", Json.num 100), ("spentToday", Json.str "500"), ("txCount", Json.num 3) ]

def mkRequest (recipient amount : String) : Json :=
  Json.mkObj [
    ("hashedId", Json.str "0x456..."),
    ("recipient", Json.str recipient),
    ("amount", Json.str amount),
    ("budget_id", Json.str "ops"),
    ("epoch", Json.num 100)
  ]

def mkProof (recipient : String) : Json :=
  let leaf := HeytingLean.Payments.Merkle.computeLeaf recipient
  -- root equals leaf for empty path
  Json.mkObj [ ("root", Json.str leaf), ("recipient", Json.str recipient), ("path", Json.arr #[]) ]

def run (_args : List String) : IO UInt32 := do
  IO.println "=== TEST: Complete Proof Lifecycle (Lean-native) ==="
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
  -- run prove + verify
  let rc1 ← IO.Process.output { cmd := "lake", args := #["exe","pm_prove","--", policyPath.toString, statePath.toString, requestPath.toString, outDir.toString, s!"--verified-proof={proofPath}"] }
  if rc1.exitCode ≠ 0 then
    IO.eprintln "pm_prove failed"
    IO.eprintln rc1.stderr
    return 1
  let rc2 ← IO.Process.output { cmd := "lake", args := #["exe","pm_verify","--", (policyPath.toString), (statePath.toString), (outDir / "r1cs.json").toString, (outDir / "witness.json").toString, (outDir / "public.json").toString, s!"--verified-proof={proofPath}"] }
  if rc2.exitCode ≠ 0 then
    IO.eprintln "pm_verify failed"
    IO.eprintln rc2.stderr
    return 1
  -- determinism: run again and compare public.json digest
  let p1 ← IO.FS.readFile (outDir / "public.json")
  let d1 ← HeytingLean.Util.sha256HexOfStringIO p1
  let _ ← IO.Process.output { cmd := "lake", args := #["exe","pm_prove","--", policyPath.toString, statePath.toString, requestPath.toString, outDir.toString, s!"--verified-proof={proofPath}"] }
  let p2 ← IO.FS.readFile (outDir / "public.json")
  let d2 ← HeytingLean.Util.sha256HexOfStringIO p2
  if d1 ≠ d2 then IO.eprintln "Non-deterministic public.json"; return 1
  -- change amount, expect different witness
  writeFile requestPath (mkRequest recipient "301" |>.compress)
  let _ ← IO.Process.output { cmd := "lake", args := #["exe","pm_prove","--", policyPath.toString, statePath.toString, requestPath.toString, outDir.toString, s!"--verified-proof={proofPath}"] }
  let p3 ← IO.FS.readFile (outDir / "public.json")
  let d3 ← HeytingLean.Util.sha256HexOfStringIO p3
  if d1 = d3 then IO.eprintln "Public unchanged after different input"; return 1
  IO.println "✓ Basic lifecycle test PASSED"
  return 0

def main (args : List String) : IO UInt32 := run args
