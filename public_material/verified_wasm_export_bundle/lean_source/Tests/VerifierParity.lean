import Lean
import Lean.Data.Json
import HeytingLean.CLI.Args

open Lean

namespace Tests

def writeFile (p : System.FilePath) (s : String) : IO Unit := IO.FS.writeFile p s

def mkPolicyCustom (recips : List String) (perTx perDay : Nat) : Json :=
  Json.mkObj [
    ("allowedRecipientsMode", Json.str "custom"),
    ("customRecipients", Json.arr (recips.map Json.str |>.toArray)),
    ("caps", Json.mkObj [("perTx", Json.str (toString perTx)), ("perDay", Json.str (toString perDay))]),
    ("budgets", Json.arr #[Json.mkObj [("id", Json.str "ops"), ("cap", Json.str "10000"), ("unit", Json.str "month")]])
  ]

def mkState (spent : Nat) (epoch : Nat) : Json :=
  Json.mkObj [ ("epoch", Json.num epoch), ("spentToday", Json.str (toString spent)), ("txCount", Json.num 0) ]

def mkRequest (recipient : String) (amount : Nat) (epoch : Nat) : Json :=
  Json.mkObj [
    ("hashedId", Json.str "0xWALLET"),
    ("recipient", Json.str recipient),
    ("amount", Json.str (toString amount)),
    ("budget_id", Json.str "ops"),
    ("epoch", Json.num epoch)
  ]

def run (_args : List String) : IO UInt32 := do
  IO.println "=== TEST: Verifier parity (pm_verify vs chain_verify) ==="
  let args := HeytingLean.CLI.stripLakeArgs _args
  let rec parseN (xs : List String) : Option Nat :=
    match xs with
    | [] => none
    | "--n" :: v :: _ => v.toNat?
    | x :: rest =>
        if x.startsWith "--n=" then (x.drop 4).toNat? else parseN rest
  let n : Nat ←
    match (← IO.getEnv "VERIFIER_PARITY_N") with
    | some s => pure (s.toNat?.getD 4)
    | none => pure ((parseN args).getD 4)
  let tmp ← IO.FS.createTempDir
  let out := tmp / "out"
  IO.FS.createDirAll out
  let policyPath := tmp / "policy.json"
  let statePath := tmp / "state.json"
  let requestPath := tmp / "request.json"
  -- Run N vectors with varied amounts/spend/recipients (default: 10; set VERIFIER_PARITY_N or pass --n).
  for i in [1:(n+1)] do
    let recip := if i % 2 == 0 then "0xAA" else "0xBB"
    let policy := mkPolicyCustom ["0xAA","0xBB"] 1000 5000
    let state := mkState (i % 900) (1 + (i / 25))
    let req := mkRequest recip (100 + (i % 400)) (1 + (i / 25))
    writeFile policyPath (policy.compress)
    writeFile statePath (state.compress)
    writeFile requestPath (req.compress)
    let rcProve ← IO.Process.output { cmd := "lake", args := #["exe","pm_prove","--", policyPath.toString, statePath.toString, requestPath.toString, out.toString] }
    if rcProve.exitCode ≠ 0 then
      IO.eprintln s!"pm_prove failed for vector {i}:\n{rcProve.stderr}"; return 1
    let r1cs := out / "r1cs.json"
    let wit := out / "witness.json"
    let pub := out / "public.json"
    let rcPm ← IO.Process.output { cmd := "lake", args := #["exe","pm_verify","--", policyPath.toString, statePath.toString, r1cs.toString, wit.toString, pub.toString] }
    let rcChain ← IO.Process.output { cmd := "lake", args := #["exe","chain_verify","--", r1cs.toString, wit.toString, pub.toString] }
    let pmOk := (rcPm.exitCode == 0)
    let chOk := (rcChain.exitCode == 0)
    if pmOk ≠ chOk then
      IO.eprintln s!"Parity mismatch on vector {i}: pm={pmOk} chain={chOk}"
      IO.eprintln s!"pm stderr: {rcPm.stderr}\nchain stderr: {rcChain.stderr}"
      return 1
    IO.println s!"✓ Parity confirmed for vector {i}"
  IO.println "=== VERIFIER PARITY COMPLETE ==="
  return 0

end Tests

def main (args : List String) : IO UInt32 :=
  Tests.run args
