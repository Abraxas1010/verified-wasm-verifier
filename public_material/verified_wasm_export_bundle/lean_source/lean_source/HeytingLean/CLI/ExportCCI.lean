import Lean
import Lean.Data.Json
import HeytingLean.CCI.Core
import HeytingLean.CCI.Json
import HeytingLean.CCI.Cert
import HeytingLean.CCI.RewriteTable
import HeytingLean.CCI.Check
import HeytingLean.CLI.Args

/-!
# Export CCI certificate (Option‑A baseline)

Emits a minimal certificate with:
- public inputs sourced from environment variables (with deterministic defaults),
- a small ω-expression plus a nontrivial rewrite id,
- a digest for the canonicalized ω-expression and a statement digest tying inputs to ω.

The goal is to keep the JSON schema and hashing stable while remaining small
enough to be exercised by executable-first QA.
-/

namespace HeytingLean
namespace CLI

open HeytingLean.CCI

private def q (s : String) : String :=
  let s' := HeytingLean.CCI.jsonEscape s
  "\"" ++ s' ++ "\""

def encodeKVStr (kvs : List (String × String)) : String :=
  let arr := kvs.map (fun (k,v) =>
    "{" ++ "\"k\":" ++ q k ++ ",\"v\":" ++ q v ++ "}")
  "[" ++ String.intercalate "," arr ++ "]"

def encodeCertStr (c : Certificate) : String :=
  let inputs := encodeKVStr c.inputs
  let omega  := encodeExprStr c.omega
  let lenses :=
    let items := c.lensImgs.map (fun l => encodeLensStr l)
    "[" ++ String.intercalate "," items ++ "]"
  let rws    :=
    let items := c.rewrites.map (fun (n : Nat) => toString n)
    "[" ++ String.intercalate "," items ++ "]"
  let digs   :=
    let hexOf (d : Digest) : String :=
      let parts := d.toList.map (fun b =>
        let s := (Nat.toDigits 16 b.toNat).asString
        if s.length = 1 then "0" ++ s else s)
      String.intercalate "" parts
    let mk : (Path × Digest) → String := fun (p,d) =>
      "{" ++ "\"path\":" ++ q p ++ ",\"digest\":" ++ q (hexOf d) ++ "}"
    let items := c.digests.map mk
    "[" ++ String.intercalate "," items ++ "]"
  "{" ++
    "\"inputs\":" ++ inputs ++ "," ++
    "\"omega\":" ++ omega ++ "," ++
    "\"lenses\":" ++ lenses ++ "," ++
    "\"rewrites\":" ++ rws ++ "," ++
    "\"digests\":" ++ digs ++
  "}"

def ExportCCI.main (argv : List String) : IO Unit := do
  -- simple flag parser: --out PATH, --inputs PATH, --set KEY=VALUE ...
  let rec parse (xs : List String)
    (out : Option String) (inp : Option String) (sets : List (String × String)) : (Option String) × (Option String) × (List (String × String)) :=
    match xs with
    | [] => (out, inp, sets)
    | "--out" :: p :: rest => parse rest (some p) inp sets
    | "--inputs" :: p :: rest => parse rest out (some p) sets
    | "--set" :: kv :: rest =>
        match kv.splitOn "=" with
        | k :: v :: _ => parse rest out inp ((k, v) :: sets)
        | _ => parse rest out inp sets
    | tok :: rest =>
        if tok.startsWith "--set=" then
          match tok.drop 6 |>.splitOn "=" with
          | k :: v :: _ => parse rest out inp ((k, v) :: sets)
          | _ => parse rest out inp sets
        else
          parse rest out inp sets
  let args := HeytingLean.CLI.stripLakeArgs argv
  let (outFlag, inputsFlag, setFlags) := parse args none none []
  -- inputs (env overrides + defaults) and version tags
  let get (k : String) (d : String) : IO String := do
    return (← IO.getEnv k).getD d
  let chainId         ← get "CHAIN_ID" "1"
  let paymentManager  ← get "PAYMENT_MANAGER" "0xPM"
  let walletAddress   ← get "WALLET_ADDRESS" "0xWALLET"
  let hashedId        ← get "HASHED_ID" "0xID"
  let policyCommit    ← get "POLICY_COMMIT" "0xPOLICY"
  let statePre        ← get "STATE_COMMIT_PRE" "s0"
  let statePost       ← get "STATE_COMMIT_POST" "s1"
  let epoch           ← get "EPOCH" "0"
  let recipient       ← get "RECIPIENT" "alice"
  let amount          ← get "AMOUNT" "42"
  let budgetId        ← get "BUDGET_ID" "0"
  let nullifier       ← get "NULLIFIER" "0x00"
  let irv             ← get "IRV" HeytingLean.CCI.IRv
  let rtv             ← get "REWRITE_TABLEV" HeytingLean.CCI.RewriteTablev
  let cv              ← get "CANONV" HeytingLean.CCI.Canonv
  let cirv            ← get "CIRCUITV" HeytingLean.CCI.Circuitv
  let inputs : PublicInputs := [
    ("chainId", chainId), ("paymentManager", paymentManager), ("walletAddress", walletAddress),
    ("hashedId", hashedId), ("policyCommit", policyCommit),
    ("stateCommit_pre", statePre), ("stateCommit_post", statePost),
    ("epoch", epoch), ("recipient", recipient), ("amount", amount), ("budget_id", budgetId), ("nullifier", nullifier),
    ("IRv", irv), ("rewriteTablev", rtv), ("canonv", cv), ("circuitv", cirv)
  ]
  -- apply inputs JSON if provided
  let inputs ← do
    match inputsFlag with
    | none => pure inputs
    | some p =>
        let fp := System.FilePath.mk p
        if !(← fp.pathExists) then
          IO.eprintln "E-INPUTS-OPEN"
          IO.Process.exit 2
        let s ←
          try IO.FS.readFile fp
          catch _ =>
            IO.eprintln "E-INPUTS-OPEN"
            IO.Process.exit 2
        match Lean.Json.parse s with
        | .error _ =>
            IO.eprintln "E-INPUTS-JSON"
            IO.Process.exit 2
        | .ok j =>
            match j.getObj? with
            | .error _ =>
                IO.eprintln "E-INPUTS-JSON"
                IO.Process.exit 2
            | .ok o =>
                let upd (kvs : List (String × String)) (k : String) : List (String × String) :=
                  match o.get? k with
                  | some (.str v) => kvs.map (fun (kk, vv) => if kk = k then (kk, v) else (kk, vv))
                  | _ => kvs
                let keys := ["chainId","paymentManager","walletAddress","hashedId","policyCommit","stateCommit_pre","stateCommit_post","epoch","recipient","amount","budget_id","nullifier","IRv","rewriteTablev","canonv","circuitv"]
                pure <| keys.foldl upd inputs
  -- apply --set overrides
  let inputs := setFlags.foldl (fun acc (k,v) => acc.map (fun (kk,vv) => if kk = k then (kk,v) else (kk,vv))) inputs
  -- Tiny demo omega + rewrites: exercise (at least) one nontrivial rewrite rule.
  let omega := Expr.notR (Expr.andR (Expr.atom "P") (Expr.atom "Q"))
  let lenses : List Lens := []
  let rewrites : List Nat := [Rule.deMorgan_and]
  -- export digest of canon(replay(omega, rewrites)) to match checker
  let omegaD := hashExpr (HeytingLean.CCI.canon (HeytingLean.CCI.applyRewrites omega rewrites))
  -- stmt digest: H("Stmt" || encode(publicInputs) || hex(omegaD))
  let stmtPayload := "Stmt|" ++ encodeKVStr inputs ++ "|" ++ (match encodeDigest omegaD with | Lean.Json.str s => s | _ => "")
  let stmtD := digestOfString stmtPayload
  let digests : List (Path × Digest) := [("omega", omegaD), ("stmt", stmtD)]
  let cert : Certificate := { inputs := inputs, omega := omega, lensImgs := lenses, rewrites := rewrites, digests := digests }
  let j := encodeCertStr cert
  match outFlag with
  | some p =>
      try IO.FS.writeFile p j
      catch _ =>
        IO.eprintln "E-OUT-WRITE"
        IO.Process.exit 2
  | none   => IO.println j

end CLI
end HeytingLean

def main (argv : List String) : IO Unit :=
  HeytingLean.CLI.ExportCCI.main argv
