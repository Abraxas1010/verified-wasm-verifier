import Lean
import Lean.Data.Json
import HeytingLean.CCI.Core
import HeytingLean.CCI.Cert
import HeytingLean.CCI.Json
import HeytingLean.CCI.CryptoSpecs
import HeytingLean.CLI.Args

/-
# cci_crypto_export CLI

Export a minimal CCI certificate for a *named* crypto property from
`crypto_proofs_master_list.md`. The omega-expression is a single atom
tagged by the property slug, and the digest is computed so that
`HeytingLean.CCI.check` accepts the certificate.

Usage (informal):

  cci_crypto_export <property-slug> [--out PATH] [--inputs PATH] [--set KEY=VALUE]...

If `<property-slug>` is omitted, `"property.unknown"` is used.
-/

namespace HeytingLean
namespace CLI
namespace CCICryptoExport

open HeytingLean.CCI

/-- Quote and escape a JSON string (shared with the CCI tools). -/
private def q (s : String) : String :=
  let s' := HeytingLean.CCI.jsonEscape s
  "\"" ++ s' ++ "\""

/-- Encode key/value environment entries as a small JSON array. -/
def encodeKVStr (kvs : List (String × String)) : String :=
  let arr := kvs.map (fun (k,v) =>
    "{" ++ "\"k\":" ++ q k ++ ",\"v\":" ++ q v ++ "}")
  "[" ++ String.intercalate "," arr ++ "]"

/-- Encode a `Certificate` as JSON, matching the format used by `ExportCCI`. -/
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

def usage : String :=
  "usage: cci_crypto_export <property-slug> [--out PATH] [--inputs PATH] [--set KEY=VALUE]"

/-- Parse CLI arguments: property slug, output path, optional inputs JSON, and overrides. -/
private def parseArgs (argv : List String) :
    Option String × Option String × Option String × List (String × String) :=
  let rec go
      (xs : List String)
      (prop : Option String)
      (out : Option String)
      (inp : Option String)
      (sets : List (String × String)) :
      Option String × Option String × Option String × List (String × String) :=
    match xs with
    | [] => (prop, out, inp, sets)
    | "--out" :: p :: rest => go rest prop (some p) inp sets
    | "--inputs" :: p :: rest => go rest prop out (some p) sets
    | tok :: rest =>
        if tok.startsWith "--set" then
          match tok.drop 5 |>.splitOn "=" with
          | k :: v :: _ => go rest prop out inp ((k,v) :: sets)
          | _ => go rest prop out inp sets
        else
          -- first non-flag positional argument is the property slug
          match prop with
          | none   => go rest (some tok) out inp sets
          | some _ => go rest prop out inp sets
  go argv none none none []

def main (argv : List String) : IO Unit := do
  let argv := HeytingLean.CLI.stripLakeArgs argv
  let (propSlugOpt, outFlag, inputsFlag, setFlags) := parseArgs argv
  let propSlug := propSlugOpt.getD "property.unknown"

  -- Base inputs are aligned with the existing ExportCCI CLI so that
  -- downstream tools can reuse the same JSON layout.
  let getEnvOr (k : String) (d : String) : IO String :=
    return (← IO.getEnv k).getD d
  let chainId         ← getEnvOr "CHAIN_ID" "1"
  let paymentManager  ← getEnvOr "PAYMENT_MANAGER" "0xPM"
  let walletAddress   ← getEnvOr "WALLET_ADDRESS" "0xWALLET"
  let hashedId        ← getEnvOr "HASHED_ID" "0xID"
  let policyCommit    ← getEnvOr "POLICY_COMMIT" "0xPOLICY"
  let statePre        ← getEnvOr "STATE_COMMIT_PRE" "s0"
  let statePost       ← getEnvOr "STATE_COMMIT_POST" "s1"
  let epoch           ← getEnvOr "EPOCH" "0"
  let recipient       ← getEnvOr "RECIPIENT" "alice"
  let amount          ← getEnvOr "AMOUNT" "42"
  let budgetId        ← getEnvOr "BUDGET_ID" "0"
  let nullifier       ← getEnvOr "NULLIFIER" "0x00"
  let irv             ← getEnvOr "IRV" "1"
  let rtv             ← getEnvOr "REWRITE_TABLEV" "1"
  let cv              ← getEnvOr "CANONV" "1"
  let cirv            ← getEnvOr "CIRCUITV" "0"
  let baseInputs : PublicInputs := [
    ("chainId", chainId), ("paymentManager", paymentManager), ("walletAddress", walletAddress),
    ("hashedId", hashedId), ("policyCommit", policyCommit),
    ("stateCommit_pre", statePre), ("stateCommit_post", statePost),
    ("epoch", epoch), ("recipient", recipient), ("amount", amount), ("budget_id", budgetId), ("nullifier", nullifier),
    ("IRv", irv), ("rewriteTablev", rtv), ("canonv", cv), ("circuitv", cirv),
    ("property_slug", propSlug)
  ]

  -- Apply inputs JSON if provided.
  let inputs ← do
    match inputsFlag with
    | none => pure baseInputs
    | some p =>
        let fp := System.FilePath.mk p
        let s ← IO.FS.readFile fp
        match Lean.Json.parse s with
        | .error _ => pure baseInputs
        | .ok j =>
            match j.getObj? with
            | .error _ => pure baseInputs
            | .ok o =>
                let upd (kvs : List (String × String)) (k : String) : List (String × String) :=
                  match o.get? k with
                  | some (.str v) => kvs.map (fun (kk, vv) => if kk = k then (kk, v) else (kk, vv))
                  | _ => kvs
                let keys :=
                  ["chainId","paymentManager","walletAddress","hashedId","policyCommit",
                   "stateCommit_pre","stateCommit_post","epoch","recipient","amount",
                   "budget_id","nullifier","IRv","rewriteTablev","canonv","circuitv","property_slug"]
                pure <| keys.foldl upd baseInputs

  -- Apply --set overrides.
  let inputs := setFlags.foldl (fun acc (k,v) =>
    acc.map (fun (kk,vv) => if kk = k then (kk,v) else (kk,vv))) inputs

  -- Build certificate from slug and encode as JSON string.
  let cert : Certificate := CryptoSpecs.mkCertificateFromSlug propSlug inputs
  let j := encodeCertStr cert
  match outFlag with
  | some p => IO.FS.writeFile p j
  | none   => IO.println j

end CCICryptoExport
end CLI
end HeytingLean

def main (argv : List String) : IO Unit :=
  HeytingLean.CLI.CCICryptoExport.main argv
