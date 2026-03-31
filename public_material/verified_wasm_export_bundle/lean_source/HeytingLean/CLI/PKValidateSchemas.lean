import Lean
import Lean.Data.Json

/-!
Lightweight local schema checks for proof-kit compatibility (no external libs).
Validates presence of required fields and simple hex patterns in public.json and receipt.json.
-/

namespace HeytingLean
namespace CLI
namespace PKValidateSchemas

open Lean

private def readFileE (p : System.FilePath) : IO (Except String String) := do
  try let s ← IO.FS.readFile p; pure (.ok s) catch e => pure (.error s!"read error at {p}: {e}")

def isHexLower (s : String) : Bool :=
  s.toList.all (fun c => c.isDigit || (c ≥ 'a' && c ≤ 'f'))

def isHexPrefixed (s : String) : Bool :=
  if s.startsWith "0x" then
    let rest := s.drop 2
    rest.toList.all (fun c => c.isDigit || (c ≥ 'a' && c ≤ 'f') || (c ≥ 'A' && c ≤ 'F'))
  else false

def requireKeys (j : Json) (keys : List String) : Except String Unit := do
  let obj ← match j.getObj? with | .ok o => pure o | .error _ => throw "expected object"
  for k in keys do
    if obj.contains k then pure () else throw s!"missing key: {k}"
  pure ()

def main (args : List String) : IO UInt32 := do
  match args with
  | [outDirStr] =>
      let outDir := System.FilePath.mk outDirStr
      let pubPath := outDir / "public.json"
      let recPath := outDir / "receipt.json"
      let certPath := outDir / "cert_pk.json"
      -- Parse public
      let pubRaw ← match (← readFileE pubPath) with | .ok s => pure s | .error m => IO.eprintln m; return 1
      let pubJ ← match Json.parse pubRaw with | .ok j => pure j | .error e => IO.eprintln e; return 1
      -- Required public fields (execution_receipt.schema.json subset + public_min)
      let pubReq := [
        "chainId","paymentManager","walletAddress","hashedId",
        "stateCommit_pre","stateCommit_post",
        "recipient","amount","budget_id","epoch","nullifier","lastEventHash",
        "IRv","rewriteTablev","canonv","circuitv",
        "omega_digest_public","ok","output_index","env_indices"
      ]
      match requireKeys pubJ pubReq with
      | .ok _ => pure ()
      | .error e => IO.eprintln s!"public.json schema error: {e}"; return 1
      -- Pattern checks
      let some omega := (pubJ.getObjVal? "omega_digest_public").toOption.bind (fun x => x.getStr?.toOption) | IO.eprintln "public.json: omega_digest_public missing"; return 1
      if !isHexPrefixed omega then IO.eprintln "public.json: omega_digest_public must be 0x-hex"; return 1
      -- Parse receipt
      let recRaw ← match (← readFileE recPath) with | .ok s => pure s | .error m => IO.eprintln m; return 1
      let recJ ← match Json.parse recRaw with | .ok j => pure j | .error e => IO.eprintln e; return 1
      match requireKeys recJ ["public","proof","cert_hash","blueprint_hash"] with
      | .ok _ => pure ()
      | .error e => IO.eprintln s!"receipt.json schema error: {e}"; return 1
      let obj ← match recJ.getObj? with | .ok o => pure o | .error _ => IO.eprintln "receipt: not object"; return 1
      let ch ← match obj.get? "cert_hash" with | some (.str s) => pure s | _ => IO.eprintln "receipt: cert_hash not string"; return 1
      let bh ← match obj.get? "blueprint_hash" with | some (.str s) => pure s | _ => IO.eprintln "receipt: blueprint_hash not string"; return 1
      if ch.length ≠ 64 || !isHexLower ch then IO.eprintln "receipt: cert_hash must be 64 lowercase hex"; return 1
      if bh.length ≠ 64 || !isHexLower bh then IO.eprintln "receipt: blueprint_hash must be 64 lowercase hex"; return 1
      -- Certificate minimal checks
      let certRaw ← match (← readFileE certPath) with | .ok s => pure s | .error m => IO.eprintln m; return 1
      let certJ ← match Json.parse certRaw with | .ok j => pure j | .error e => IO.eprintln e; return 1
      match requireKeys certJ ["inputs","omega","digests","rewrites"] with
      | .ok _ => pure ()
      | .error e => IO.eprintln s!"cert_pk.json schema error: {e}"; return 1
      let certObj ← match certJ.getObj? with | .ok o => pure o | .error _ => IO.eprintln "cert: not object"; return 1
      -- digests checks
      let dObj ← match certObj.get? "digests" with | some (.obj o) => pure o | _ => IO.eprintln "cert: digests not object"; return 1
      let some (.str omegaHex) := dObj.get? "omega" | IO.eprintln "cert: digests.omega missing"; return 1
      let some (.str stmtHex) := dObj.get? "stmt" | IO.eprintln "cert: digests.stmt missing"; return 1
      if !isHexPrefixed omegaHex then IO.eprintln "cert: digests.omega must be 0x-hex"; return 1
      if !isHexPrefixed stmtHex then IO.eprintln "cert: digests.stmt must be 0x-hex"; return 1
      IO.println "schemas: ok"
      return 0
  | _ =>
      IO.eprintln "usage: lake exe pk_validate_schemas <outdir>"; return 2

end PKValidateSchemas
end CLI
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.PKValidateSchemas.main args
