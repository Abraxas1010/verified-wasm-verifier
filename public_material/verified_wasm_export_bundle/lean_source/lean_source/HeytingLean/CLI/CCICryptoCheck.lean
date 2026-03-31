import Lean
import Lean.Data.Json
import HeytingLean.CCI.Core
import HeytingLean.CCI.Json
import HeytingLean.CCI.Cert
import HeytingLean.CCI.Check
import HeytingLean.CLI.Args

/-
# cci_crypto_check CLI

Specialised checker for crypto certificates. It reuses the same core
logic as `cci_check` but is intended to be paired with
`cci_crypto_export` and the property IDs from `CCI.CryptoSpecs`.
-/

namespace HeytingLean
namespace CLI
namespace CCICryptoCheck

open HeytingLean.CCI

def usage : String :=
  "usage: cci_crypto_check [PATH] [--cert PATH]  (env fallback: CCI_CERT_PATH)"

private def checkFile (p : String) : IO Unit := do
  let fp := System.FilePath.mk p
  if !(← fp.pathExists) then
    IO.eprintln "E-CERT-OPEN"
    IO.Process.exit 2
  let s ← IO.FS.readFile fp
  -- parse JSON and extract omega + omega digest hex
  match Lean.Json.parse s with
  | .error _ =>
      IO.eprintln "E-CERT-JSON"
      IO.Process.exit 2
  | .ok j =>
      match j.getObj? with
      | .error _ =>
          IO.eprintln "invalid certificate JSON object"
          IO.Process.exit 2
      | .ok o =>
          -- decode omega
          let omega? := (o.get? "omega") >>= decodeExpr
          -- digests: find entry where path = "omega"
          let hex? : Option String := Id.run do
            match o.get? "digests" with
            | some (.arr a) =>
                let rec go (i : Nat) : Option String :=
                  if h : i < a.size then
                    have _ := h
                    match (a[i]!).getObj? with
                    | .ok oi =>
                        match (oi.get? "path", oi.get? "digest") with
                        | (some (.str p), some (.str hex)) =>
                            if p = "omega" then some hex else go (i+1)
                        | _ => go (i+1)
                    | _ => go (i+1)
                  else none
                go 0
            | _ => none
          match (omega?, hex?) with
          | (some omega, some hex) =>
              -- idempotence check
              let c1 := HeytingLean.CCI.canon omega
              let c2 := HeytingLean.CCI.canon c1
              if c1 ≠ c2 then
                IO.eprintln "E-IDEMP"
                IO.Process.exit 1
              -- compute expected hex string from canon(omega)
              let expD := HeytingLean.CCI.hashExpr (HeytingLean.CCI.canon omega)
              let expHex := match HeytingLean.CCI.encodeDigest expD with | Lean.Json.str s => s | _ => ""
              if expHex = hex then
                IO.println "cci_crypto_check: ok"
              else
                IO.eprintln "E-DIGEST-MISMATCH"
                IO.Process.exit 1
          | _ =>
              IO.eprintln "missing omega/digest in certificate"
              IO.Process.exit 2

def run (argv : List String) : IO Unit := do
  let argv := HeytingLean.CLI.stripLakeArgs argv
  -- precedence: positional PATH > --cert PATH > env
  let posPath? := argv.findSome? (fun s => if s.startsWith "--" then none else some s)
  let rec findFlag (xs : List String) : Option String :=
    match xs with
    | [] => none
    | "--cert" :: p :: _ => some p
    | _ :: rest => findFlag rest
  let flagPath? := findFlag argv
  let envPath? := (← IO.getEnv "CCI_CERT_PATH")
  match (posPath? <|> flagPath? <|> envPath?) with
  | some p => checkFile p
  | none =>
      IO.eprintln usage
      IO.Process.exit 2

end CCICryptoCheck
end CLI
end HeytingLean

def main (argv : List String) : IO Unit :=
  HeytingLean.CLI.CCICryptoCheck.run argv
