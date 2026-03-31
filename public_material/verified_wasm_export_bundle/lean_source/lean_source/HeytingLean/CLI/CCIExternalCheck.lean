import Lean
import Lean.Data.Json
import HeytingLean.CCI.Core
import HeytingLean.CCI.Json
import HeytingLean.CCI.Cert
import HeytingLean.CCI.Check
import HeytingLean.CCI.CryptoSpecs
import HeytingLean.Crypto.Registry
import HeytingLean.CLI.Args

/-
# cci_external_check CLI

Specialised checker for externally generated CCI certificates.

It reuses the same core logic as `cci_check`, but additionally reports
the canonical omega expression and, when possible, a slug for atom-only
omegas so that results can be correlated with master-list properties.
-/

namespace HeytingLean
namespace CLI
namespace CCIExternalCheck

open HeytingLean.CCI
open HeytingLean.CCI.CryptoSpecs
open HeytingLean.Crypto

def usage : String :=
  "usage: cci_external_check [PATH] [--cert PATH]  (env fallback: CCI_EXTERNAL_CERT_PATH or CCI_CERT_PATH)"

private def checkFile (p : String) : IO Unit := do
  let fp := System.FilePath.mk p
  if !(← fp.pathExists) then
    IO.eprintln "E-CERT-OPEN"
    IO.Process.exit 2
  let s ← IO.FS.readFile fp
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
          -- rewrites (optional): array of rule ids
          let rws : List RuleId :=
            match o.get? "rewrites" with
            | some (.arr a) =>
                a.toList.filterMap (fun j =>
                  match j.getNat? with
                  | .ok n => some n
                  | .error _ =>
                      match j with
                      | .str s => s.toNat?
                      | _ => none)
            | _ => []
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
              let omega' := HeytingLean.CCI.applyRewrites omega rws
              -- canonicalise and check idempotence
              let c1 := HeytingLean.CCI.canon omega'
              let c2 := HeytingLean.CCI.canon c1
              if c1 ≠ c2 then
                IO.eprintln "E-IDEMP"
                IO.Process.exit 1
              -- compute expected hex string from canon(omega)
              let expD := HeytingLean.CCI.hashExpr c1
              let expHex := match HeytingLean.CCI.encodeDigest expD with
                            | Lean.Json.str s => s
                            | _ => ""
              if expHex = hex then
                let slug? :=
                  match c1 with
                  | Expr.atom id => some id
                  | _ => none
                match slug? with
                | some id =>
                    -- Attempt to resolve the slug to a global crypto property
                    -- and, when available, its master-list key and theorem.
                    let prop? := CryptoSpecs.propertyOfSlug? id
                    match prop? with
                    | some prop =>
                        let key := Crypto.Registry.masterListKey prop
                        let thm? := Crypto.Registry.theoremName? prop
                        let thmStr :=
                          match thm? with
                          | some n => toString n
                          | none => "-"
                        IO.println s!"cci_external_check: ok omega_atom={id} property={key} theorem={thmStr}"
                    | none =>
                        IO.println s!"cci_external_check: ok omega_atom={id}"
                | none =>
                    IO.println "cci_external_check: ok omega_nonatom"
              else
                IO.eprintln "E-DIGEST-MISMATCH"
                IO.Process.exit 1
          | _ =>
              IO.eprintln "missing omega/digest in certificate"
              IO.Process.exit 2

def run (argv : List String) : IO Unit := do
  let argv := HeytingLean.CLI.stripLakeArgs argv
  -- precedence: positional PATH > --cert PATH > CCI_EXTERNAL_CERT_PATH > CCI_CERT_PATH
  let posPath? := argv.findSome? (fun s => if s.startsWith "--" then none else some s)
  let rec findFlag (xs : List String) : Option String :=
    match xs with
    | [] => none
    | "--cert" :: p :: _ => some p
    | _ :: rest => findFlag rest
  let flagPath? := findFlag argv
  let envExt? := (← IO.getEnv "CCI_EXTERNAL_CERT_PATH")
  let envDefault? := (← IO.getEnv "CCI_CERT_PATH")
  match (posPath? <|> flagPath? <|> envExt? <|> envDefault?) with
  | some p => checkFile p
  | none =>
      IO.eprintln usage
      IO.Process.exit 2

end CCIExternalCheck
end CLI
end HeytingLean

def main (argv : List String) : IO Unit :=
  HeytingLean.CLI.CCIExternalCheck.run argv
