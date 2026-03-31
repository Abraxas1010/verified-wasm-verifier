import Lean
import Lean.Data.Json
import HeytingLean.CCI.Core
import HeytingLean.CCI.Json
import HeytingLean.CCI.Cert
import HeytingLean.CCI.Check
import HeytingLean.Crypto.ZK.CLI.ProveFromCert

open Lean
open HeytingLean
open HeytingLean.CCI
open HeytingLean.Crypto.ZK.CLI

/-- Write a minimal cert JSON directly (no CLI dependency). -/
def writeCert (p : System.FilePath) : IO Unit := do
  let inputs : List (String × String) := [
    ("chainId","1"),("paymentManager","0xPM"),("walletAddress","0xWALLET"),("hashedId","0xID"),
    ("policyCommit","0xPOLICY"),("stateCommit_pre","s0"),("stateCommit_post","s1"),("epoch","0"),
    ("recipient","alice"),("amount","42"),("budget_id","0"),("nullifier","0x00"),
    ("IRv", IRv),("rewriteTablev", RewriteTablev),("canonv", Canonv),("circuitv", Circuitv)]
  let omega := Expr.impR (Expr.atom "P") (Expr.atom "Q")
  let omegaD := hashExpr (canon omega)
  let hex :=
    let parts := omegaD.toList.map (fun b =>
      let s := (Nat.toDigits 16 b.toNat).asString
      if s.length = 1 then "0" ++ s else s)
    String.intercalate "" parts
  let inputsJson := Json.arr <| Array.mk <|
    inputs.map (fun (k,v) => Json.mkObj [("k", Json.str k), ("v", Json.str v)])
  let j := Json.mkObj [
    ("inputs", inputsJson),
    ("omega", (Json.mkObj [("tag", Json.str "impR"), ("a", Json.mkObj [("tag", Json.str "atom"), ("id", Json.str "P")]), ("b", Json.mkObj [("tag", Json.str "atom"), ("id", Json.str "Q")])])),
    ("lenses", Json.arr #[]),
    ("rewrites", Json.arr #[]),
    ("digests", Json.arr #[Json.mkObj [("path", Json.str "omega"), ("digest", Json.str hex)]])
  ]
  IO.FS.writeFile p j.compress

/-- Read, tamper omega digest, and write to another path. -/
def tamperOmegaDigest (src dst : System.FilePath) : IO Unit := do
  let s ← IO.FS.readFile src
  match Json.parse s with
  | .error _ => pure ()
  | .ok j =>
    match j.getObj? with
    | .error _ => pure ()
    | .ok o =>
      match o.get? "digests" with
      | some (.arr a) =>
          -- rebuild digests with flipped first hex char of omega
          let rec go (i : Nat) (acc : List Json) : List Json :=
            if h : i < a.size then
              have _ := h
              match (a[i]!).getObj? with
              | .ok oi =>
                match (oi.get? "path", oi.get? "digest") with
                | (some (.str p), some (.str hex)) =>
                    let hex' := if hex.length > 0 then "0" ++ hex.drop 1 else hex
                    let oi' := Json.mkObj [("path", Json.str p), ("digest", Json.str hex')]
                    go (i+1) (oi' :: acc)
                | _ => go (i+1) acc
              | _ => go (i+1) acc
            else acc.reverse
          let dig' := Json.arr (Array.mk (go 0 []))
          let o' := Json.mkObj [
            ("inputs", (o.get? "inputs").getD Json.null),
            ("omega", (o.get? "omega").getD Json.null),
            ("lenses", (o.get? "lenses").getD (Json.arr #[])),
            ("rewrites", (o.get? "rewrites").getD (Json.arr #[])),
            ("digests", dig')
          ]
          IO.FS.writeFile dst o'.compress
      | _ => pure ()

/-- Replace omega with (andR (atom "Q") (atom "R")) and fix digests. -/
def makeFixedPointFail (src dst : System.FilePath) : IO Unit := do
  let s ← IO.FS.readFile src
  match Json.parse s with
  | .error _ => pure ()
  | .ok j =>
    match j.getObj? with
    | .error _ => pure ()
    | .ok o =>
      let omegaNew := Json.mkObj [
        ("tag", Json.str "andR"),
        ("a", Json.mkObj [("tag", Json.str "atom"), ("id", Json.str "Q")]),
        ("b", Json.mkObj [("tag", Json.str "atom"), ("id", Json.str "R")])
      ]
      -- recompute omega digest using Lean-side hash to keep parity
      let e? := HeytingLean.CCI.decodeExpr omegaNew
      match e? with
      | none => pure ()
      | some e =>
        let d := HeytingLean.CCI.hashExpr (HeytingLean.CCI.canon e)
        let hex :=
          let parts := d.toList.map (fun b =>
            let s := (Nat.toDigits 16 b.toNat).asString
            if s.length = 1 then "0" ++ s else s)
          String.intercalate "" parts
        -- rebuild digests
        let dig' := Json.arr #[Json.mkObj [("path", Json.str "omega"), ("digest", Json.str hex)]]
        let o' := Json.mkObj [
          ("inputs", (o.get? "inputs").getD Json.null),
          ("omega", omegaNew),
          ("lenses", (o.get? "lenses").getD (Json.arr #[])),
          ("rewrites", (o.get? "rewrites").getD (Json.arr #[])),
          ("digests", dig')
        ]
        IO.FS.writeFile dst o'.compress

/- Prover semantics tests (compile-time initialize smoke) -/
initialize
  let base := System.FilePath.mk "/tmp"
  let cert := base / "cci_prover_cert.json"
  let certTam := base / "cci_prover_cert_tamper.json"
  let certFix := base / "cci_prover_cert_fixfail.json"
  -- positive: export → verify
  writeCert cert
  let ok1 ← ProveFromCert.verifyCertAtPath cert.toString
  IO.println s!"prover-positive: {ok1}"
  -- negative: tamper digest
  tamperOmegaDigest cert certTam
  let ok2 ← ProveFromCert.verifyCertAtPath certTam.toString
  IO.println s!"prover-negative-digest: {ok2}"
  -- negative: fixed-point fail (omega=Q∧R; core C includes p)
  makeFixedPointFail cert certFix
  let ok3 ← ProveFromCert.verifyCertAtPathWithCore certFix.toString ["p"]
  IO.println s!"prover-negative-fixpoint: {ok3}"
