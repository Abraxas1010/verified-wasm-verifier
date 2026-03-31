/-
  Offline exporter for a tiny Ωᴿ proof IR:
  Γ = [A] ⊢ OrR A B   via OrRI (Hyp A)
-/
import Lean
import HeytingLean.CLI.Args

open Lean

namespace HeytingLean.CLI.ExportOmegaR

/- Build the tiny IR object(s) exactly as in the schema, without depending on OmegaR types -/
def irOrIntroJson : Json :=
  let A : Json := Json.mkObj [("tag", Json.str "Var"), ("name", Json.str "A")]
  let B : Json := Json.mkObj [("tag", Json.str "Var"), ("name", Json.str "B")]
  let hypsJ : Json := Json.arr #[A]
  let goalJ : Json := Json.mkObj [("tag", Json.str "OrR"), ("left", A), ("right", B)]
  let deriv  : Json :=
    Json.mkObj [
      ("rule", Json.str "OrRI"),
      ("concl", goalJ),
      ("child", Json.mkObj [
         ("rule", Json.str "Hyp"),
         ("concl", A),
         ("hypFormula", A)
      ])
    ]
  let syms := Json.arr (#["A","B","C"].map Json.str)
  Json.mkObj [
    ("version",    Json.str "1.0.0"),
    ("logic_kind", Json.str "heyting"),     -- kernel is logic-agnostic; compute harness remains boolean-only
    ("carrier_id", Json.str "bool3"),
    ("nucleus_id", Json.str "join_const_1"),
    ("symbols",    syms),
    ("hyps",       hypsJ),
    ("goal",       goalJ),
    ("derivation", deriv)
  ]

def irImpIntroJson : Json :=
  let A : Json := Json.mkObj [("tag", Json.str "Var"), ("name", Json.str "A")]
  let hypsJ : Json := Json.arr #[]
  let goalJ : Json := Json.mkObj [("tag", Json.str "ImpR"), ("left", A), ("right", A)]
  let deriv  : Json :=
    Json.mkObj [
      ("rule", Json.str "ImpI"),
      ("assume", A),
      ("concl", goalJ),
      ("child", Json.mkObj [
         ("rule", Json.str "Hyp"),
         ("concl", A),
         ("hypFormula", A)
      ])
    ]
  let syms := Json.arr (#["A","B"].map Json.str)
  Json.mkObj [
    ("version",    Json.str "1.0.0"),
    ("logic_kind", Json.str "heyting"),
    ("carrier_id", Json.str "bool3"),
    ("nucleus_id", Json.str "join_const_1"),
    ("symbols",    syms),
    ("hyps",       hypsJ),
    ("goal",       goalJ),
    ("derivation", deriv)
  ]

def writeFile (path : System.FilePath) (s : String) : IO Unit := do
  if let some d := path.parent then
    if (← d.pathExists) = false then IO.FS.createDirAll d
  IO.FS.writeFile path s

/-- CLI: lake exe export_omegaR [--demo or|imp] [--out artifacts/lean_omegaR_proof.json] -/
def run (argv : List String) : IO Unit := do
  let argv := HeytingLean.CLI.stripLakeArgs argv
  let rec loop (args : List String) (demo : String) (out : String) : IO (String × String) := do
    match args with
    | "--demo" :: d :: rest => loop rest d out
    | "--out"  :: p :: rest => loop rest demo p
    | _ :: rest => loop rest demo out
    | [] => pure (demo, out)
  let (demo, out) ← loop argv "or" "artifacts/lean_omegaR_proof.json"
  let j := if demo == "imp" then irImpIntroJson else irOrIntroJson
  let s := j.pretty
  let outPath := System.FilePath.mk out
  IO.eprintln s!"[export_omegaR] writing {out}"
  writeFile outPath s

end HeytingLean.CLI.ExportOmegaR

def main (argv : List String) : IO Unit := HeytingLean.CLI.ExportOmegaR.run argv
