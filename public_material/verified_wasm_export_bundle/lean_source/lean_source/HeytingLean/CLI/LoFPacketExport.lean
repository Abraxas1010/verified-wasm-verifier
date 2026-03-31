import Lean
import Lean.Data.Json
import HeytingLean.LoF.Blueprint.PrimordialTheorem
import HeytingLean.CLI.TheoremDiagramExport
import HeytingLean.CLI.Args

/-
# LoFPacketExport CLI

Export a unified "LoF packet" for a theorem:

* Lean-level diagram from `theorem_diagram_export`;
* lightweight LoF blueprint metadata (currently specialised to the residuation law).

This is designed as a simple backend for front-ends that want to show
blueprint/LoF/diagram views side by side.
-/

open Lean
open Lean.Json
open HeytingLean.LoF
open HeytingLean.LoF.Blueprint
open HeytingLean.CLI.TheoremDiagramExport

/-- Minimal packet wrapper combining LoF metadata with a structural diagram
for the residuation theorem. -/
def mkResiduationPacket (mode : String) : IO Json := do
  let constName := "HeytingLean.LoF.Reentry.residuation"
  let diag ← theoremDiagramJson constName mode
  let blueprintMeta : Json :=
    Json.mkObj
      [ ("blueprintKind", Json.str "residuation")
      , ("label",         Json.str "Heyting residuation on Ω_R")
      , ("description",
          Json.str
            "Residuation law in the Heyting core Ω_R: a ⊓ b ≤ c ↔ a ≤ b ⇨ c.")
      , ("regionLhs",     Json.str "a ⊓ b")
      , ("regionRhs",     Json.str "a ⇨ c")
      , ("nucleusLevel",  Json.str "Ω_R (fixed points of R)")
      ]
  pure <|
    Json.mkObj
      [ ("kind",      Json.str "lof-packet")
      , ("const",     Json.str constName)
      , ("mode",      Json.str mode)
      , ("blueprint", blueprintMeta)
      , ("diagram",   diag)
      ]

/-- Fallback packet for arbitrary constants: wrap the structural diagram and
mark the LoF metadata as generic. -/
def mkGenericPacket (constName mode : String) : IO Json := do
  let diag ← theoremDiagramJson constName mode
  let blueprintMeta : Json :=
    Json.mkObj
      [ ("blueprintKind", Json.str "generic")
      , ("label",         Json.str constName)
      , ("description",
          Json.str
            "Generic LoF packet: structural Heyting-style view derived from the Lean type.")
      ]
  pure <|
    Json.mkObj
      [ ("kind",      Json.str "lof-packet")
      , ("const",     Json.str constName)
      , ("mode",      Json.str mode)
      , ("blueprint", blueprintMeta)
      , ("diagram",   diag)
      ]

/-- Usage string for the CLI. -/
private def usage : String :=
  "lof_packet_export --const NAME [--mode MODE]\n" ++
  "  NAME : fully qualified constant name (e.g. HeytingLean.LoF.Reentry.residuation)\n" ++
  "  MODE : optional calculus tag (default: region)"

/-- Parse CLI arguments into `(constName, mode)` if possible. -/
private def parseArgs : List String → Option (String × String)
  | "--const" :: name :: rest =>
      let rec findMode
        | [] => "region"
        | "--mode" :: m :: _ => m
        | _ :: xs => findMode xs
      some (name, findMode rest)
  | _ => none

/-- Entrypoint: emit a LoF packet JSON bundle for a constant, combining
`theorem_diagram_export` output with LoF metadata. -/
def main (argv : List String) : IO UInt32 := do
  let argv := HeytingLean.CLI.stripLakeArgs argv
  match parseArgs argv with
  | none =>
      IO.eprintln usage
      pure 1
  | some (constName, mode) =>
      let j ←
        if constName = "HeytingLean.LoF.Reentry.residuation" then
          mkResiduationPacket mode
        else
          mkGenericPacket constName mode
      IO.println (toString j)
      pure 0
