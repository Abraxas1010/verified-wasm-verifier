import Lean
import Lean.Data.Json
import HeytingLean.CLI.Certified.Json
import HeytingLean.Certified.Query

open Lean
open HeytingLean.CLI.Certified
open HeytingLean.Certified

private def parseOptTy (j : Json) (k : String) : Except String (Option Ty) :=
  match getString? j k with
  | none => .ok none
  | some s =>
      match Ty.ofString? s with
      | some t => .ok (some t)
      | none => .error s!"unknown {k}: {s}"

private def parseOptProperty (j : Json) (k : String) : Except String (Option Property) :=
  match getString? j k with
  | none => .ok none
  | some s =>
      match Property.ofString? s with
      | some p => .ok (some p)
      | none => .error s!"unknown {k}: {s}"

private def parseOptModality (j : Json) (k : String) : Except String (Option ModalityProfile) :=
  match getString? j k with
  | none => .ok none
  | some s =>
      match ModalityProfile.ofName? s with
      | some m => .ok (some m)
      | none => .error s!"unknown {k}: {s}"

def main (args : List String) : IO UInt32 := do
  match (← readInputJson args) with
  | .error e => die e
  | .ok j =>
      match parseOptTy j "dom", parseOptTy j "cod", parseOptProperty j "property", parseOptModality j "modality" with
      | .ok dom?, .ok cod?, .ok prop?, .ok mod? =>
          let q : Query := { dom? := dom?, cod? := cod?, property? := prop?, modality? := mod? }
          let headers := CertifiedLibrary.demo.queryHeaders q
          okJson <|
            Json.mkObj
              [ ("count", Json.num headers.length)
              , ("programs", toJson (headers.map toJson |>.toArray))
              ]
      | .error e, _, _, _ => die e
      | _, .error e, _, _ => die e
      | _, _, .error e, _ => die e
      | _, _, _, .error e => die e
