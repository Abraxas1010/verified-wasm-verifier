import Lean
import Lean.Data.Json
import HeytingLean.CLI.Certified.Json
import HeytingLean.Certified.Compose
import HeytingLean.Certified.Modality

open Lean
open HeytingLean.CLI.Certified
open HeytingLean.Certified

private def collectStrings? : List Json → Option (List String)
  | [] => some []
  | (.str s) :: xs => (collectStrings? xs).map (s :: ·)
  | _ :: _ => none

private def getStringList? (j : Json) (k : String) : Option (List String) :=
  match j.getObjVal? k with
  | .ok (.arr xs) => collectStrings? xs.toList
  | _ => none

private def foldCompose?
    (lib : CertifiedLibrary) (acc : CertifiedProgram) (rest : List ProgramId) : Option CertifiedProgram :=
  match rest with
  | [] => some acc
  | id :: ids =>
      match lib.find? id with
      | none => none
      | some next =>
          match CertifiedLibrary.composePrograms? next acc with
          | none => none
          | some acc' => foldCompose? lib acc' ids

private def composePipeline? (lib : CertifiedLibrary) (ids : List ProgramId) : Option CertifiedProgram :=
  match ids with
  | [] => none
  | id0 :: rest =>
      match lib.find? id0 with
      | none => none
      | some p0 => foldCompose? lib p0 rest

def main (args : List String) : IO UInt32 := do
  match (← readInputJson args) with
  | .error e => die e
  | .ok j =>
      let ids? := getStringList? j "ids"
      let reqPropsRaw := getStringList? j "required_properties" |>.getD []
      let modName? := getString? j "modality"
      let modality? := modName?.bind ModalityProfile.ofName?
      match ids? with
      | none =>
          die "expected JSON with key ids: [string]"
      | some ids =>
          let lib := CertifiedLibrary.demo
          match composePipeline? lib ids with
          | none =>
              die "pipeline composition failed (missing program id or type mismatch)"
          | some final =>
              let reqProps : List Property :=
                reqPropsRaw.filterMap Property.ofString?
              let missing : List Property :=
                reqProps.filter (fun p => decide (p ∉ final.properties))
              let modOk :=
                match modality? with
                | none => true
                | some m => m.admissible final.invariants
              let ok := missing.isEmpty && modOk
              let out :=
                Json.mkObj
                  [ ("ok", Json.bool ok)
                  , ("pipeline", toJson (ids.map Json.str |>.toArray))
                  , ("final", toJson final.header)
                  , ("missing_properties", toJson (missing.map toJson |>.toArray))
                  , ("modality", match modality? with | some m => toJson m | none => Json.null)
                  ]
              IO.println out.compress
              pure (if ok then 0 else 1)
