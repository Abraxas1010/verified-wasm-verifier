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

private def collectNats? : List Json → Option (List Nat)
  | [] => some []
  | x :: xs =>
      match x.getNat? with
      | .ok n => (collectNats? xs).map (n :: ·)
      | .error _ => none

private def collectInts? : List Json → Option (List Int)
  | [] => some []
  | x :: xs =>
      match x.getInt? with
      | .ok n => (collectInts? xs).map (n :: ·)
      | .error _ => none

private def getStringList? (j : Json) (k : String) : Option (List String) :=
  match j.getObjVal? k with
  | .ok (.arr xs) => collectStrings? xs.toList
  | _ => none

private def getNatList? (j : Json) (k : String) : Option (List Nat) :=
  match j.getObjVal? k with
  | .ok (.arr xs) => collectNats? xs.toList
  | _ => none

private def getIntList? (j : Json) (k : String) : Option (List Int) :=
  match j.getObjVal? k with
  | .ok (.arr xs) => collectInts? xs.toList
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

private def getInputNat? (j : Json) : Option Nat :=
  getNat? j "input"

private def getInputInt? (j : Json) : Option Int :=
  getInt? j "input"

private def getInputListNat? (j : Json) : Option (List Nat) :=
  getNatList? j "input"

private def getInputListInt? (j : Json) : Option (List Int) :=
  getIntList? j "input"

private def getInputU32? (j : Json) : Option UInt32 :=
  getNat? j "input" |>.map UInt32.ofNat

private def toJsonListNat (xs : List Nat) : Json :=
  Json.arr (xs.map toJson |>.toArray)

private def toJsonListInt (xs : List Int) : Json :=
  Json.arr (xs.map toJson |>.toArray)

private def toJsonU32 (x : UInt32) : Json :=
  toJson x.toNat

private def toJsonVal : (t : Ty) → t.interp → Json
  | .nat, x => toJson x
  | .int, x => toJson x
  | .listNat, xs => toJsonListNat xs
  | .u32, x => toJsonU32 x
  | .prod a b, x => Json.arr #[toJsonVal a x.1, toJsonVal b x.2]

private def parseVal? : (t : Ty) → Json → Option t.interp
  | .nat, j =>
      match j.getNat? with
      | .ok n => some n
      | .error _ => none
  | .int, j =>
      match j.getInt? with
      | .ok i => some i
      | .error _ => none
  | .listNat, j =>
      match j with
      | .arr xs => collectNats? xs.toList
      | _ => none
  | .u32, j =>
      match j.getNat? with
      | .ok n => some (UInt32.ofNat n)
      | .error _ => none
  | .prod a b, j =>
      match j with
      | .arr xs =>
          match xs.toList with
          | [ja, jb] =>
              match parseVal? a ja, parseVal? b jb with
              | some xa, some xb => some (xa, xb)
              | _, _ => none
          | _ => none
      | _ => none

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
              let verificationOk := missing.isEmpty && modOk

              let outVal? : Option Json := do
                let inJ ←
                  match j.getObjVal? "input" with
                  | .ok v => some v
                  | .error _ => none
                let x ← parseVal? final.dom inJ
                return toJsonVal final.cod (final.fn x)

              match outVal? with
              | none =>
                  die "expected JSON input compatible with pipeline domain under key input"
              | some outVal =>
                  let out :=
                    Json.mkObj
                      [ ("ok", Json.bool true)
                      , ("pipeline", toJson (ids.map Json.str |>.toArray))
                      , ("final", toJson final.header)
                      , ("output", outVal)
                      , ("verification_ok", Json.bool verificationOk)
                      , ("missing_properties", toJson (missing.map toJson |>.toArray))
                      , ("modality", match modality? with | some m => toJson m | none => Json.null)
                      ]
                  IO.println out.compress
                  pure 0
