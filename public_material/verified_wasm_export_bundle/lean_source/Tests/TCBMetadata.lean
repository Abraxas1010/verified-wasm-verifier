import Lean
import HeytingLean.TCB.Metadata

open HeytingLean
open HeytingLean.TCB
open Lean

private def expect (cond : Bool) (msg : String) : IO Unit :=
  if cond then pure () else throw <| IO.userError msg

private def expectStringField (obj : Json) (key label : String) : IO Unit := do
  match obj.getObjVal? key with
  | Except.ok (.str s) => expect (!s.trim.isEmpty) s!"{label} must not be empty"
  | _ => throw <| IO.userError s!"Missing string field {label}"

private def expectObjectField (obj : Json) (key label : String) : IO Json := do
  match obj.getObjVal? key with
  | Except.ok j@(.obj _) => pure j
  | _ => throw <| IO.userError s!"Missing object field {label}"

/-- Smoke test: ensure metadata JSON contains required fields per schema. -/
def main (_args : List String) : IO UInt32 := do
  let snapshot ← current
  let json := Metadata.toJson snapshot
  expectStringField json "lean_version" "lean_version"
  expectStringField json "project_commit" "project_commit"
  expectStringField json "mathlib_commit" "mathlib_commit"
  expectStringField json "os" "os"
  expectStringField json "arch" "arch"
  expectStringField json "timestamp" "timestamp"
  let compilerJson ← expectObjectField json "compiler" "compiler"
  expectStringField compilerJson "name" "compiler.name"
  expectStringField compilerJson "version" "compiler.version"
  match compilerJson.getObjVal? "flags" with
  | Except.ok (.str _) => pure ()
  | _ => throw <| IO.userError "Missing compiler.flags"
  let backendJson ← expectObjectField json "backend" "backend"
  expectStringField backendJson "type" "backend.type"
  match backendJson.getObjVal? "details" with
  | Except.ok (.str _) => pure ()
  | _ => throw <| IO.userError "Missing backend.details"
  let theoremsJson ← expectObjectField json "theorems" "theorems"
  expectStringField theoremsJson "format" "theorems.format"
  expectStringField theoremsJson "manifest_version" "theorems.manifest_version"
  match theoremsJson.getObjVal? "theorem_count" with
  | Except.ok (.num _) => pure ()
  | _ => throw <| IO.userError "Missing theorems.theorem_count"
  let theoremsManifest ← expectObjectField json "theorems_manifest" "theorems_manifest"
  expectStringField theoremsManifest "path" "theorems_manifest.path"
  expectStringField theoremsManifest "sha256" "theorems_manifest.sha256"
  pure 0
