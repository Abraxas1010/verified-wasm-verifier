import Lean
import Lean.Data.Json
import HeytingLean.CLI.Certified.Json
import HeytingLean.Certified.Compose

open Lean
open HeytingLean.CLI.Certified
open HeytingLean.Certified

def main (args : List String) : IO UInt32 := do
  match (← readInputJson args) with
  | .error e => die e
  | .ok j =>
      let fId? := getString? j "f_id"
      let gId? := getString? j "g_id"
      match fId?, gId? with
      | some fId, some gId =>
          match CertifiedLibrary.compose? CertifiedLibrary.demo fId gId with
          | some comp => okJson (toJson comp)
          | none => die s!"cannot compose: {fId} ∘ {gId}"
      | _, _ =>
          die "expected JSON with string keys: f_id, g_id"
