import Lean
import Lean.Data.Json
import HeytingLean.BountyHunter.EvmTrace.Types

namespace HeytingLean.BountyHunter.EvmTrace

open Lean
open Lean.Json

private def expectObj (j : Json) : Except String Json := do
  match j.getObj? with
  | .ok _ => pure j
  | .error _ => throw "expected JSON object"

private def getStrField? (obj : Json) (k : String) : Option String :=
  match obj.getObjVal? k with
  | .ok v =>
      match v.getStr? with
      | .ok s => some s
      | .error _ => none
  | .error _ => none

private def getObjField? (obj : Json) (k : String) : Option Json :=
  match obj.getObjVal? k with
  | .ok v =>
      match v.getObj? with
      | .ok _ => some v
      | .error _ => none
  | .error _ => none

def eventOfJsonE (j : Json) : Except String Event := do
  let obj ← expectObj j
  let op ←
    match getStrField? obj "op" with
    | some s => pure s
    | none => throw "missing field 'op'"

  let sload :=
    match getObjField? obj "sload" with
    | none => none
    | some o =>
        match getStrField? o "key" with
        | some key => some { key := key }
        | none => none

  let sstore :=
    match getObjField? obj "sstore" with
    | none => none
    | some o =>
        match getStrField? o "key" with
        | none => none
        | some key =>
            let value := getStrField? o "value"
            some { key := key, value := value }

  let boundary :=
    match getObjField? obj "boundary" with
    | none => none
    | some o =>
        match getStrField? o "kind", getStrField? o "to" with
        | some kind, some to =>
            let value := getStrField? o "value"
            let gas := getStrField? o "gas"
            some { kind := kind, to := to, value := value, gas := gas }
        | _, _ => none

  pure { op := op, sload := sload, sstore := sstore, boundary := boundary }

def traceOfJsonE (j : Json) : Except String Trace := do
  let obj ← expectObj j
  let version :=
    match obj.getObjVal? "version" with
    | .ok v =>
        match v.getStr? with
        | .ok s => s
        | .error _ => "evm_observer_trace.v0"
    | .error _ => "evm_observer_trace.v0"
  let evsVal ←
    match obj.getObjVal? "events" with
    | .ok v => pure v
    | .error _ => throw "missing field 'events'"
  let evsArr ←
    match evsVal.getArr? with
    | .ok a => pure a
    | .error _ => throw "field 'events' not an array"
  let mut evs : Array Event := #[]
  for e in evsArr do
    match eventOfJsonE e with
    | .ok ev => evs := evs.push ev
    | .error _ => continue
  pure { version := version, events := evs }

end HeytingLean.BountyHunter.EvmTrace
