import Lean
import Std
import Lean.Data.Json
import HeytingLean.Util.JCS
import HeytingLean.BountyHunter.AlgebraIR.Types
import HeytingLean.BountyHunter.AlgebraIR.Json
import HeytingLean.BountyHunter.AlgebraIR.Replay

/-!
# HeytingLean.BountyHunter.AlgebraIR.ToyEVMReplay

Toy concrete replay of an `AlgebraIR.Replay.Trace`.

This is not a full EVM semantics. It is an executable checkpoint that:
- deterministically interprets storage read/write and boundary call effects,
- produces a replay report that can be consumed by downstream tooling,
- validates CEI-style witness properties on the observed trace.
-/

namespace HeytingLean.BountyHunter.AlgebraIR
namespace ToyEVMReplay

open Lean
open Lean.Json
open HeytingLean.BountyHunter.AlgebraIR

structure StorageKV where
  slot : Nat
  value : Nat
  deriving Repr, DecidableEq, Inhabited

structure State where
  storage : Std.HashMap Nat Nat := {}
  calls : Array String := #[]
  reads : Array Nat := #[]
  writes : Array Nat := #[]
  readsDyn : Array String := #[]
  writesDyn : Array String := #[]
  deriving Inhabited

private def stateToStorageArray (s : State) : Array StorageKV :=
  Id.run do
    let mut out : Array StorageKV := #[]
    for (k, v) in s.storage.toList do
      out := out.push { slot := k, value := v }
    out.qsort (fun a b => a.slot < b.slot)

structure Event where
  idx : Nat
  node : NodeId
  tag : String
  effects : Array Effect := #[]
  storageAfter : Array StorageKV := #[]
  deriving Repr, DecidableEq, Inhabited

structure Report where
  version : String := "algebrair.toy_evm_replay.v1"
  slot : Nat
  slotExpr? : Option String := none
  verdict : String
  boundaryIndex? : Option Nat := none
  writeIndex? : Option Nat := none
  stateFinal : Array StorageKV := #[]
  calls : Array String := #[]
  events : Array Event := #[]
  deriving Repr, DecidableEq, Inhabited

private def storageKVToJson (kv : StorageKV) : Json :=
  Json.mkObj [("slot", Json.num kv.slot), ("value", Json.num kv.value)]

private def eventToJson (e : Event) : Json :=
  Json.mkObj
    [ ("idx", Json.num e.idx)
    , ("node", Json.num e.node)
    , ("tag", Json.str e.tag)
    , ("effects", Json.arr (e.effects.map HeytingLean.BountyHunter.AlgebraIR.effectToJson))
    , ("storageAfter", Json.arr (e.storageAfter.map storageKVToJson))
    ]

def reportToJson (r : Report) : Json :=
  let base :=
    [ ("version", Json.str r.version)
    , ("slot", Json.num r.slot)
    , ("verdict", Json.str r.verdict)
    , ("calls", Json.arr (r.calls.map Json.str))
    , ("stateFinal", Json.arr (r.stateFinal.map storageKVToJson))
    , ("events", Json.arr (r.events.map eventToJson))
    ]
  let base :=
    match r.slotExpr? with
    | none => base
    | some s => base ++ [("slotExpr", Json.str s)]
  let base :=
    match r.boundaryIndex? with
    | none => base
    | some i => base ++ [("boundaryIndex", Json.num i)]
  let base :=
    match r.writeIndex? with
    | none => base
    | some i => base ++ [("writeIndex", Json.num i)]
  Json.mkObj base

def reportCanonicalString (r : Report) : String :=
  HeytingLean.Util.JCS.canonicalString (reportToJson r)

private def updateIndexMin (cur : Option Nat) (i : Nat) : Option Nat :=
  match cur with
  | none => some i
  | some j => some (min i j)

private def applyEffect (slot : Nat) (idx : Nat) (eff : Effect) (s : State) :
    State × Option Nat × Option Nat :=
  match eff with
  | .storageRead k =>
      let reads := if k = slot then s.reads.push k else s.reads
      ({ s with reads := reads }, none, none)
  | .storageReadDyn se =>
      ({ s with readsDyn := s.readsDyn.push se }, none, none)
  | .storageWrite k =>
      if k = slot then
        let s' : State :=
          { s with
            storage := s.storage.insert k 0
            writes := s.writes.push k }
        (s', none, some idx)
      else
        ({ s with storage := s.storage.insert k 0 }, none, none)
  | .storageWriteDyn se =>
      ({ s with writesDyn := s.writesDyn.push se }, none, none)
  | .boundaryCall target =>
      let s' : State := { s with calls := s.calls.push target }
      (s', some idx, none)

private def runWith (slot : Nat) (slotExpr? : Option String) (t : Replay.Trace) : Report :=
  Id.run do
    let mut s : State := {}
    let mut boundaryIdx? : Option Nat := none
    let mut writeIdx? : Option Nat := none
    let mut events : Array Event := #[]
    for h in [:t.path.size] do
      let step := t.path[h]!
      let mut s2 := s
      let mut b2 := boundaryIdx?
      let mut w2 := writeIdx?
      for eff in step.effects do
        let (s3, b?, w?) := applyEffect slot h eff s2
        s2 := s3
        if let some bi := b? then
          b2 := updateIndexMin b2 bi
        if let some wi := w? then
          w2 := updateIndexMin w2 wi
        -- Dynamic selection: record the first matching dyn-write index.
        match slotExpr?, eff with
        | some sel, .storageWriteDyn se =>
            if se = sel then
              w2 := updateIndexMin w2 h
        | _, _ => pure ()
      let storageAfter := stateToStorageArray s2
      events := events.push { idx := h, node := step.node, tag := step.tag, effects := step.effects, storageAfter := storageAfter }
      s := s2
      boundaryIdx? := b2
      writeIdx? := w2

    let verdict :=
      match boundaryIdx?, writeIdx? with
      | none, _ => "NO_BOUNDARY"
      | some _, none => "VULNERABLE (boundary before write)"
      | some b, some w =>
          if b < w then
            "VULNERABLE (boundary before write)"
          else
            "SAFE (write before boundary)"
    { slot := slot
      slotExpr? := slotExpr?
      verdict := verdict
      boundaryIndex? := boundaryIdx?
      writeIndex? := writeIdx?
      stateFinal := stateToStorageArray s
      calls := s.calls
      events := events
    }

def run (slot : Nat) (t : Replay.Trace) : Report :=
  runWith slot none t

def runSlotExpr (slotExpr : String) (t : Replay.Trace) : Report :=
  runWith 0 (some slotExpr) t

end ToyEVMReplay
end HeytingLean.BountyHunter.AlgebraIR
