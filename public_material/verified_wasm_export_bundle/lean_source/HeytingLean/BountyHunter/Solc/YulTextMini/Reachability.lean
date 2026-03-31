import Std
import Lean.Data.Json
import HeytingLean.BountyHunter.Solc.YulTextMini.Types
import HeytingLean.BountyHunter.Solc.YulTextMini.CallInterface
import HeytingLean.BountyHunter.Solc.YulTextMini.Summary

/-!
# HeytingLean.BountyHunter.Solc.YulTextMini.Reachability

Phase 4 (WP4/WP5) MVP: **bounded reachability / hyperproperty checking** over the YulTextMini
extraction surface.

This module intentionally stays coarse:
- it uses the Summary fixpoint closure to approximate internal-call reachability;
- it uses call-interface boundary call tags (e.g. `target_slot=n`, `value=callvalue`) as events;
- it synthesizes small **witness sequences** (k=2) for cross-function properties.

The strategic edge (WP5) is represented as an explicit closure operator `R` over mined facts.
We treat "there exists a reachable violation" as `R(Facts) ⊓ ¬Invariant ≠ ⊥` and report a witness.
-/

namespace HeytingLean.BountyHunter.Solc.YulTextMini

open Std
open Lean

structure ReachabilityFinding where
  version : String := "bh.yultextmini.reachability_finding.v0"
  property : String
  k : Nat
  targetSlot : Nat
  targetSlotRef : String := ""
  writers : Array String
  callers : Array String
  witnessSequences : Array (Array String)
  callSiteFn : String
  call : BoundaryCall
  deriving Inhabited

def ReachabilityFinding.toJson (f : ReachabilityFinding) : Json :=
  Json.mkObj
    [ ("version", Json.str f.version)
    , ("property", Json.str f.property)
    , ("k", Json.num f.k)
    , ("targetSlot", Json.num f.targetSlot)
    , ("targetSlotRef", Json.str f.targetSlotRef)
    , ("writers", Json.arr (f.writers.map Json.str))
    , ("callers", Json.arr (f.callers.map Json.str))
    , ("witnessSequences", Json.arr (f.witnessSequences.map (fun xs => Json.arr (xs.map Json.str))))
    , ("callSiteFn", Json.str f.callSiteFn)
    , ("call", f.call.toJson)
    ]

structure ClosureInvariant where
  version : String := "bh.yultextmini.closure_invariant.v0"
  id : String
  violated : Bool
  reason : String
  properties : Array String
  findings : Array ReachabilityFinding := #[]
  deriving Inhabited

def ClosureInvariant.toJson (i : ClosureInvariant) : Json :=
  Json.mkObj
    [ ("version", Json.str i.version)
    , ("id", Json.str i.id)
    , ("violated", Json.bool i.violated)
    , ("reason", Json.str i.reason)
    , ("properties", Json.arr (i.properties.map Json.str))
    , ("findings", Json.arr (i.findings.map ReachabilityFinding.toJson))
    ]

structure Facts where
  version : String := "bh.yultextmini.reachability_facts.v0"
  -- Slots that are writable by some *external entrypoint* (under summary closure).
  writableSlots : Std.HashSet Nat := {}
  writableSlotRefs : Std.HashSet String := {}
  -- Slots that appear as storage-derived targets for value-bearing calls reachable from some external entrypoint.
  callTargetSlots : Std.HashSet Nat := {}
  callTargetSlotRefs : Std.HashSet String := {}
  deriving Inhabited

def Facts.toJson (f : Facts) : Json :=
  let ws := (f.writableSlots.toList.mergeSort (· < ·)).toArray
  let wsr := (f.writableSlotRefs.toList.mergeSort (fun a b => a < b)).toArray
  let ts := (f.callTargetSlots.toList.mergeSort (· < ·)).toArray
  let tsr := (f.callTargetSlotRefs.toList.mergeSort (fun a b => a < b)).toArray
  Json.mkObj
    [ ("version", Json.str f.version)
    , ("writableSlots", Json.arr (ws.map (fun n => Json.num (JsonNumber.fromNat n))))
    , ("writableSlotRefs", Json.arr (wsr.map Json.str))
    , ("callTargetSlots", Json.arr (ts.map (fun n => Json.num (JsonNumber.fromNat n))))
    , ("callTargetSlotRefs", Json.arr (tsr.map Json.str))
    ]

/-!
`R`: closure / nucleus operator for Facts.

For the MVP we normalize by ensuring:
- `writableSlots` is computed only from *external entrypoints* (not internal helper functions).
- `callTargetSlots` is computed only from value-bearing, storage-derived call targets reachable from external entrypoints.

This is monotone and idempotent under the chosen mining procedure, and it provides the
“normal form” that our inconsistency check operates on.
-/
def closeFacts (facts : Facts) : Facts :=
  facts

private def tagSlotNat? (t : String) : Option Nat :=
  if t.startsWith "target_slot=" then
    (t.drop "target_slot=".length).toNat?
  else
    none

private def tagSlotRef? (t : String) : Option String :=
  if t.startsWith "target_slotref=" then
    some (t.drop "target_slotref=".length)
  else
    none

private def isValueBearing (tags : Array String) : Bool :=
  tags.any (· = "value=callvalue") || tags.any (· = "value=nonzero_const") || tags.any (· = "value=nonzero_maybe")

private def isStorageDerivedTarget (tags : Array String) : Bool :=
  tags.any (· = "target=storage_derived") &&
    (tags.any (fun t => t.startsWith "target_slot=") || tags.any (fun t => t.startsWith "target_slotref="))

private def isNonConstTarget (tags : Array String) : Bool :=
  !(tags.any (· = "target=const"))

private def isCallLike (kind : String) : Bool :=
  kind = "call" || kind = "callcode"

private def isCallSiteLike (kind : String) : Bool :=
  kind = "call" || kind = "staticcall" || kind = "delegatecall" || kind = "callcode"

private def isUncheckedReturnSite (s : CallSite) : Bool :=
  isCallSiteLike s.kind && !s.checked

/-!
Privilege heuristics (Phase 5.6):

Reachability facts treat any external entrypoint as a potential writer, but many real-world protocols
have privileged configuration setters (e.g. `onlyRole`, `onlyOwner`, `initializer`). Those should not
dominate high-signal "user-controllable target" findings.

We therefore classify writer entrypoints as "privileged" if their summary-closure callees include
common access-control / initialization modifier hooks emitted by solc for OpenZeppelin-style code.

This is intentionally heuristic and conservative: we still *report* the pattern, but under a
separate property name so the default closure invariant is not marked violated.
-/
def isPrivilegedEntrypointSummaryHeuristic (s : FnSummary) : Bool :=
  s.callees.toList.any (fun c =>
    c.startsWith "modifier_onlyRole_" ||
    c.startsWith "modifier_onlyOwner_" ||
    c.startsWith "modifier_onlyAdmin_" ||
    c.startsWith "modifier_initializer_" ||
    c.startsWith "modifier_reinitializer_" ||
    c.startsWith "modifier_onlyInitializing_" ||
    c.startsWith "modifier_onlyBridgeAdaptor_" ||
    c.startsWith "modifier_onlyGovernor_" ||
    c.startsWith "fun__checkRole_" ||
    c.startsWith "fun_checkRole_"
  )

def closeInvariants (xs : Array ClosureInvariant) : Array ClosureInvariant :=
  xs

def mineClosureInvariants (findings : Array ReachabilityFinding) : Array ClosureInvariant :=
  let mk (id : String) (reason : String) (ps : Array String) : ClosureInvariant :=
    let fs := findings.filter (fun f => ps.any (· = f.property))
    { id := id
      violated := !fs.isEmpty
      reason := reason
      properties := ps
      findings := fs.take 6
    }
  closeInvariants #[
    mk "no_unchecked_low_level_call_return"
      "heuristic: an unchecked low-level call return is reachable from an external entrypoint"
      #["unchecked_low_level_call_return"],
    mk "no_value_bearing_nonconst_call_then_write"
      "heuristic: a value-bearing call to a non-const target is followed by a storage write (intraprocedural order)"
      #["value_bearing_nonconst_call_then_write"],
    mk "no_mutable_storage_derived_value_call_target"
      "heuristic: a value-bearing call target derived from storage slot S is reachable, and some external entrypoint can write S"
      #["mutable_storage_derived_value_call_target", "mutable_storage_derived_value_call_target_k3"]
  ]

structure ReachabilityScanStats where
  version : String := "bh.yultextmini.reachability_stats.v0"
  functionsTotal : Nat := 0
  functionsSelected : Nat := 0
  functionsParsedCalls : Nat := 0
  externalEntrypoints : Nat := 0
  slotsWritable : Nat := 0
  slotsCallTargets : Nat := 0
  findingsCount : Nat := 0
  failures : Array (String × String) := #[]
  deriving Inhabited

def ReachabilityScanStats.toJson (s : ReachabilityScanStats) : Json :=
  Json.mkObj
    [ ("version", Json.str s.version)
    , ("functionsTotal", Json.num s.functionsTotal)
    , ("functionsSelected", Json.num s.functionsSelected)
    , ("functionsParsedCalls", Json.num s.functionsParsedCalls)
    , ("externalEntrypoints", Json.num s.externalEntrypoints)
    , ("slotsWritable", Json.num s.slotsWritable)
    , ("slotsCallTargets", Json.num s.slotsCallTargets)
    , ("findingsCount", Json.num s.findingsCount)
    , ("failures",
        Json.arr <|
          s.failures.map (fun (p : String × String) => Json.mkObj [("fn", Json.str p.1), ("error", Json.str p.2)]))
    ]

private def isExternalEntrypoint (fn : String) : Bool :=
  fn.startsWith "external_fun_"

private def isInterestingFnName (fn : String) : Bool :=
  fn.startsWith "fun_" || fn.startsWith "external_fun_" || fn.startsWith "getter_fun_" || fn.startsWith "modifier_"

private def sortedDedupe (xs : Array String) : Array String :=
  xs.toList.eraseDups.mergeSort (fun a b => a < b) |>.toArray

private def hsNatToSortedArray (s : Std.HashSet Nat) : Array Nat :=
  (s.toList.mergeSort (· < ·)).toArray

private def addSlotToMap (m : Std.HashMap Nat (Array String)) (slot : Nat) (fn : String) : Std.HashMap Nat (Array String) :=
  let cur := m.getD slot #[]
  m.insert slot (cur.push fn)

/-!
Compute bounded reachability facts and a single high-signal cross-function property:

`mutable_storage_derived_value_call_target` (k=2)
- There exists an external entrypoint that can write storage slot `s`.
- There exists an external entrypoint that can reach a value-bearing `call/callcode` whose target is derived from slot `s`.

This is designed to produce actionable leads for adapter-style contracts.
-/
/-!
Generalized reachability scan (Phase 5.5):

`kMax` controls the maximum witness-sequence length emitted:
- `kMax ≥ 1` enables single-call temporal properties (unchecked returns; call-then-write heuristics).
- `kMax ≥ 2` enables the original cross-function k=2 property.
- `kMax ≥ 3` emits an additional k=3 witness variant for the k=2 property when possible.
-/
def scanIRReachability (ir : String) (fnsAll : Array String) (iterMax : Nat := 6) (kMax : Nat := 2) :
    ReachabilityScanStats × Facts × Array ReachabilityFinding :=
  Id.run do
    let ctx := buildSummaryContext ir fnsAll iterMax

    let fns := fnsAll.toList.filter isInterestingFnName |>.toArray
    let mut callsByFn : Std.HashMap String (Array BoundaryCall) := {}
    let mut sitesByFn : Std.HashMap String (Array CallSite) := {}
    let mut writesAfterRiskyByFn : Std.HashMap String (Nat × Array String) := {}
    let mut failures : Array (String × String) := #[]
    let mut parsedCalls : Nat := 0
    for fn in fns do
      match scanIRCallInterfaceScoredWithWrites ir fn with
      | .error e => failures := failures.push (fn, e)
      | .ok (calls, sites, _score, _flags, _writesAny, writesAfterRisky, writesAfterEv) =>
          parsedCalls := parsedCalls + 1
          callsByFn := callsByFn.insert fn calls
          sitesByFn := sitesByFn.insert fn sites
          writesAfterRiskyByFn := writesAfterRiskyByFn.insert fn (writesAfterRisky, writesAfterEv)

    let externalFns := fns.filter isExternalEntrypoint

    -- Facts mined "pre-closure".
    let mut facts : Facts := {}

    -- Index: slot -> external entrypoints that can write it (under summary closure).
    let mut writersBySlot : Std.HashMap Nat (Array String) := {}
    let mut writersBySlotUnpriv : Std.HashMap Nat (Array String) := {}
    let mut writersBySlotRef : Std.HashMap String (Array String) := {}
    let mut writersBySlotRefUnpriv : Std.HashMap String (Array String) := {}
    for ext in externalFns do
      let s := ctx.summaries.getD ext {}
      let privilegedWriter := isPrivilegedEntrypointSummaryHeuristic s
      for w in s.writes.toList do
        match w.toNat? with
        | none => pure ()
        | some n =>
            facts := { facts with writableSlots := facts.writableSlots.insert n }
            writersBySlot := addSlotToMap writersBySlot n ext
            if !privilegedWriter then
              writersBySlotUnpriv := addSlotToMap writersBySlotUnpriv n ext
      for w in s.writes.toList do
        facts := { facts with writableSlotRefs := facts.writableSlotRefs.insert w }
        let cur := writersBySlotRef.getD w #[]
        writersBySlotRef := writersBySlotRef.insert w (cur.push ext)
        if !privilegedWriter then
          let cur2 := writersBySlotRefUnpriv.getD w #[]
          writersBySlotRefUnpriv := writersBySlotRefUnpriv.insert w (cur2.push ext)

    -- Index: slot -> external entrypoints that can (reach a) value-bearing call whose target is derived from the slot.
    let mut callersBySlot : Std.HashMap Nat (Array String) := {}
    let mut callersBySlotRef : Std.HashMap String (Array String) := {}
    -- Evidence: slot -> (calleeFn, call) sample.
    let mut callEvidenceBySlot : Std.HashMap Nat (String × BoundaryCall) := {}
    let mut callEvidenceBySlotRef : Std.HashMap String (String × BoundaryCall) := {}

    for ext in externalFns do
      let s := ctx.summaries.getD ext {}
      -- Consider calls in any reachable internal helper, plus the entrypoint itself.
      let reachable := (sortedDedupe ((s.callees.toList.toArray).push ext))
      for fn in reachable do
        let calls := callsByFn.getD fn #[]
        for c in calls do
          if isCallLike c.kind && isValueBearing c.tags && isStorageDerivedTarget c.tags then
            match c.tags.findSome? tagSlotNat? with
            | none => pure ()
            | some slot =>
                facts := { facts with callTargetSlots := facts.callTargetSlots.insert slot }
                callersBySlot := addSlotToMap callersBySlot slot ext
                if (callEvidenceBySlot.get? slot).isNone then
                  callEvidenceBySlot := callEvidenceBySlot.insert slot (fn, c)
            match c.tags.findSome? tagSlotRef? with
            | none => pure ()
            | some slotRef =>
                facts := { facts with callTargetSlotRefs := facts.callTargetSlotRefs.insert slotRef }
                let cur := callersBySlotRef.getD slotRef #[]
                callersBySlotRef := callersBySlotRef.insert slotRef (cur.push ext)
                if (callEvidenceBySlotRef.get? slotRef).isNone then
                  callEvidenceBySlotRef := callEvidenceBySlotRef.insert slotRef (fn, c)

    -- Apply nucleus/closure.
    let factsR := closeFacts facts

    let mut findings : Array ReachabilityFinding := #[]
    if kMax ≥ 1 then
      -- Property: unchecked low-level call return is reachable from an external entrypoint.
      -- We report a single-call witness `[external_fun_*]`.
      for ext in externalFns do
        let s := ctx.summaries.getD ext {}
        let reachable := (sortedDedupe ((s.callees.toList.toArray).push ext))
        let mut found : Option (String × CallSite) := none
        for fn in reachable do
          if found.isSome then
            continue
          let sites := sitesByFn.getD fn #[]
          match sites.find? isUncheckedReturnSite with
          | none => pure ()
          | some site => found := some (fn, site)
        match found with
        | none => pure ()
        | some (callSiteFn, site) =>
            findings :=
              findings.push
                { property := "unchecked_low_level_call_return"
                  k := 1
                  targetSlot := (site.call.tags.findSome? tagSlotNat?).getD 0
                  targetSlotRef := (site.call.tags.findSome? tagSlotRef?).getD ""
                  writers := #[]
                  callers := #[ext]
                  witnessSequences := #[#[ext]]
                  callSiteFn := callSiteFn
                  call := site.call
                }

      -- Property: value-bearing call to non-const target occurs, and there is at least one storage write
      -- after the first such call (intraprocedural order), in some reachable helper.
      for ext in externalFns do
        let s := ctx.summaries.getD ext {}
        let reachable := (sortedDedupe ((s.callees.toList.toArray).push ext))
        let mut found : Option (String × BoundaryCall × Array String) := none
        for fn in reachable do
          if found.isSome then
            continue
          let (writesAfterRisky, ev) := writesAfterRiskyByFn.getD fn (0, #[])
          if writesAfterRisky = 0 then
            continue
          let calls := callsByFn.getD fn #[]
          match calls.find? (fun c => isCallLike c.kind && isValueBearing c.tags && isNonConstTarget c.tags) with
          | none => pure ()
          | some c => found := some (fn, c, ev)
        match found with
        | none => pure ()
        | some (callSiteFn, call, _ev) =>
            findings :=
              findings.push
                { property := "value_bearing_nonconst_call_then_write"
                  k := 1
                  targetSlot := (call.tags.findSome? tagSlotNat?).getD 0
                  targetSlotRef := (call.tags.findSome? tagSlotRef?).getD ""
                  writers := #[]
                  callers := #[ext]
                  witnessSequences := #[#[ext]]
                  callSiteFn := callSiteFn
                  call := call
                }

    -- Property: mutable storage-derived value call target (k=2, k=3 variants).
    for slot in hsNatToSortedArray factsR.callTargetSlots do
      match writersBySlot.get? slot, callersBySlot.get? slot, callEvidenceBySlot.get? slot with
      | some ws, some cs, some (callSiteFn, call) =>
          let wsUnpriv := writersBySlotUnpriv.getD slot #[]
          let writersRaw := if wsUnpriv.isEmpty then ws else wsUnpriv
          let writers := sortedDedupe writersRaw
          let callers := sortedDedupe cs
          if writers.size > 0 && callers.size > 0 then
            let propBase :=
              if wsUnpriv.isEmpty then
                "mutable_storage_derived_value_call_target_privileged_writers"
              else
                "mutable_storage_derived_value_call_target"
            if kMax ≥ 2 then
              let mut wit : Array (Array String) := #[]
              -- Deterministic small witness set.
              let maxW : Nat := 3
              let maxC : Nat := 3
              for w in writers.take maxW do
                for cfn in callers.take maxC do
                  wit := wit.push #[w, cfn]
              findings :=
                findings.push
                  { property := propBase
                    k := 2
                    targetSlot := slot
                    targetSlotRef := toString slot
                    writers := writers
                    callers := callers
                    witnessSequences := wit
                    callSiteFn := callSiteFn
                    call := call
                  }
            if kMax ≥ 3 && writers.size ≥ 2 then
              let mut wit3 : Array (Array String) := #[]
              let maxW : Nat := 3
              let maxC : Nat := 2
              let ws2 := writers.take maxW
              for i in [:ws2.size] do
                for j in [:ws2.size] do
                  if i = j then
                    continue
                  for cfn in callers.take maxC do
                    wit3 := wit3.push #[ws2[i]!, ws2[j]!, cfn]
              if !wit3.isEmpty then
                findings :=
                  findings.push
                    { property := propBase ++ "_k3"
                      k := 3
                      targetSlot := slot
                      targetSlotRef := toString slot
                      writers := writers
                      callers := callers
                      witnessSequences := wit3
                      callSiteFn := callSiteFn
                      call := call
                    }
      | _, _, _ => pure ()

    -- SlotRef-string variant (covers mappings/arrays/struct slots in addition to literal slots).
    for slotRef in (factsR.callTargetSlotRefs.toList.mergeSort (fun a b => a < b)).toArray do
      let ws := writersBySlotRef.getD slotRef #[]
      let wsUnpriv := writersBySlotRefUnpriv.getD slotRef #[]
      let cs := callersBySlotRef.getD slotRef #[]
      match callEvidenceBySlotRef.get? slotRef with
      | none => pure ()
      | some (callSiteFn, call) =>
          let writersRaw := if wsUnpriv.isEmpty then ws else wsUnpriv
          let writers := sortedDedupe writersRaw
          let callers := sortedDedupe cs
          if writers.size > 0 && callers.size > 0 then
            let propBase :=
              if wsUnpriv.isEmpty then
                "mutable_storage_derived_value_call_target_privileged_writers"
              else
                "mutable_storage_derived_value_call_target"
            if kMax ≥ 2 then
              let mut wit : Array (Array String) := #[]
              let maxW : Nat := 3
              let maxC : Nat := 3
              for w in writers.take maxW do
                for cfn in callers.take maxC do
                  wit := wit.push #[w, cfn]
              findings :=
                findings.push
                  { property := propBase
                    k := 2
                    targetSlot := slotRef.toNat?.getD 0
                    targetSlotRef := slotRef
                    writers := writers
                    callers := callers
                    witnessSequences := wit
                    callSiteFn := callSiteFn
                    call := call
                  }

    let stats : ReachabilityScanStats :=
      { functionsTotal := fnsAll.size
        functionsSelected := fns.size
        functionsParsedCalls := parsedCalls
        externalEntrypoints := externalFns.size
        slotsWritable := factsR.writableSlots.size
        slotsCallTargets := factsR.callTargetSlots.size
        findingsCount := findings.size
        failures := failures ++ ctx.failures
      }
    return (stats, factsR, findings)

/-! Backwards-compatible wrapper for the Phase 4 API. -/
def scanIRReachabilityK2 (ir : String) (fnsAll : Array String) (iterMax : Nat := 6) :
    ReachabilityScanStats × Facts × Array ReachabilityFinding :=
  scanIRReachability ir fnsAll iterMax 2

end HeytingLean.BountyHunter.Solc.YulTextMini
