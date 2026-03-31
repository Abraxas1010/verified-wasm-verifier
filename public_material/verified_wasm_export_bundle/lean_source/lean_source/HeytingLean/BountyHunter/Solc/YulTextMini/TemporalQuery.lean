import Std
import Lean.Data.Json
import HeytingLean.BountyHunter.Solc.YulTextMini.Types
import HeytingLean.BountyHunter.Solc.YulTextMini.CallInterface
import HeytingLean.BountyHunter.Solc.YulTextMini.Summary

/-!
# HeytingLean.BountyHunter.Solc.YulTextMini.TemporalQuery

Phase 7: a tiny, deterministic **temporal query DSL** over bounded external-call traces.

This is intentionally corpus-first and conservative:
- it only quantifies over sequences of `external_fun_*` entrypoints,
- it uses the existing Summary fixpoint (closure `R`) plus CallInterface extraction,
- it emits a bounded set of witnesses when a query is satisfiable.

DSL (MVP):
- steps are separated by `;`
- within a step, atoms are conjoined with `,` or `&`
- atoms:
  - `unchecked_return`
  - `call_then_write`                        (value-bearing non-const call then storage write)
  - `write_slot=<n|$var>`
  - `call_target_slot=<n|$var>`              (value-bearing, storage-derived target tagged with `target_slot=n`)

Example:
`write_slot=$s; call_target_slot=$s`
-/

namespace HeytingLean.BountyHunter.Solc.YulTextMini

open Std
open Lean

inductive TSlotTerm where
  | lit : Nat → TSlotTerm
  | var : String → TSlotTerm
  deriving Inhabited, Repr

inductive TAtom where
  | uncheckedReturn : TAtom
  | callThenWrite : TAtom
  | callThenWriteSameSlot : TAtom
  | delegatecallNonconstTarget : TAtom
  | calldataPassthroughUnguarded : TAtom
  | approveUserSpender : TAtom
  | writeSlot : TSlotTerm → TAtom
  | callTargetSlot : TSlotTerm → TAtom
  | writeSlotRef : TSlotTerm → TAtom
  | callTargetSlotRef : TSlotTerm → TAtom
  deriving Inhabited, Repr

abbrev TStep := Array TAtom

structure TQuery where
  steps : Array TStep
  deriving Inhabited, Repr

private def trim (s : String) : String :=
  s.trim

private def splitOnAny (seps : List Char) (s : String) : Array String :=
  Id.run do
    let mut out : Array String := #[]
    let mut cur : Array Char := #[]
    for c in s.data do
      if seps.contains c then
        out := out.push (String.mk cur.toList)
        cur := #[]
      else
        cur := cur.push c
    out := out.push (String.mk cur.toList)
    return out

private def parseSlotTerm? (s0 : String) : Except String TSlotTerm := do
  let s := trim s0
  if s.startsWith "$" then
    let v := s.drop 1
    if v.isEmpty then
      throw "empty slot variable: use $s"
    else
      return .var v
  else
    match s.toNat? with
    | some n => return .lit n
    | none => throw s!"expected Nat or $var for slot term, got: {s0}"

private def parseAtom? (s0 : String) : Except String TAtom := do
  let s := trim s0
  if s = "unchecked_return" then
    return .uncheckedReturn
  if s = "call_then_write" then
    return .callThenWrite
  if s = "call_then_write_same_slot" then
    return .callThenWriteSameSlot
  if s = "delegatecall_nonconst_target" then
    return .delegatecallNonconstTarget
  if s = "calldata_passthrough_unguarded" then
    return .calldataPassthroughUnguarded
  if s = "approve_user_spender" then
    return .approveUserSpender
  if s.startsWith "write_slot=" then
    let t ← parseSlotTerm? (s.drop "write_slot=".length)
    return .writeSlot t
  if s.startsWith "call_target_slot=" then
    let t ← parseSlotTerm? (s.drop "call_target_slot=".length)
    return .callTargetSlot t
  if s.startsWith "write_slotref=" then
    let t ← parseSlotTerm? (s.drop "write_slotref=".length)
    return .writeSlotRef t
  if s.startsWith "call_target_slotref=" then
    let t ← parseSlotTerm? (s.drop "call_target_slotref=".length)
    return .callTargetSlotRef t
  throw s!"unknown atom: {s0}"

def parseTemporalQuery? (q0 : String) : Except String TQuery := do
  let rawSteps := (q0.splitOn ";").toArray.map trim |>.filter (fun s => !s.isEmpty)
  if rawSteps.isEmpty then
    throw "empty query"
  let mut steps : Array TStep := #[]
  for st in rawSteps do
    let parts := splitOnAny ['&', ','] st |>.map trim |>.filter (fun s => !s.isEmpty)
    if parts.isEmpty then
      throw s!"empty step in query near: {st}"
    let mut atoms : Array TAtom := #[]
    for p in parts do
      atoms := atoms.push (← parseAtom? p)
    steps := steps.push atoms
  return { steps := steps }

abbrev parseQuery? := parseTemporalQuery?

structure ExtFacts where
  writesSlots : Std.HashSet Nat := {}
  writesSlotRefs : Std.HashSet String := {}
  callTargetSlots : Std.HashSet Nat := {}
  callTargetSlotRefs : Std.HashSet String := {}
  hasUncheckedReturn : Bool := false
  hasCallThenWrite : Bool := false
  hasCallThenWriteSameSlot : Bool := false
  hasDelegatecallNonconstTarget : Bool := false
  hasCalldataPassthroughUnguarded : Bool := false
  hasApproveUserSpender : Bool := false
  deriving Inhabited

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

private def isCallLike (kind : String) : Bool :=
  kind = "call" || kind = "callcode"

private def addNatIfSome (s : Std.HashSet Nat) (n? : Option Nat) : Std.HashSet Nat :=
  match n? with
  | none => s
  | some n => s.insert n

private def hsNatToSortedArray (s : Std.HashSet Nat) : Array Nat :=
  (s.toList.mergeSort (· < ·)).toArray

private def hsStringToSortedArray (s : Std.HashSet String) : Array String :=
  (s.toList.mergeSort (fun a b => a < b)).toArray

private def isExternalEntrypoint (fn : String) : Bool :=
  fn.startsWith "external_fun_"

private def isInterestingFnName (fn : String) : Bool :=
  fn.startsWith "fun_" || fn.startsWith "external_fun_" || fn.startsWith "getter_fun_" || fn.startsWith "modifier_"

private def sortedDedupe (xs : Array String) : Array String :=
  xs.toList.eraseDups.mergeSort (fun a b => a < b) |>.toArray

inductive SlotVal where
  | nat : Nat → SlotVal
  | ref : String → SlotVal
  deriving Inhabited, Repr

private def envGetNat? (env : Std.HashMap String SlotVal) (k : String) : Option Nat :=
  match env.get? k with
  | none => none
  | some (.nat n) => some n
  | some (.ref s) => s.toNat?

private def envGetRef? (env : Std.HashMap String SlotVal) (k : String) : Option String :=
  match env.get? k with
  | none => none
  | some (.ref s) => some s
  | some (.nat n) => some (toString n)

private def envSetNat (env : Std.HashMap String SlotVal) (k : String) (v : Nat) : Std.HashMap String SlotVal :=
  env.insert k (.nat v)

private def envSetRef (env : Std.HashMap String SlotVal) (k : String) (v : String) : Std.HashMap String SlotVal :=
  env.insert k (.ref v)

private def stepMatches (facts : ExtFacts) (env0 : Std.HashMap String SlotVal) (atoms : TStep) :
    Array (Std.HashMap String SlotVal) :=
  Id.run do
    let mut envs : Array (Std.HashMap String SlotVal) := #[env0]
    for a in atoms do
      let mut next : Array (Std.HashMap String SlotVal) := #[]
      for env in envs do
        match a with
        | .uncheckedReturn =>
            if facts.hasUncheckedReturn then next := next.push env
        | .callThenWrite =>
            if facts.hasCallThenWrite then next := next.push env
        | .callThenWriteSameSlot =>
            if facts.hasCallThenWriteSameSlot then next := next.push env
        | .delegatecallNonconstTarget =>
            if facts.hasDelegatecallNonconstTarget then next := next.push env
        | .calldataPassthroughUnguarded =>
            if facts.hasCalldataPassthroughUnguarded then next := next.push env
        | .approveUserSpender =>
            if facts.hasApproveUserSpender then next := next.push env
        | .writeSlot t =>
            match t with
            | .lit n =>
                if facts.writesSlots.contains n then
                  next := next.push env
            | .var v =>
                match envGetNat? env v with
                | some n =>
                    if facts.writesSlots.contains n then
                      next := next.push env
                | none =>
                    for n in hsNatToSortedArray facts.writesSlots do
                      next := next.push (envSetNat env v n)
        | .callTargetSlot t =>
            match t with
            | .lit n =>
                if facts.callTargetSlots.contains n then
                  next := next.push env
            | .var v =>
                match envGetNat? env v with
                | some n =>
                    if facts.callTargetSlots.contains n then
                      next := next.push env
                | none =>
                    for n in hsNatToSortedArray facts.callTargetSlots do
                      next := next.push (envSetNat env v n)
        | .writeSlotRef t =>
            let containsRef (r : String) : Bool := facts.writesSlotRefs.contains r
            match t with
            | .lit n =>
                if containsRef (toString n) then
                  next := next.push env
            | .var v =>
                match envGetRef? env v with
                | some r =>
                    if containsRef r then
                      next := next.push env
                | none =>
                    for r in hsStringToSortedArray facts.writesSlotRefs do
                      next := next.push (envSetRef env v r)
        | .callTargetSlotRef t =>
            let containsRef (r : String) : Bool := facts.callTargetSlotRefs.contains r
            match t with
            | .lit n =>
                if containsRef (toString n) then
                  next := next.push env
            | .var v =>
                match envGetRef? env v with
                | some r =>
                    if containsRef r then
                      next := next.push env
                | none =>
                    for r in hsStringToSortedArray facts.callTargetSlotRefs do
                      next := next.push (envSetRef env v r)
      envs := next
      if envs.isEmpty then
        return #[]
    return envs

structure TemporalMatch where
  env : Std.HashMap String SlotVal
  witness : Array String
  deriving Inhabited

def TemporalMatch.toJson (m : TemporalMatch) : Json :=
  let envItems :=
    (m.env.toList.mergeSort (fun a b => a.1 < b.1)).map (fun (k, v) =>
      match v with
      | .nat n => Json.mkObj [("var", Json.str k), ("value", Json.num (JsonNumber.fromNat n))]
      | .ref s => Json.mkObj [("var", Json.str k), ("value", Json.str s)])
  Json.mkObj
    [ ("env", Json.arr envItems.toArray)
    , ("witness", Json.arr (m.witness.map Json.str))
    ]

structure TemporalScanStats where
  version : String := "bh.yultextmini.temporal_query_stats.v0"
  functionsTotal : Nat := 0
  functionsSelected : Nat := 0
  externalEntrypoints : Nat := 0
  parsedCalls : Nat := 0
  matchesCount : Nat := 0
  failures : Array (String × String) := #[]
  deriving Inhabited

def TemporalScanStats.toJson (s : TemporalScanStats) : Json :=
  Json.mkObj
    [ ("version", Json.str s.version)
    , ("functionsTotal", Json.num s.functionsTotal)
    , ("functionsSelected", Json.num s.functionsSelected)
    , ("externalEntrypoints", Json.num s.externalEntrypoints)
    , ("parsedCalls", Json.num s.parsedCalls)
    , ("matchesCount", Json.num s.matchesCount)
    , ("failures",
        Json.arr <|
          s.failures.map (fun (p : String × String) => Json.mkObj [("fn", Json.str p.1), ("error", Json.str p.2)]))
    ]

private def factsOfExternal
    (ctx : SummaryContext)
    (callsByFn : Std.HashMap String (Array BoundaryCall))
    (sitesByFn : Std.HashMap String (Array CallSite))
    (writesAfterRiskyByFn : Std.HashMap String Nat)
    (flagsByFn : Std.HashMap String (Std.HashSet String))
    (callThenWriteSameSlotByFn : Std.HashMap String Bool)
    (calldataGuardByFn : Std.HashMap String Bool)
    (ext : String) : ExtFacts :=
  Id.run do
    let s := ctx.summaries.getD ext {}
    let reachable := sortedDedupe ((hsStringToSortedArray s.callees).push ext)
    let mut callTargetSlots : Std.HashSet Nat := {}
    let mut callTargetSlotRefs : Std.HashSet String := {}
    let mut hasUnchecked : Bool := false
    let mut hasCallThenWrite : Bool := false
    let mut hasCallThenWriteSameSlot : Bool := false
    let mut hasDelegatecallNonconstTarget : Bool := false
    let mut hasCalldataPassthroughUnguarded : Bool := false
    let mut hasApproveUserSpender : Bool := false
    for fn in reachable do
      let calls := callsByFn.getD fn #[]
      for c in calls do
        if isCallLike c.kind && isValueBearing c.tags && isStorageDerivedTarget c.tags then
          callTargetSlots := addNatIfSome callTargetSlots (c.tags.findSome? tagSlotNat?)
          match c.tags.findSome? tagSlotRef? with
          | none => pure ()
          | some r => callTargetSlotRefs := callTargetSlotRefs.insert r
        if (c.kind = "delegatecall" || c.kind = "callcode") && !(c.tags.any (· = "target=const")) then
          hasDelegatecallNonconstTarget := true
      let sites := sitesByFn.getD fn #[]
      if sites.any (fun site => (site.kind = "call" || site.kind = "staticcall" || site.kind = "delegatecall" || site.kind = "callcode") && !site.checked) then
        hasUnchecked := true
      if (writesAfterRiskyByFn.getD fn 0) > 0 then
        hasCallThenWrite := true
      if callThenWriteSameSlotByFn.getD fn false then
        hasCallThenWriteSameSlot := true
      let flags := flagsByFn.getD fn {}
      if flags.contains "calldata_passthrough_no_len_guard" then
        hasCalldataPassthroughUnguarded := true
      if flags.contains "approve_like_with_calldata_derived_address_no_allowlist_evidence" then
        hasApproveUserSpender := true
    -- If the external entrypoint itself has a length guard, treat passthrough as guarded.
    if calldataGuardByFn.getD ext false then
      hasCalldataPassthroughUnguarded := false
    let mut writesSlots : Std.HashSet Nat := {}
    for w in s.writes.toList do
      match w.toNat? with
      | some n => writesSlots := writesSlots.insert n
      | none => pure ()
    let mut writesSlotRefs : Std.HashSet String := {}
    for w in s.writes.toList do
      writesSlotRefs := writesSlotRefs.insert w
    return { writesSlots := writesSlots
             writesSlotRefs := writesSlotRefs
             callTargetSlots := callTargetSlots
             callTargetSlotRefs := callTargetSlotRefs
             hasUncheckedReturn := hasUnchecked
             hasCallThenWrite := hasCallThenWrite
             hasCallThenWriteSameSlot := hasCallThenWriteSameSlot
             hasDelegatecallNonconstTarget := hasDelegatecallNonconstTarget
             hasCalldataPassthroughUnguarded := hasCalldataPassthroughUnguarded
             hasApproveUserSpender := hasApproveUserSpender }

def scanIRTemporalQuery
    (ir : String)
    (fnsAll : Array String)
    (q : TQuery)
    (iterMax : Nat := 6)
    (maxMatches : Nat := 24) :
    TemporalScanStats × Array TemporalMatch :=
  Id.run do
    let ctx := buildSummaryContext ir fnsAll iterMax

    let fns := fnsAll.toList.filter isInterestingFnName |>.toArray
    let mut callsByFn : Std.HashMap String (Array BoundaryCall) := {}
    let mut sitesByFn : Std.HashMap String (Array CallSite) := {}
    let mut writesAfterRiskyByFn : Std.HashMap String Nat := {}
    let mut flagsByFn : Std.HashMap String (Std.HashSet String) := {}
    let mut callThenWriteSameSlotByFn : Std.HashMap String Bool := {}
    let mut calldataGuardByFn : Std.HashMap String Bool := {}
    let mut failures : Array (String × String) := #[]
    let mut parsed : Nat := 0
    for fn in fns do
      match scanIRCallInterfaceScoredWithWrites ir fn with
      | .error e => failures := failures.push (fn, e)
      | .ok (calls, sites, _score, _flags, _writesAny, writesAfterRisky, _ev) =>
          parsed := parsed + 1
          callsByFn := callsByFn.insert fn calls
          sitesByFn := sitesByFn.insert fn sites
          writesAfterRiskyByFn := writesAfterRiskyByFn.insert fn writesAfterRisky
          flagsByFn := flagsByFn.insert fn (_flags.foldl (fun acc fl => acc.insert fl.name) {})
          match HeytingLean.BountyHunter.Solc.YulTextMini.scanIRCallThenWriteSameSlotRef ir fn with
          | .error _ => callThenWriteSameSlotByFn := callThenWriteSameSlotByFn.insert fn false
          | .ok b => callThenWriteSameSlotByFn := callThenWriteSameSlotByFn.insert fn b
          match HeytingLean.BountyHunter.Solc.YulTextMini.scanIRHasCalldataLenGuard ir fn with
          | .error _ => calldataGuardByFn := calldataGuardByFn.insert fn false
          | .ok b => calldataGuardByFn := calldataGuardByFn.insert fn b

    let externalFns := (fns.filter isExternalEntrypoint).qsort (fun a b => a < b)

    let rec go (steps : List TStep) (env : Std.HashMap String SlotVal) (w : Array String) (acc0 : Array TemporalMatch) :
        Array TemporalMatch :=
      Id.run do
        if acc0.size ≥ maxMatches then
          return acc0
        match steps with
        | [] =>
            return acc0.push { env := env, witness := w }
        | step :: rest =>
            let mut acc := acc0
            for ext in externalFns do
              if acc.size ≥ maxMatches then
                break
              let facts :=
                factsOfExternal ctx callsByFn sitesByFn writesAfterRiskyByFn flagsByFn callThenWriteSameSlotByFn calldataGuardByFn ext
              let envs := stepMatches facts env step
              for env2 in envs do
                if acc.size ≥ maxMatches then
                  break
                acc := go rest env2 (w.push ext) acc
            return acc

    let ms := go q.steps.toList {} #[] #[]

    let stats : TemporalScanStats :=
      { functionsTotal := fnsAll.size
        functionsSelected := fns.size
        externalEntrypoints := externalFns.size
        parsedCalls := parsed
        matchesCount := ms.size
        failures := failures ++ ctx.failures
      }
    return (stats, ms)

end HeytingLean.BountyHunter.Solc.YulTextMini
