/-
Copyright (c) 2026 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

import HeytingLean.HeytingVeil.Intake.DispatchIntent

/-!
# Intake Dispatch Batch

Batch wrapper for multiple dispatch intents with deterministic ordering and
aggregate readiness counters for orchestration dashboards.
-/

namespace HeytingLean
namespace HeytingVeil
namespace Intake
namespace DispatchBatch

open HeytingLean.HeytingVeil.Intake.DecisionExport
open HeytingLean.HeytingVeil.Intake.DispatchIntent

structure DispatchBatch where
  intents : List DispatchIntent.DispatchIntent
  deriving Repr

/-- Build a batch from decision-export jobs, preserving input order. -/
def fromJobs (jobs : List DecisionExportJob) : DispatchBatch :=
  { intents := jobs.map DispatchIntent.build }

def totalCount (batch : DispatchBatch) : Nat :=
  batch.intents.length

def readyCount (batch : DispatchBatch) : Nat :=
  (batch.intents.filter (fun i => i.dispatchReady)).length

def blockedCount (batch : DispatchBatch) : Nat :=
  totalCount batch - readyCount batch

theorem counts_partition (batch : DispatchBatch) :
    readyCount batch + blockedCount batch = totalCount batch := by
  unfold blockedCount totalCount readyCount
  exact Nat.add_sub_of_le (List.length_filter_le _ _)

def consistencyOk (batch : DispatchBatch) : Bool :=
  decide (readyCount batch + blockedCount batch = totalCount batch)

theorem consistencyOk_true (batch : DispatchBatch) : consistencyOk batch = true := by
  unfold consistencyOk
  exact decide_eq_true (counts_partition batch)

def integrityDigest (batch : DispatchBatch) : String :=
  let intentDigests := batch.intents.map (fun i => i.adapterTuple.integrityDigest)
  String.intercalate "|"
    [
      "dispatch-batch-v1",
      toString (totalCount batch),
      toString (readyCount batch),
      toString (blockedCount batch),
      String.intercalate ";" intentDigests
    ]

/-- Ready-only projection for triage views. -/
def readyOnly (batch : DispatchBatch) : DispatchBatch :=
  { intents := batch.intents.filter (fun i => i.dispatchReady) }

/-- Blocked-only projection for triage views. -/
def blockedOnly (batch : DispatchBatch) : DispatchBatch :=
  { intents := batch.intents.filter (fun i => !i.dispatchReady) }

theorem readyOnly_count_eq_readyCount (batch : DispatchBatch) :
    totalCount (readyOnly batch) = readyCount batch := by
  simp [readyOnly, totalCount, readyCount]

/-- Lookup by stable batch index (0-based). -/
def findByIdx (batch : DispatchBatch) (idx : Nat) : Option DispatchIntent.DispatchIntent :=
  batch.intents[idx]?

/-- Lookup first intent matching the dispatch spec id hint. -/
def findBySpecId (batch : DispatchBatch) (specId : String) : Option DispatchIntent.DispatchIntent :=
  batch.intents.find? (fun i => i.adapterTuple.specIdHint = specId)

/-- Lookup first intent matching its adapter integrity digest. -/
def findByIntegrityDigest (batch : DispatchBatch) (digest : String) : Option DispatchIntent.DispatchIntent :=
  batch.intents.find? (fun i => i.adapterTuple.integrityDigest = digest)

/-- Human-readable dashboard summary for a dispatch batch. -/
def renderSummary (batch : DispatchBatch) : String :=
  String.intercalate "\n"
    [
      "dispatch_batch_total=" ++ toString (totalCount batch),
      "dispatch_batch_ready=" ++ toString (readyCount batch),
      "dispatch_batch_blocked=" ++ toString (blockedCount batch),
      "dispatch_batch_consistency_ok=" ++ toString (consistencyOk batch),
      "dispatch_batch_integrity_digest=" ++ integrityDigest batch,
      "dispatch_batch_indexed=true"
    ]

/-- Render triage projection counters (ready-only and blocked-only views). -/
def renderTriageSummary (batch : DispatchBatch) : String :=
  let readyView := readyOnly batch
  let blockedView := blockedOnly batch
  String.intercalate "\n"
    [
      renderSummary batch,
      "dispatch_ready_view_total=" ++ toString (totalCount readyView),
      "dispatch_blocked_view_total=" ++ toString (totalCount blockedView)
    ]

private def escapeJson (s : String) : String :=
  (((s.replace "\\" "\\\\").replace "\"" "\\\"").replace "\n" "\\n")

private def renderIntentJsonList (xs : List DispatchIntent.DispatchIntent) : String :=
  "[" ++ String.intercalate ", " (xs.map (fun i => DispatchIntent.renderJson i)) ++ "]"

private def renderIndexedIntentsAux (idx : Nat) (xs : List DispatchIntent.DispatchIntent) : List String :=
  match xs with
  | [] => []
  | x :: rest =>
      ("{\"idx\":" ++ toString idx ++ ",\"intent\":" ++ DispatchIntent.renderJson x ++ "}") ::
        renderIndexedIntentsAux (idx + 1) rest

private def renderIndexedIntentJsonList (xs : List DispatchIntent.DispatchIntent) : String :=
  "[" ++ String.intercalate ", " (renderIndexedIntentsAux 0 xs) ++ "]"

private def renderIntentOptionJson (x? : Option DispatchIntent.DispatchIntent) : String :=
  match x? with
  | some x => DispatchIntent.renderJson x
  | none => "null"

def renderLookupByIdxJson (batch : DispatchBatch) (idx : Nat) : String :=
  renderIntentOptionJson (findByIdx batch idx)

def renderLookupBySpecIdJson (batch : DispatchBatch) (specId : String) : String :=
  renderIntentOptionJson (findBySpecId batch specId)

def renderLookupByDigestJson (batch : DispatchBatch) (digest : String) : String :=
  renderIntentOptionJson (findByIntegrityDigest batch digest)

structure QueryTelemetry where
  idxQueries : Nat
  idxHits : Nat
  specQueries : Nat
  specHits : Nat
  digestQueries : Nat
  digestHits : Nat
  totalQueries : Nat
  totalHits : Nat
  totalMisses : Nat
  deriving Repr

structure QueryTraceRow where
  kind : String
  key : String
  hit : Bool
  deriving Repr

structure QueryTrace where
  rows : List QueryTraceRow
  deriving Repr

private def countSome {α : Type} (xs : List (Option α)) : Nat :=
  (xs.filter Option.isSome).length

def queryTelemetry (batch : DispatchBatch) (idxs : List Nat) (specIds : List String)
    (digests : List String) : QueryTelemetry :=
  let idxResults := idxs.map (fun i => findByIdx batch i)
  let specResults := specIds.map (fun s => findBySpecId batch s)
  let digestResults := digests.map (fun d => findByIntegrityDigest batch d)
  let idxHits := countSome idxResults
  let specHits := countSome specResults
  let digestHits := countSome digestResults
  let totalQueries := idxs.length + specIds.length + digests.length
  let totalHits := idxHits + specHits + digestHits
  {
    idxQueries := idxs.length
    idxHits := idxHits
    specQueries := specIds.length
    specHits := specHits
    digestQueries := digests.length
    digestHits := digestHits
    totalQueries := totalQueries
    totalHits := totalHits
    totalMisses := totalQueries - totalHits
  }

def queryTrace (batch : DispatchBatch) (idxs : List Nat) (specIds : List String)
    (digests : List String) : QueryTrace :=
  let idxRows := idxs.map (fun i =>
    { kind := "idx", key := toString i, hit := (findByIdx batch i).isSome })
  let specRows := specIds.map (fun s =>
    { kind := "spec", key := s, hit := (findBySpecId batch s).isSome })
  let digestRows := digests.map (fun d =>
    { kind := "digest", key := d, hit := (findByIntegrityDigest batch d).isSome })
  { rows := idxRows ++ specRows ++ digestRows }

def renderQueryTelemetrySummary (t : QueryTelemetry) : String :=
  String.intercalate "\n"
    [
      "query_idx_hits=" ++ toString t.idxHits ++ "/" ++ toString t.idxQueries,
      "query_spec_hits=" ++ toString t.specHits ++ "/" ++ toString t.specQueries,
      "query_digest_hits=" ++ toString t.digestHits ++ "/" ++ toString t.digestQueries,
      "query_total_hits=" ++ toString t.totalHits ++ "/" ++ toString t.totalQueries,
      "query_total_misses=" ++ toString t.totalMisses
    ]

def renderQueryTelemetryJson (t : QueryTelemetry) : String :=
  String.intercalate ""
    [
      "{",
      "\"idxQueries\":", toString t.idxQueries, ",",
      "\"idxHits\":", toString t.idxHits, ",",
      "\"specQueries\":", toString t.specQueries, ",",
      "\"specHits\":", toString t.specHits, ",",
      "\"digestQueries\":", toString t.digestQueries, ",",
      "\"digestHits\":", toString t.digestHits, ",",
      "\"totalQueries\":", toString t.totalQueries, ",",
      "\"totalHits\":", toString t.totalHits, ",",
      "\"totalMisses\":", toString t.totalMisses,
      "}"
    ]

def renderQueryTraceSummary (trace : QueryTrace) : String :=
  String.intercalate "\n"
    (trace.rows.map (fun r => "query_trace kind=" ++ r.kind ++ " key=" ++ r.key ++ " hit=" ++ toString r.hit))

private def escapeJsonField (s : String) : String :=
  (((s.replace "\\" "\\\\").replace "\"" "\\\"").replace "\n" "\\n")

private def renderTraceRowsJson (rows : List QueryTraceRow) : String :=
  let elems :=
    rows.map (fun r =>
      String.intercalate ""
        [
          "{",
          "\"kind\":\"", escapeJsonField r.kind, "\",",
          "\"key\":\"", escapeJsonField r.key, "\",",
          "\"hit\":", toString r.hit,
          "}"
        ])
  "[" ++ String.intercalate ", " elems ++ "]"

def renderQueryTraceJson (trace : QueryTrace) : String :=
  String.intercalate ""
    [
      "{",
      "\"rows\":", renderTraceRowsJson trace.rows,
      "}"
    ]

def traceDigest (trace : QueryTrace) : String :=
  let rowDigests := trace.rows.map (fun r => r.kind ++ ":" ++ r.key ++ ":" ++ toString r.hit)
  String.intercalate "|"
    [
      "dispatch-trace-v1",
      toString trace.rows.length,
      String.intercalate ";" rowDigests
    ]

def traceOrderChecksum (trace : QueryTrace) : String :=
  let order := trace.rows.map (fun r => r.kind ++ ":" ++ r.key)
  String.intercalate "|"
    [
      "dispatch-trace-order-v1",
      toString trace.rows.length,
      String.intercalate ";" order
    ]

def traceKindRows (trace : QueryTrace) (kind : String) : Nat :=
  (trace.rows.filter (fun r => r.kind = kind)).length

def traceIdxRows (trace : QueryTrace) : Nat :=
  traceKindRows trace "idx"

def traceSpecRows (trace : QueryTrace) : Nat :=
  traceKindRows trace "spec"

def traceDigestRows (trace : QueryTrace) : Nat :=
  traceKindRows trace "digest"

def traceKindHits (trace : QueryTrace) (kind : String) : Nat :=
  (trace.rows.filter (fun r => r.kind = kind && r.hit)).length

def traceIdxHits (trace : QueryTrace) : Nat :=
  traceKindHits trace "idx"

def traceSpecHits (trace : QueryTrace) : Nat :=
  traceKindHits trace "spec"

def traceDigestHits (trace : QueryTrace) : Nat :=
  traceKindHits trace "digest"

def traceCountConsistent (t : QueryTelemetry) (trace : QueryTrace) : Bool :=
  decide (trace.rows.length = t.totalQueries)

theorem queryTrace_count_matches_telemetry (batch : DispatchBatch)
    (idxs : List Nat) (specIds : List String) (digests : List String) :
    (queryTrace batch idxs specIds digests).rows.length =
      (queryTelemetry batch idxs specIds digests).totalQueries := by
  simp [queryTrace, queryTelemetry, Nat.add_assoc]

def traceKindCountsConsistent (t : QueryTelemetry) (trace : QueryTrace) : Bool :=
  decide (
    traceIdxRows trace = t.idxQueries ∧
    traceSpecRows trace = t.specQueries ∧
    traceDigestRows trace = t.digestQueries
  )

def traceHitCountsConsistent (t : QueryTelemetry) (trace : QueryTrace) : Bool :=
  decide (
    traceIdxHits trace = t.idxHits ∧
    traceSpecHits trace = t.specHits ∧
    traceDigestHits trace = t.digestHits
  )

def traceDriftClass (t : QueryTelemetry) (trace : QueryTrace) : String :=
  let volumeMismatch := !(traceCountConsistent t trace) || !(traceKindCountsConsistent t trace)
  let hitMismatch := !(traceHitCountsConsistent t trace)
  if volumeMismatch && hitMismatch then
    "both"
  else if volumeMismatch then
    "volume_mismatch"
  else if hitMismatch then
    "hit_mismatch"
  else
    "none"

def traceRemediationHint (t : QueryTelemetry) (trace : QueryTrace) : String :=
  match traceDriftClass t trace with
  | "none" => "no_action"
  | "volume_mismatch" => "trace_volume_rebuild"
  | "hit_mismatch" => "lookup_hit_reconcile"
  | "both" => "full_reconcile"
  | _ => "full_reconcile"

def traceRemediationPriority (t : QueryTelemetry) (trace : QueryTrace) : Nat :=
  match traceDriftClass t trace with
  | "none" => 0
  | "volume_mismatch" => 1
  | "hit_mismatch" => 2
  | "both" => 3
  | _ => 3

def traceAlertKey (t : QueryTelemetry) (trace : QueryTrace) : String :=
  toString (traceRemediationPriority t trace) ++
    "|" ++ traceRemediationHint t trace ++
    "|" ++ traceOrderChecksum trace

def renderRemediationPacketJson (t : QueryTelemetry) (trace : QueryTrace) : String :=
  String.intercalate ""
    [
      "{",
      "\"driftClass\":\"", escapeJsonField (traceDriftClass t trace), "\",",
      "\"remediationHint\":\"", escapeJsonField (traceRemediationHint t trace), "\",",
      "\"remediationPriority\":", toString (traceRemediationPriority t trace), ",",
      "\"alertKey\":\"", escapeJsonField (traceAlertKey t trace), "\"",
      "}"
    ]

def renderRemediationPacketBatchJson (rows : List (QueryTelemetry × QueryTrace)) : String :=
  let elems :=
    rows.map (fun row => renderRemediationPacketJson row.fst row.snd)
  "[" ++ String.intercalate ", " elems ++ "]"

structure LabeledRemediationPacketRow where
  label : String
  telemetry : QueryTelemetry
  trace : QueryTrace

def renderLabeledRemediationPacketBatchJson (rows : List LabeledRemediationPacketRow) : String :=
  let elems :=
    rows.map (fun r =>
      String.intercalate ""
        [
          "{",
          "\"label\":\"", escapeJsonField r.label, "\",",
          "\"packet\":", renderRemediationPacketJson r.telemetry r.trace,
          "}"
        ])
  "[" ++ String.intercalate ", " elems ++ "]"

def remediationQueueSchema : String :=
  "heytingveil.intake.remediation_queue.v1"

def labeledRowAlertKey (row : LabeledRemediationPacketRow) : String :=
  traceAlertKey row.telemetry row.trace

def queueEnvelopeFingerprint (rows : List LabeledRemediationPacketRow) : String :=
  let firstAlert :=
    match rows with
    | [] => ""
    | r :: _ => labeledRowAlertKey r
  let lastAlert :=
    match rows.reverse with
    | [] => ""
    | r :: _ => labeledRowAlertKey r
  String.intercalate "|"
    [
      remediationQueueSchema,
      toString rows.length,
      firstAlert,
      lastAlert
    ]

def labeledRowPriority (row : LabeledRemediationPacketRow) : Nat :=
  traceRemediationPriority row.telemetry row.trace

def queueMaxPriority (rows : List LabeledRemediationPacketRow) : Nat :=
  rows.foldl (fun acc row => Nat.max acc (labeledRowPriority row)) 0

def queueHasCritical (rows : List LabeledRemediationPacketRow) : Bool :=
  decide (queueMaxPriority rows = 3)

def queueTopPriorityRow? (rows : List LabeledRemediationPacketRow) : Option LabeledRemediationPacketRow :=
  match rows with
  | [] => none
  | r :: rs =>
      some (rs.foldl
        (fun best row =>
          if labeledRowPriority row > labeledRowPriority best then row else best)
        r)

def queueTopLabel (rows : List LabeledRemediationPacketRow) : String :=
  match queueTopPriorityRow? rows with
  | some row => row.label
  | none => ""

def queueTopAlertKey (rows : List LabeledRemediationPacketRow) : String :=
  match queueTopPriorityRow? rows with
  | some row => labeledRowAlertKey row
  | none => ""

def queueCriticalRows (rows : List LabeledRemediationPacketRow) : List LabeledRemediationPacketRow :=
  rows.filter (fun row => labeledRowPriority row = 3)

def queueCriticalCount (rows : List LabeledRemediationPacketRow) : Nat :=
  (queueCriticalRows rows).length

def queueCriticalLabels (rows : List LabeledRemediationPacketRow) : List String :=
  (queueCriticalRows rows).map (fun row => row.label)

def queueHealthStatus (rows : List LabeledRemediationPacketRow) : String :=
  if queueHasCritical rows then
    "critical"
  else if queueMaxPriority rows > 0 then
    "warning"
  else
    "ok"

def queueStatusToken (rows : List LabeledRemediationPacketRow) : String :=
  String.intercalate "|"
    [
      queueHealthStatus rows,
      toString (queueMaxPriority rows),
      toString (queueCriticalCount rows),
      queueEnvelopeFingerprint rows
    ]

def renderStringJsonList (xs : List String) : String :=
  let elems := xs.map (fun x => "\"" ++ escapeJsonField x ++ "\"")
  "[" ++ String.intercalate ", " elems ++ "]"

structure QueueHeader where
  schema : String
  generatedAt : String
  entryCount : Nat
  maxPriority : Nat
  hasCritical : Bool
  criticalCount : Nat
  criticalLabels : List String
  health : String
  statusToken : String
  topLabel : String
  topAlertKey : String
  fingerprint : String

def queueHeader
    (rows : List LabeledRemediationPacketRow)
    (generatedAt : String := "1970-01-01T00:00:00Z") : QueueHeader :=
  {
    schema := remediationQueueSchema
    generatedAt := generatedAt
    entryCount := rows.length
    maxPriority := queueMaxPriority rows
    hasCritical := queueHasCritical rows
    criticalCount := queueCriticalCount rows
    criticalLabels := queueCriticalLabels rows
    health := queueHealthStatus rows
    statusToken := queueStatusToken rows
    topLabel := queueTopLabel rows
    topAlertKey := queueTopAlertKey rows
    fingerprint := queueEnvelopeFingerprint rows
  }

@[simp] theorem queueHeader_schema (rows : List LabeledRemediationPacketRow) (generatedAt : String) :
    (queueHeader rows generatedAt).schema = remediationQueueSchema := by
  rfl

@[simp] theorem queueHeader_generatedAt (rows : List LabeledRemediationPacketRow) (generatedAt : String) :
    (queueHeader rows generatedAt).generatedAt = generatedAt := by
  rfl

@[simp] theorem queueHeader_entryCount (rows : List LabeledRemediationPacketRow) (generatedAt : String) :
    (queueHeader rows generatedAt).entryCount = rows.length := by
  rfl

@[simp] theorem queueHeader_maxPriority (rows : List LabeledRemediationPacketRow) (generatedAt : String) :
    (queueHeader rows generatedAt).maxPriority = queueMaxPriority rows := by
  rfl

@[simp] theorem queueHeader_hasCritical (rows : List LabeledRemediationPacketRow) (generatedAt : String) :
    (queueHeader rows generatedAt).hasCritical = queueHasCritical rows := by
  rfl

@[simp] theorem queueHeader_criticalCount (rows : List LabeledRemediationPacketRow) (generatedAt : String) :
    (queueHeader rows generatedAt).criticalCount = queueCriticalCount rows := by
  rfl

@[simp] theorem queueHeader_criticalLabels (rows : List LabeledRemediationPacketRow) (generatedAt : String) :
    (queueHeader rows generatedAt).criticalLabels = queueCriticalLabels rows := by
  rfl

@[simp] theorem queueHeader_health (rows : List LabeledRemediationPacketRow) (generatedAt : String) :
    (queueHeader rows generatedAt).health = queueHealthStatus rows := by
  rfl

@[simp] theorem queueHeader_statusToken (rows : List LabeledRemediationPacketRow) (generatedAt : String) :
    (queueHeader rows generatedAt).statusToken = queueStatusToken rows := by
  rfl

@[simp] theorem queueHeader_topLabel (rows : List LabeledRemediationPacketRow) (generatedAt : String) :
    (queueHeader rows generatedAt).topLabel = queueTopLabel rows := by
  rfl

@[simp] theorem queueHeader_topAlertKey (rows : List LabeledRemediationPacketRow) (generatedAt : String) :
    (queueHeader rows generatedAt).topAlertKey = queueTopAlertKey rows := by
  rfl

@[simp] theorem queueHeader_fingerprint (rows : List LabeledRemediationPacketRow) (generatedAt : String) :
    (queueHeader rows generatedAt).fingerprint = queueEnvelopeFingerprint rows := by
  rfl

def renderQueueHeaderFieldsJson (h : QueueHeader) : String :=
  String.intercalate ""
    [
      "\"schema\":\"", escapeJsonField h.schema, "\",",
      "\"generatedAt\":\"", escapeJsonField h.generatedAt, "\",",
      "\"entryCount\":", toString h.entryCount, ",",
      "\"maxPriority\":", toString h.maxPriority, ",",
      "\"hasCritical\":", toString h.hasCritical, ",",
      "\"criticalCount\":", toString h.criticalCount, ",",
      "\"criticalLabels\":", renderStringJsonList h.criticalLabels, ",",
      "\"health\":\"", escapeJsonField h.health, "\",",
      "\"statusToken\":\"", escapeJsonField h.statusToken, "\",",
      "\"topLabel\":\"", escapeJsonField h.topLabel, "\",",
      "\"topAlertKey\":\"", escapeJsonField h.topAlertKey, "\",",
      "\"fingerprint\":\"", escapeJsonField h.fingerprint, "\""
    ]

def renderQueueHeaderJson (h : QueueHeader) : String :=
  "{" ++ renderQueueHeaderFieldsJson h ++ "}"

def renderLabeledRemediationQueueEnvelopeJson
    (rows : List LabeledRemediationPacketRow)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  let h := queueHeader rows generatedAt
  String.intercalate ""
    [
      "{",
      renderQueueHeaderFieldsJson h, ",",
      "\"entries\":", renderLabeledRemediationPacketBatchJson rows,
      "}"
    ]

def renderLabeledRemediationQueueHeaderJson
    (rows : List LabeledRemediationPacketRow)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  renderQueueHeaderJson (queueHeader rows generatedAt)

structure QueueSnapshotBundle where
  schema : String
  generatedAt : String
  header : QueueHeader
  entries : List LabeledRemediationPacketRow

def queueSnapshotBundle
    (rows : List LabeledRemediationPacketRow)
    (generatedAt : String := "1970-01-01T00:00:00Z") : QueueSnapshotBundle :=
  {
    schema := remediationQueueSchema
    generatedAt := generatedAt
    header := queueHeader rows generatedAt
    entries := rows
  }

def bundleMetadataConsistent (b : QueueSnapshotBundle) : Bool :=
  let h := b.header
  decide (
    h.schema = b.schema ∧
    h.generatedAt = b.generatedAt ∧
    h.entryCount = b.entries.length ∧
    h.maxPriority = queueMaxPriority b.entries ∧
    h.hasCritical = queueHasCritical b.entries ∧
    h.criticalCount = queueCriticalCount b.entries ∧
    h.criticalLabels = queueCriticalLabels b.entries ∧
    h.health = queueHealthStatus b.entries ∧
    h.statusToken = queueStatusToken b.entries ∧
    h.topLabel = queueTopLabel b.entries ∧
    h.topAlertKey = queueTopAlertKey b.entries ∧
    h.fingerprint = queueEnvelopeFingerprint b.entries
  )

def queueSnapshotBundleConsistent
    (rows : List LabeledRemediationPacketRow)
    (generatedAt : String := "1970-01-01T00:00:00Z") : Bool :=
  bundleMetadataConsistent (queueSnapshotBundle rows generatedAt)

theorem queueSnapshotBundleConsistent_true
    (rows : List LabeledRemediationPacketRow)
    (generatedAt : String) :
    queueSnapshotBundleConsistent rows generatedAt = true := by
  simp [queueSnapshotBundleConsistent, bundleMetadataConsistent, queueSnapshotBundle]

@[simp] theorem queueSnapshotBundle_schema (rows : List LabeledRemediationPacketRow) (generatedAt : String) :
    (queueSnapshotBundle rows generatedAt).schema = remediationQueueSchema := by
  rfl

@[simp] theorem queueSnapshotBundle_generatedAt (rows : List LabeledRemediationPacketRow) (generatedAt : String) :
    (queueSnapshotBundle rows generatedAt).generatedAt = generatedAt := by
  rfl

@[simp] theorem queueSnapshotBundle_header (rows : List LabeledRemediationPacketRow) (generatedAt : String) :
    (queueSnapshotBundle rows generatedAt).header = queueHeader rows generatedAt := by
  rfl

@[simp] theorem queueSnapshotBundle_entries (rows : List LabeledRemediationPacketRow) (generatedAt : String) :
    (queueSnapshotBundle rows generatedAt).entries = rows := by
  rfl

def renderLabeledRemediationQueueBundleJson
    (rows : List LabeledRemediationPacketRow)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  let bundle := queueSnapshotBundle rows generatedAt
  let header := renderQueueHeaderJson bundle.header
  let envelope := renderLabeledRemediationQueueEnvelopeJson bundle.entries bundle.generatedAt
  String.intercalate ""
    [
      "{",
      "\"schema\":\"", escapeJsonField bundle.schema, "\",",
      "\"generatedAt\":\"", escapeJsonField bundle.generatedAt, "\",",
      "\"header\":", header, ",",
      "\"envelope\":", envelope,
      "}"
    ]

def renderLabeledRemediationQueueBundleConsistencySummary
    (rows : List LabeledRemediationPacketRow)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  "bundle_metadata_consistent=" ++ toString (queueSnapshotBundleConsistent rows generatedAt)

def renderTelemetryTraceSummary (t : QueryTelemetry) (trace : QueryTrace) : String :=
  String.intercalate "\n"
    [
      renderQueryTelemetrySummary t,
      "query_trace_rows=" ++ toString trace.rows.length,
      "query_trace_idx_rows=" ++ toString (traceIdxRows trace),
      "query_trace_spec_rows=" ++ toString (traceSpecRows trace),
      "query_trace_digest_rows=" ++ toString (traceDigestRows trace),
      "query_trace_idx_hits=" ++ toString (traceIdxHits trace) ++ "/" ++ toString (traceIdxRows trace),
      "query_trace_spec_hits=" ++ toString (traceSpecHits trace) ++ "/" ++ toString (traceSpecRows trace),
      "query_trace_digest_hits=" ++ toString (traceDigestHits trace) ++ "/" ++ toString (traceDigestRows trace),
      "query_trace_count_consistent=" ++ toString (traceCountConsistent t trace),
      "query_trace_kind_counts_consistent=" ++ toString (traceKindCountsConsistent t trace),
      "query_trace_hit_counts_consistent=" ++ toString (traceHitCountsConsistent t trace),
      "query_trace_drift_class=" ++ traceDriftClass t trace,
      "query_trace_remediation_hint=" ++ traceRemediationHint t trace,
      "query_trace_remediation_priority=" ++ toString (traceRemediationPriority t trace),
      "query_trace_alert_key=" ++ traceAlertKey t trace,
      "query_trace_digest=" ++ traceDigest trace,
      "query_trace_order_checksum=" ++ traceOrderChecksum trace
    ]

def renderTelemetryTraceJson (t : QueryTelemetry) (trace : QueryTrace) : String :=
  String.intercalate ""
    [
      "{",
      "\"telemetry\":", renderQueryTelemetryJson t, ",",
      "\"trace\":", renderQueryTraceJson trace, ",",
      "\"traceRows\":", toString trace.rows.length, ",",
      "\"traceIdxRows\":", toString (traceIdxRows trace), ",",
      "\"traceSpecRows\":", toString (traceSpecRows trace), ",",
      "\"traceDigestRows\":", toString (traceDigestRows trace), ",",
      "\"traceIdxHits\":", toString (traceIdxHits trace), ",",
      "\"traceSpecHits\":", toString (traceSpecHits trace), ",",
      "\"traceDigestHits\":", toString (traceDigestHits trace), ",",
      "\"countConsistent\":", toString (traceCountConsistent t trace), ",",
      "\"kindCountsConsistent\":", toString (traceKindCountsConsistent t trace), ",",
      "\"hitCountsConsistent\":", toString (traceHitCountsConsistent t trace), ",",
      "\"driftClass\":\"", escapeJsonField (traceDriftClass t trace), "\",",
      "\"remediationHint\":\"", escapeJsonField (traceRemediationHint t trace), "\",",
      "\"remediationPriority\":", toString (traceRemediationPriority t trace), ",",
      "\"alertKey\":\"", escapeJsonField (traceAlertKey t trace), "\",",
      "\"traceDigest\":\"", escapeJsonField (traceDigest trace), "\",",
      "\"traceOrderChecksum\":\"", escapeJsonField (traceOrderChecksum trace), "\"",
      "}"
    ]

/-- Deterministic JSON-style batch payload with aggregate counters and intents. -/
def renderJson (batch : DispatchBatch) : String :=
  String.intercalate ""
    [
      "{",
      "\"total\":", toString (totalCount batch), ",",
      "\"ready\":", toString (readyCount batch), ",",
      "\"blocked\":", toString (blockedCount batch), ",",
      "\"consistencyOk\":", toString (consistencyOk batch), ",",
      "\"integrityDigest\":\"", escapeJson (integrityDigest batch), "\",",
      "\"summary\":\"", escapeJson (renderSummary batch), "\",",
      "\"intents\":", renderIntentJsonList batch.intents, ",",
      "\"indexedIntents\":", renderIndexedIntentJsonList batch.intents,
      "}"
    ]

def renderDispatchRemediationHandoffJson
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  let dispatchPayload := renderJson batch
  let queuePayload := renderLabeledRemediationQueueBundleJson queueRows generatedAt
  String.intercalate ""
    [
      "{",
      "\"dispatchBatch\":", dispatchPayload, ",",
      "\"remediationQueue\":", queuePayload,
      "}"
    ]

def renderDispatchRemediationHandoffQuickSummaryJson
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  let bridgeReadyCount :=
    (batch.intents.filter (fun i => i.adapterTuple.bridgeHooksReady)).length
  let bridgeReadyAll := decide (bridgeReadyCount = totalCount batch)
  let unresolvedBridgeSpecs :=
    (batch.intents.filter (fun i => !i.adapterTuple.bridgeHooksReady))
      |>.map (fun i => i.adapterTuple.specIdHint)
  String.intercalate ""
    [
      "{",
      "\"dispatchDigest\":\"", escapeJsonField (integrityDigest batch), "\",",
      "\"queueFingerprint\":\"", escapeJsonField (queueEnvelopeFingerprint queueRows), "\",",
      "\"queueHealth\":\"", escapeJsonField (queueHealthStatus queueRows), "\",",
      "\"bridgeHooksReadyCount\":", toString bridgeReadyCount, ",",
      "\"bridgeHooksReadyAll\":", toString bridgeReadyAll, ",",
      "\"unresolvedBridgeSpecs\":", renderStringJsonList unresolvedBridgeSpecs, ",",
      "\"bundleConsistent\":", toString (queueSnapshotBundleConsistent queueRows generatedAt),
      "}"
    ]

def bridgeHooksReadyCount (batch : DispatchBatch) : Nat :=
  (batch.intents.filter (fun i => i.adapterTuple.bridgeHooksReady)).length

def bridgeHooksReadyAll (batch : DispatchBatch) : Bool :=
  decide (bridgeHooksReadyCount batch = totalCount batch)

def unresolvedBridgeSpecLabels (batch : DispatchBatch) : List String :=
  (batch.intents.filter (fun i => !i.adapterTuple.bridgeHooksReady))
    |>.map (fun i => i.adapterTuple.specIdHint)

def bridgeGateAllowsExecution (batch : DispatchBatch) : Bool :=
  bridgeHooksReadyAll batch

def bridgeGateReason (batch : DispatchBatch) : String :=
  if bridgeGateAllowsExecution batch then
    "ok"
  else
    "bridge_assignment_required"

structure HandoffQuickView where
  dispatchDigest : String
  queueFingerprint : String
  queueHealth : String
  bridgeHooksReadyAll : Bool
  unresolvedBridgeSpecCount : Nat
  bundleConsistent : Bool
deriving Repr, DecidableEq

def handoffQuickView
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (generatedAt : String := "1970-01-01T00:00:00Z") : HandoffQuickView :=
  {
    dispatchDigest := integrityDigest batch
    queueFingerprint := queueEnvelopeFingerprint queueRows
    queueHealth := queueHealthStatus queueRows
    bridgeHooksReadyAll := bridgeHooksReadyAll batch
    unresolvedBridgeSpecCount := (unresolvedBridgeSpecLabels batch).length
    bundleConsistent := queueSnapshotBundleConsistent queueRows generatedAt
  }

def handoffDeepView
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (generatedAt : String := "1970-01-01T00:00:00Z") : HandoffQuickView :=
  let h := queueHeader queueRows generatedAt
  {
    dispatchDigest := integrityDigest batch
    queueFingerprint := h.fingerprint
    queueHealth := h.health
    bridgeHooksReadyAll := bridgeHooksReadyAll batch
    unresolvedBridgeSpecCount := (unresolvedBridgeSpecLabels batch).length
    bundleConsistent := queueSnapshotBundleConsistent queueRows generatedAt
  }

def quickConsistentWithHandoff
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (generatedAt : String := "1970-01-01T00:00:00Z") : Bool :=
  decide (handoffQuickView batch queueRows generatedAt = handoffDeepView batch queueRows generatedAt)

theorem quickConsistentWithHandoff_true
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (generatedAt : String) :
    quickConsistentWithHandoff batch queueRows generatedAt = true := by
  simp [quickConsistentWithHandoff, handoffQuickView, handoffDeepView, queueHeader]

def renderDispatchRemediationControlPlaneJson
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  let quick := renderDispatchRemediationHandoffQuickSummaryJson batch queueRows generatedAt
  let handoff := renderDispatchRemediationHandoffJson batch queueRows generatedAt
  String.intercalate ""
    [
      "{",
      "\"quickSummary\":", quick, ",",
      "\"quickConsistentWithHandoff\":", toString (quickConsistentWithHandoff batch queueRows generatedAt), ",",
      "\"handoff\":", handoff,
      "}"
    ]

def controlPlaneHeaderPollingToken
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  String.intercalate "|"
    [
      integrityDigest batch,
      queueEnvelopeFingerprint queueRows,
      toString (quickConsistentWithHandoff batch queueRows generatedAt)
    ]

def renderDispatchRemediationControlPlaneHeaderJson
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  let quick := renderDispatchRemediationHandoffQuickSummaryJson batch queueRows generatedAt
  let quickConsistent := quickConsistentWithHandoff batch queueRows generatedAt
  let pollToken := controlPlaneHeaderPollingToken batch queueRows generatedAt
  String.intercalate ""
    [
      "{",
      "\"quickSummary\":", quick, ",",
      "\"quickConsistentWithHandoff\":", toString quickConsistent, ",",
      "\"pollToken\":\"", escapeJsonField pollToken, "\"",
      "}"
    ]

def controlPlanePollingToken
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  String.intercalate "|"
    [
      integrityDigest batch,
      queueEnvelopeFingerprint queueRows,
      toString (quickConsistentWithHandoff batch queueRows generatedAt)
    ]

theorem controlPlaneHeaderPollingToken_eq_controlPlanePollingToken
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (generatedAt : String) :
    controlPlaneHeaderPollingToken batch queueRows generatedAt =
      controlPlanePollingToken batch queueRows generatedAt := by
  simp [controlPlaneHeaderPollingToken, controlPlanePollingToken]

def pollTokenAlignedWithHeader
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (generatedAt : String := "1970-01-01T00:00:00Z") : Bool :=
  decide (
    controlPlaneHeaderPollingToken batch queueRows generatedAt =
      controlPlanePollingToken batch queueRows generatedAt
  )

theorem pollTokenAlignedWithHeader_true
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (generatedAt : String) :
    pollTokenAlignedWithHeader batch queueRows generatedAt = true := by
  simp [pollTokenAlignedWithHeader, controlPlaneHeaderPollingToken_eq_controlPlanePollingToken]

def renderDispatchRemediationPollSnapshotJson
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  String.intercalate ""
    [
      "{",
      "\"generatedAt\":\"", escapeJsonField generatedAt, "\",",
      "\"pollToken\":\"", escapeJsonField (controlPlanePollingToken batch queueRows generatedAt), "\",",
      "\"queueHealth\":\"", escapeJsonField (queueHealthStatus queueRows), "\",",
      "\"pollTokenAlignedWithHeader\":", toString (pollTokenAlignedWithHeader batch queueRows generatedAt),
      "}"
    ]

def renderDispatchRemediationPollAlignmentSummary
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  "poll_token_aligned_with_header=" ++ toString (pollTokenAlignedWithHeader batch queueRows generatedAt)

def pollContractSchema : String :=
  "heytingveil.intake.control_plane_poll_contract.v1"

def pollContractConsistent
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (generatedAt : String := "1970-01-01T00:00:00Z") : Bool :=
  decide (
    controlPlaneHeaderPollingToken batch queueRows generatedAt =
      controlPlanePollingToken batch queueRows generatedAt ∧
    pollTokenAlignedWithHeader batch queueRows generatedAt = true
  )

theorem pollContractConsistent_true
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (generatedAt : String) :
    pollContractConsistent batch queueRows generatedAt = true := by
  simp [
    pollContractConsistent,
    controlPlaneHeaderPollingToken_eq_controlPlanePollingToken,
    pollTokenAlignedWithHeader_true
  ]

def renderDispatchRemediationPollContractJson
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  String.intercalate ""
    [
      "{",
      "\"schema\":\"", escapeJsonField pollContractSchema, "\",",
      "\"generatedAt\":\"", escapeJsonField generatedAt, "\",",
      "\"header\":", renderDispatchRemediationControlPlaneHeaderJson batch queueRows generatedAt, ",",
      "\"snapshot\":", renderDispatchRemediationPollSnapshotJson batch queueRows generatedAt, ",",
      "\"pollAlignmentSummary\":\"", escapeJsonField (renderDispatchRemediationPollAlignmentSummary batch queueRows generatedAt), "\",",
      "\"pollContractConsistent\":", toString (pollContractConsistent batch queueRows generatedAt),
      "}"
    ]

def pollChangedSince
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : Bool :=
  decide (controlPlanePollingToken batch queueRows generatedAt ≠ baselinePollToken)

theorem pollChangedSince_self_false
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (generatedAt : String) :
    pollChangedSince batch queueRows (controlPlanePollingToken batch queueRows generatedAt) generatedAt = false := by
  simp [pollChangedSince]

def renderPollChangedSinceSummary
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  "poll_changed_since_baseline=" ++
    toString (pollChangedSince batch queueRows baselinePollToken generatedAt)

def pollResponseSchema : String :=
  "heytingveil.intake.control_plane_poll_response.v1"

def renderDispatchRemediationPollResponseJson
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  let current := controlPlanePollingToken batch queueRows generatedAt
  let changed := pollChangedSince batch queueRows baselinePollToken generatedAt
  let summary := renderPollChangedSinceSummary batch queueRows baselinePollToken generatedAt
  String.intercalate ""
    [
      "{",
      "\"schema\":\"", escapeJsonField pollResponseSchema, "\",",
      "\"generatedAt\":\"", escapeJsonField generatedAt, "\",",
      "\"baselinePollToken\":\"", escapeJsonField baselinePollToken, "\",",
      "\"currentPollToken\":\"", escapeJsonField current, "\",",
      "\"changed\":", toString changed, ",",
      "\"changeSummary\":\"", escapeJsonField summary, "\",",
      "\"pollContract\":", renderDispatchRemediationPollContractJson batch queueRows generatedAt,
      "}"
    ]

def pollAction
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  if pollChangedSince batch queueRows baselinePollToken generatedAt then
    "refresh"
  else
    "noop"

def effectiveAction
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  if bridgeGateAllowsExecution batch then
    pollAction batch queueRows baselinePollToken generatedAt
  else
    "blocked_bridge_assignment"

theorem pollAction_self_noop
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (generatedAt : String) :
    pollAction batch queueRows (controlPlanePollingToken batch queueRows generatedAt) generatedAt = "noop" := by
  simp [pollAction, pollChangedSince_self_false]

def pollActionReason
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  if pollChangedSince batch queueRows baselinePollToken generatedAt then
    "token_drift"
  else
    "unchanged"

def effectiveReason
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  if bridgeGateAllowsExecution batch then
    pollActionReason batch queueRows baselinePollToken generatedAt
  else
    bridgeGateReason batch

def effectiveStatus
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  let action := effectiveAction batch queueRows baselinePollToken generatedAt
  let reason := effectiveReason batch queueRows baselinePollToken generatedAt
  if action = "blocked_bridge_assignment" then
    "blocked_bridge_assignment_required"
  else if action = "refresh" ∧ reason = "token_drift" then
    "refresh_token_drift"
  else if action = "noop" ∧ reason = "unchanged" then
    "noop_unchanged"
  else
    action ++ "_" ++ reason

theorem effectiveStatus_gate_open
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String)
    (hGate : bridgeGateAllowsExecution batch = true) :
    effectiveStatus batch queueRows baselinePollToken generatedAt =
      (if pollChangedSince batch queueRows baselinePollToken generatedAt then
        "refresh_token_drift"
      else
        "noop_unchanged") := by
  by_cases hChanged : pollChangedSince batch queueRows baselinePollToken generatedAt = true
  · simp [effectiveStatus, effectiveAction, effectiveReason, pollAction, pollActionReason, hGate, hChanged]
  · have hChangedFalse : pollChangedSince batch queueRows baselinePollToken generatedAt = false := by
      cases hBool : pollChangedSince batch queueRows baselinePollToken generatedAt <;> simp_all
    simp [effectiveStatus, effectiveAction, effectiveReason, pollAction, pollActionReason, hGate, hChangedFalse]

theorem effectiveStatus_gate_blocked
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String)
    (hGate : bridgeGateAllowsExecution batch = false) :
    effectiveStatus batch queueRows baselinePollToken generatedAt =
      "blocked_bridge_assignment_required" := by
  simp [effectiveStatus, effectiveAction, hGate]

def effectiveStatusClass
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  let status := effectiveStatus batch queueRows baselinePollToken generatedAt
  if status = "blocked_bridge_assignment_required" then
    "blocked"
  else if status = "refresh_token_drift" then
    "executable_refresh"
  else
    "executable_noop"

theorem effectiveStatusClass_gate_open
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String)
    (hGate : bridgeGateAllowsExecution batch = true) :
    effectiveStatusClass batch queueRows baselinePollToken generatedAt =
      (if pollChangedSince batch queueRows baselinePollToken generatedAt then
        "executable_refresh"
      else
        "executable_noop") := by
  by_cases hChanged : pollChangedSince batch queueRows baselinePollToken generatedAt = true
  · simp [effectiveStatusClass, effectiveStatus_gate_open, hGate, hChanged]
  · have hChangedFalse : pollChangedSince batch queueRows baselinePollToken generatedAt = false := by
      cases hBool : pollChangedSince batch queueRows baselinePollToken generatedAt <;> simp_all
    simp [effectiveStatusClass, effectiveStatus_gate_open, hGate, hChangedFalse]

theorem effectiveStatusClass_gate_blocked
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String)
    (hGate : bridgeGateAllowsExecution batch = false) :
    effectiveStatusClass batch queueRows baselinePollToken generatedAt = "blocked" := by
  simp [effectiveStatusClass, effectiveStatus_gate_blocked, hGate]

def effectiveExecutionAllowed
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : Bool :=
  if effectiveStatusClass batch queueRows baselinePollToken generatedAt = "blocked" then
    false
  else
    true

theorem effectiveExecutionAllowed_gate_open
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String)
    (hGate : bridgeGateAllowsExecution batch = true) :
    effectiveExecutionAllowed batch queueRows baselinePollToken generatedAt = true := by
  have hClass :
      effectiveStatusClass batch queueRows baselinePollToken generatedAt =
        (if pollChangedSince batch queueRows baselinePollToken generatedAt then
          "executable_refresh"
        else
          "executable_noop") :=
    effectiveStatusClass_gate_open batch queueRows baselinePollToken generatedAt hGate
  rw [effectiveExecutionAllowed, hClass]
  by_cases hChanged : pollChangedSince batch queueRows baselinePollToken generatedAt = true
  · simp [hChanged]
  · have hChangedFalse : pollChangedSince batch queueRows baselinePollToken generatedAt = false := by
      cases hBool : pollChangedSince batch queueRows baselinePollToken generatedAt <;> simp_all
    simp [hChangedFalse]

theorem effectiveExecutionAllowed_gate_blocked
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String)
    (hGate : bridgeGateAllowsExecution batch = false) :
    effectiveExecutionAllowed batch queueRows baselinePollToken generatedAt = false := by
  simp [effectiveExecutionAllowed, effectiveStatusClass_gate_blocked, hGate]

def effectiveExecutionDirective
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  if effectiveExecutionAllowed batch queueRows baselinePollToken generatedAt then
    "execute_now"
  else
    "await_bridge_assignment"

theorem effectiveExecutionDirective_gate_open
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String)
    (hGate : bridgeGateAllowsExecution batch = true) :
    effectiveExecutionDirective batch queueRows baselinePollToken generatedAt = "execute_now" := by
  simp [effectiveExecutionDirective, effectiveExecutionAllowed_gate_open, hGate]

theorem effectiveExecutionDirective_gate_blocked
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String)
    (hGate : bridgeGateAllowsExecution batch = false) :
    effectiveExecutionDirective batch queueRows baselinePollToken generatedAt =
      "await_bridge_assignment" := by
  simp [effectiveExecutionDirective, effectiveExecutionAllowed_gate_blocked, hGate]

def effectiveRunnerEnvelope
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  "directive=" ++ effectiveExecutionDirective batch queueRows baselinePollToken generatedAt ++
    "|status=" ++ effectiveStatus batch queueRows baselinePollToken generatedAt ++
    "|class=" ++ effectiveStatusClass batch queueRows baselinePollToken generatedAt ++
    "|allowed=" ++ toString (effectiveExecutionAllowed batch queueRows baselinePollToken generatedAt)

def runnerEnvelopeExecuteRefresh : String :=
  "directive=execute_now|status=refresh_token_drift|class=executable_refresh|allowed=" ++ toString true

def runnerEnvelopeExecuteNoop : String :=
  "directive=execute_now|status=noop_unchanged|class=executable_noop|allowed=" ++ toString true

def runnerEnvelopeAwaitBridge : String :=
  "directive=await_bridge_assignment|status=blocked_bridge_assignment_required|class=blocked|allowed=" ++
    toString false

def effectiveExecutionContractVersion : String :=
  "heytingveil.execution.contract.v1"

def effectiveExecutionContractHash
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  "v=" ++ effectiveExecutionContractVersion ++
    "|env=" ++ effectiveRunnerEnvelope batch queueRows baselinePollToken generatedAt

theorem effectiveRunnerEnvelope_gate_open
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String)
    (hGate : bridgeGateAllowsExecution batch = true) :
    effectiveRunnerEnvelope batch queueRows baselinePollToken generatedAt =
      (if pollChangedSince batch queueRows baselinePollToken generatedAt then
        runnerEnvelopeExecuteRefresh
      else
        runnerEnvelopeExecuteNoop) := by
  by_cases hChanged : pollChangedSince batch queueRows baselinePollToken generatedAt = true
  · simp [
      effectiveRunnerEnvelope,
      runnerEnvelopeExecuteRefresh,
      effectiveExecutionDirective_gate_open,
      effectiveStatus_gate_open,
      effectiveStatusClass_gate_open,
      effectiveExecutionAllowed_gate_open,
      hGate,
      hChanged
    ]
  · have hChangedFalse : pollChangedSince batch queueRows baselinePollToken generatedAt = false := by
      cases hBool : pollChangedSince batch queueRows baselinePollToken generatedAt <;> simp_all
    simp [
      effectiveRunnerEnvelope,
      runnerEnvelopeExecuteNoop,
      effectiveExecutionDirective_gate_open,
      effectiveStatus_gate_open,
      effectiveStatusClass_gate_open,
      effectiveExecutionAllowed_gate_open,
      hGate,
      hChangedFalse
    ]

theorem effectiveRunnerEnvelope_gate_blocked
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String)
    (hGate : bridgeGateAllowsExecution batch = false) :
    effectiveRunnerEnvelope batch queueRows baselinePollToken generatedAt =
      runnerEnvelopeAwaitBridge := by
  simp [
    effectiveRunnerEnvelope,
    runnerEnvelopeAwaitBridge,
    effectiveExecutionDirective_gate_blocked,
    effectiveStatus_gate_blocked,
    effectiveStatusClass_gate_blocked,
    effectiveExecutionAllowed_gate_blocked,
    hGate
  ]

theorem effectiveExecutionContractHash_gate_open
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String)
    (hGate : bridgeGateAllowsExecution batch = true) :
    effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt =
      "v=heytingveil.execution.contract.v1|env=" ++
        (if pollChangedSince batch queueRows baselinePollToken generatedAt then
          runnerEnvelopeExecuteRefresh
        else
          runnerEnvelopeExecuteNoop) := by
  simp [effectiveExecutionContractHash, effectiveExecutionContractVersion, effectiveRunnerEnvelope_gate_open, hGate]

theorem effectiveExecutionContractHash_gate_blocked
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String)
    (hGate : bridgeGateAllowsExecution batch = false) :
    effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt =
      "v=heytingveil.execution.contract.v1|env=" ++ runnerEnvelopeAwaitBridge := by
  simp [effectiveExecutionContractHash, effectiveExecutionContractVersion, effectiveRunnerEnvelope_gate_blocked, hGate]

def effectiveExecutionContractCoherent
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : Bool :=
  decide (
    effectiveExecutionContractVersion = "heytingveil.execution.contract.v1" ∧
    effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt =
      "v=heytingveil.execution.contract.v1|env=" ++ effectiveRunnerEnvelope batch queueRows baselinePollToken generatedAt ∧
    (effectiveExecutionAllowed batch queueRows baselinePollToken generatedAt = true ↔
      effectiveExecutionDirective batch queueRows baselinePollToken generatedAt = "execute_now") ∧
    (effectiveExecutionAllowed batch queueRows baselinePollToken generatedAt = false ↔
      effectiveExecutionDirective batch queueRows baselinePollToken generatedAt = "await_bridge_assignment")
  )

theorem effectiveExecutionContractCoherent_true
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String) :
    effectiveExecutionContractCoherent batch queueRows baselinePollToken generatedAt = true := by
  simp [
    effectiveExecutionContractCoherent,
    effectiveExecutionContractVersion,
    effectiveExecutionContractHash,
    effectiveRunnerEnvelope,
    effectiveExecutionAllowed,
    effectiveExecutionDirective
  ]

theorem pollActionReason_self_unchanged
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (generatedAt : String) :
    pollActionReason batch queueRows (controlPlanePollingToken batch queueRows generatedAt) generatedAt = "unchanged" := by
  simp [pollActionReason, pollChangedSince_self_false]

def fetchHandoffDirective
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : Bool :=
  pollChangedSince batch queueRows baselinePollToken generatedAt

theorem fetchHandoffDirective_self_false
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (generatedAt : String) :
    fetchHandoffDirective batch queueRows (controlPlanePollingToken batch queueRows generatedAt) generatedAt = false := by
  simp [fetchHandoffDirective, pollChangedSince_self_false]

def effectiveFetchHandoff
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : Bool :=
  if bridgeGateAllowsExecution batch then
    fetchHandoffDirective batch queueRows baselinePollToken generatedAt
  else
    false

def fetchTarget
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  if fetchHandoffDirective batch queueRows baselinePollToken generatedAt then
    "handoff"
  else
    "none"

theorem fetchTarget_self_none
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (generatedAt : String) :
    fetchTarget batch queueRows (controlPlanePollingToken batch queueRows generatedAt) generatedAt = "none" := by
  simp [fetchTarget, fetchHandoffDirective_self_false]

def effectiveFetchTarget
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  if bridgeGateAllowsExecution batch then
    fetchTarget batch queueRows baselinePollToken generatedAt
  else
    "none"

def pollNextStep
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  if fetchHandoffDirective batch queueRows baselinePollToken generatedAt then
    "fetch_handoff"
  else
    "wait"

theorem pollNextStep_self_wait
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (generatedAt : String) :
    pollNextStep batch queueRows (controlPlanePollingToken batch queueRows generatedAt) generatedAt = "wait" := by
  simp [pollNextStep, fetchHandoffDirective_self_false]

def effectiveNextStep
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  if bridgeGateAllowsExecution batch then
    pollNextStep batch queueRows baselinePollToken generatedAt
  else
    "assign_bridge_hooks"

def pollActionResponseCoherent
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : Bool :=
  let fetch := fetchHandoffDirective batch queueRows baselinePollToken generatedAt
  let action := pollAction batch queueRows baselinePollToken generatedAt
  let target := fetchTarget batch queueRows baselinePollToken generatedAt
  let step := pollNextStep batch queueRows baselinePollToken generatedAt
  decide (
    (fetch = true ↔ action = "refresh") ∧
    (fetch = true ↔ target = "handoff") ∧
    (fetch = true ↔ step = "fetch_handoff")
  )

theorem pollActionResponseCoherent_true
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String) :
    pollActionResponseCoherent batch queueRows baselinePollToken generatedAt = true := by
  simp [
    pollActionResponseCoherent,
    fetchHandoffDirective,
    pollAction,
    fetchTarget,
    pollNextStep
  ]

def renderPollActionResponseCoherenceSummary
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  "poll_action_response_coherent=" ++
    toString (pollActionResponseCoherent batch queueRows baselinePollToken generatedAt)

def pollActionResponseEffectiveCoherent
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : Bool :=
  let gate := bridgeGateAllowsExecution batch
  decide (
    (gate = true ↔ bridgeGateReason batch = "ok") ∧
    (gate = true →
      effectiveAction batch queueRows baselinePollToken generatedAt =
        pollAction batch queueRows baselinePollToken generatedAt) ∧
    (gate = false →
      effectiveAction batch queueRows baselinePollToken generatedAt =
        "blocked_bridge_assignment") ∧
    (gate = true →
      effectiveReason batch queueRows baselinePollToken generatedAt =
        pollActionReason batch queueRows baselinePollToken generatedAt) ∧
    (gate = false →
      effectiveReason batch queueRows baselinePollToken generatedAt =
        bridgeGateReason batch) ∧
    (gate = true →
      effectiveStatus batch queueRows baselinePollToken generatedAt =
        (if pollChangedSince batch queueRows baselinePollToken generatedAt then
          "refresh_token_drift"
        else
          "noop_unchanged")) ∧
    (gate = false →
      effectiveStatus batch queueRows baselinePollToken generatedAt =
        "blocked_bridge_assignment_required") ∧
    (gate = true →
      effectiveStatusClass batch queueRows baselinePollToken generatedAt =
        (if pollChangedSince batch queueRows baselinePollToken generatedAt then
          "executable_refresh"
        else
          "executable_noop")) ∧
    (gate = false →
      effectiveStatusClass batch queueRows baselinePollToken generatedAt =
        "blocked") ∧
    (gate = true →
      effectiveExecutionAllowed batch queueRows baselinePollToken generatedAt = true) ∧
    (gate = false →
      effectiveExecutionAllowed batch queueRows baselinePollToken generatedAt = false) ∧
    (gate = true →
      effectiveExecutionDirective batch queueRows baselinePollToken generatedAt =
        "execute_now") ∧
    (gate = false →
      effectiveExecutionDirective batch queueRows baselinePollToken generatedAt =
        "await_bridge_assignment") ∧
    (gate = true →
      effectiveRunnerEnvelope batch queueRows baselinePollToken generatedAt =
        (if pollChangedSince batch queueRows baselinePollToken generatedAt then
          runnerEnvelopeExecuteRefresh
        else
          runnerEnvelopeExecuteNoop)) ∧
    (gate = false →
      effectiveRunnerEnvelope batch queueRows baselinePollToken generatedAt =
        runnerEnvelopeAwaitBridge) ∧
    (gate = true →
      effectiveExecutionContractVersion = "heytingveil.execution.contract.v1") ∧
    (gate = false →
      effectiveExecutionContractVersion = "heytingveil.execution.contract.v1") ∧
    (gate = true →
      effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt =
        "v=heytingveil.execution.contract.v1|env=" ++
          (if pollChangedSince batch queueRows baselinePollToken generatedAt then
            runnerEnvelopeExecuteRefresh
          else
            runnerEnvelopeExecuteNoop)) ∧
    (gate = false →
      effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt =
        "v=heytingveil.execution.contract.v1|env=" ++ runnerEnvelopeAwaitBridge) ∧
    (gate = true →
      effectiveFetchHandoff batch queueRows baselinePollToken generatedAt =
        fetchHandoffDirective batch queueRows baselinePollToken generatedAt) ∧
    (gate = true →
      effectiveFetchTarget batch queueRows baselinePollToken generatedAt =
        fetchTarget batch queueRows baselinePollToken generatedAt) ∧
    (gate = false →
      effectiveFetchHandoff batch queueRows baselinePollToken generatedAt = false) ∧
    (gate = false →
      effectiveFetchTarget batch queueRows baselinePollToken generatedAt = "none") ∧
    (gate = true →
      effectiveNextStep batch queueRows baselinePollToken generatedAt =
        pollNextStep batch queueRows baselinePollToken generatedAt) ∧
    (gate = false →
      effectiveNextStep batch queueRows baselinePollToken generatedAt = "assign_bridge_hooks")
  )

theorem pollActionResponseEffectiveCoherent_true
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String) :
    pollActionResponseEffectiveCoherent batch queueRows baselinePollToken generatedAt = true := by
  by_cases hGate : bridgeGateAllowsExecution batch = true
  · have hStatus :
      effectiveStatus batch queueRows baselinePollToken generatedAt =
        (if pollChangedSince batch queueRows baselinePollToken generatedAt then
          "refresh_token_drift"
        else
          "noop_unchanged") :=
      effectiveStatus_gate_open batch queueRows baselinePollToken generatedAt hGate
    have hStatusClass :
        effectiveStatusClass batch queueRows baselinePollToken generatedAt =
          (if pollChangedSince batch queueRows baselinePollToken generatedAt then
            "executable_refresh"
          else
            "executable_noop") :=
      effectiveStatusClass_gate_open batch queueRows baselinePollToken generatedAt hGate
    have hExecutionAllowed :
        effectiveExecutionAllowed batch queueRows baselinePollToken generatedAt = true :=
      effectiveExecutionAllowed_gate_open batch queueRows baselinePollToken generatedAt hGate
    have hExecutionDirective :
        effectiveExecutionDirective batch queueRows baselinePollToken generatedAt =
          "execute_now" :=
      effectiveExecutionDirective_gate_open batch queueRows baselinePollToken generatedAt hGate
    have hRunnerEnvelope :
        effectiveRunnerEnvelope batch queueRows baselinePollToken generatedAt =
          (if pollChangedSince batch queueRows baselinePollToken generatedAt then
            runnerEnvelopeExecuteRefresh
          else
            runnerEnvelopeExecuteNoop) :=
      effectiveRunnerEnvelope_gate_open batch queueRows baselinePollToken generatedAt hGate
    have hContractHash :
        effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt =
          "v=heytingveil.execution.contract.v1|env=" ++
            (if pollChangedSince batch queueRows baselinePollToken generatedAt then
              runnerEnvelopeExecuteRefresh
            else
              runnerEnvelopeExecuteNoop) :=
      effectiveExecutionContractHash_gate_open batch queueRows baselinePollToken generatedAt hGate
    simp [
      pollActionResponseEffectiveCoherent,
      effectiveExecutionContractVersion,
      bridgeGateReason,
      effectiveAction,
      effectiveReason,
      hStatus,
      hStatusClass,
      hExecutionAllowed,
      hExecutionDirective,
      hRunnerEnvelope,
      hContractHash,
      effectiveFetchHandoff,
      effectiveFetchTarget,
      effectiveNextStep,
      hGate
    ]
  · have hGateFalse : bridgeGateAllowsExecution batch = false := by
      cases hBool : bridgeGateAllowsExecution batch <;> simp_all
    have hStatus :
        effectiveStatus batch queueRows baselinePollToken generatedAt =
          "blocked_bridge_assignment_required" :=
      effectiveStatus_gate_blocked batch queueRows baselinePollToken generatedAt hGateFalse
    have hStatusClass :
        effectiveStatusClass batch queueRows baselinePollToken generatedAt = "blocked" :=
      effectiveStatusClass_gate_blocked batch queueRows baselinePollToken generatedAt hGateFalse
    have hExecutionAllowed :
        effectiveExecutionAllowed batch queueRows baselinePollToken generatedAt = false :=
      effectiveExecutionAllowed_gate_blocked batch queueRows baselinePollToken generatedAt hGateFalse
    have hExecutionDirective :
        effectiveExecutionDirective batch queueRows baselinePollToken generatedAt =
          "await_bridge_assignment" :=
      effectiveExecutionDirective_gate_blocked batch queueRows baselinePollToken generatedAt hGateFalse
    have hRunnerEnvelope :
        effectiveRunnerEnvelope batch queueRows baselinePollToken generatedAt =
          runnerEnvelopeAwaitBridge :=
      effectiveRunnerEnvelope_gate_blocked batch queueRows baselinePollToken generatedAt hGateFalse
    have hContractHash :
        effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt =
          "v=heytingveil.execution.contract.v1|env=" ++ runnerEnvelopeAwaitBridge :=
      effectiveExecutionContractHash_gate_blocked batch queueRows baselinePollToken generatedAt hGateFalse
    simp [
      pollActionResponseEffectiveCoherent,
      effectiveExecutionContractVersion,
      bridgeGateReason,
      effectiveAction,
      effectiveReason,
      hStatus,
      hStatusClass,
      hExecutionAllowed,
      hExecutionDirective,
      hRunnerEnvelope,
      hContractHash,
      effectiveFetchHandoff,
      effectiveFetchTarget,
      effectiveNextStep,
      hGateFalse
    ]

def renderPollActionResponseEffectiveCoherenceSummary
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  "poll_action_response_effective_coherent=" ++
    toString (pollActionResponseEffectiveCoherent batch queueRows baselinePollToken generatedAt)

def renderEffectiveExecutionContractCoherenceSummary
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  "effective_execution_contract_coherent=" ++
    toString (effectiveExecutionContractCoherent batch queueRows baselinePollToken generatedAt)

def renderEffectiveExecutionContractJson
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  let version := effectiveExecutionContractVersion
  let hash := effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt
  let envelope := effectiveRunnerEnvelope batch queueRows baselinePollToken generatedAt
  let directive := effectiveExecutionDirective batch queueRows baselinePollToken generatedAt
  let status := effectiveStatus batch queueRows baselinePollToken generatedAt
  let statusClass := effectiveStatusClass batch queueRows baselinePollToken generatedAt
  let allowed := effectiveExecutionAllowed batch queueRows baselinePollToken generatedAt
  let coherent := effectiveExecutionContractCoherent batch queueRows baselinePollToken generatedAt
  String.intercalate ""
    [
      "{",
      "\"schema\":\"", escapeJsonField version, "\",",
      "\"generatedAt\":\"", escapeJsonField generatedAt, "\",",
      "\"baselinePollToken\":\"", escapeJsonField baselinePollToken, "\",",
      "\"effectiveExecutionContractVersion\":\"", escapeJsonField version, "\",",
      "\"effectiveExecutionContractHash\":\"", escapeJsonField hash, "\",",
      "\"effectiveRunnerEnvelope\":\"", escapeJsonField envelope, "\",",
      "\"effectiveExecutionDirective\":\"", escapeJsonField directive, "\",",
      "\"effectiveStatus\":\"", escapeJsonField status, "\",",
      "\"effectiveStatusClass\":\"", escapeJsonField statusClass, "\",",
      "\"effectiveExecutionAllowed\":", toString allowed, ",",
      "\"coherent\":", toString coherent, ",",
      "\"summary\":\"", escapeJsonField
        (renderEffectiveExecutionContractCoherenceSummary batch queueRows baselinePollToken generatedAt), "\"",
      "}"
    ]

def effectiveExecutionContractMatches
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (expectedVersion : String)
    (expectedHash : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : Bool :=
  decide (
    effectiveExecutionContractVersion = expectedVersion ∧
    effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt = expectedHash
  )

theorem effectiveExecutionContractMatches_actual_true
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String) :
    effectiveExecutionContractMatches
      batch queueRows baselinePollToken
      effectiveExecutionContractVersion
      (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
      generatedAt = true := by
  simp [effectiveExecutionContractMatches]

theorem effectiveExecutionContractHash_ne_bad_hash
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String) :
    effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt ≠ "bad-hash" := by
  intro h
  have hdata := congrArg String.data h
  simp [effectiveExecutionContractHash] at hdata

theorem effectiveExecutionContractMatches_bad_hash_false
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String) :
    effectiveExecutionContractMatches
      batch queueRows baselinePollToken
      effectiveExecutionContractVersion
      "bad-hash"
      generatedAt = false := by
  have hneq : effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt ≠ "bad-hash" :=
    effectiveExecutionContractHash_ne_bad_hash batch queueRows baselinePollToken generatedAt
  simp [effectiveExecutionContractMatches, hneq]

def renderEffectiveExecutionContractMatchSummary
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (expectedVersion : String)
    (expectedHash : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  let actualVersion := effectiveExecutionContractVersion
  let actualHash := effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt
  let isMatch := effectiveExecutionContractMatches
    batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  if isMatch then
    "effective_execution_contract_match=true"
  else
    String.intercalate "|"
      [
        "effective_execution_contract_match=false",
        "expected_version=" ++ expectedVersion,
        "actual_version=" ++ actualVersion,
        "expected_hash=" ++ expectedHash,
        "actual_hash=" ++ actualHash
      ]

def renderEffectiveExecutionContractMatchJson
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (expectedVersion : String)
    (expectedHash : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  let actualVersion := effectiveExecutionContractVersion
  let actualHash := effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt
  let isMatch := effectiveExecutionContractMatches
    batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  String.intercalate ""
    [
      "{",
      "\"schema\":\"heytingveil.execution.contract_match.v1\",",
      "\"generatedAt\":\"", escapeJsonField generatedAt, "\",",
      "\"baselinePollToken\":\"", escapeJsonField baselinePollToken, "\",",
      "\"expectedVersion\":\"", escapeJsonField expectedVersion, "\",",
      "\"actualVersion\":\"", escapeJsonField actualVersion, "\",",
      "\"expectedHash\":\"", escapeJsonField expectedHash, "\",",
      "\"actualHash\":\"", escapeJsonField actualHash, "\",",
      "\"matches\":", toString isMatch, ",",
      "\"summary\":\"", escapeJsonField
        (renderEffectiveExecutionContractMatchSummary
          batch queueRows baselinePollToken expectedVersion expectedHash generatedAt), "\"",
      "}"
    ]

def effectiveExecutionHandoffBundleDecision
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (expectedVersion : String)
    (expectedHash : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  let effectiveCoherent := pollActionResponseEffectiveCoherent batch queueRows baselinePollToken generatedAt
  let contractCoherent := effectiveExecutionContractCoherent batch queueRows baselinePollToken generatedAt
  let contractMatch := effectiveExecutionContractMatches
    batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  if !effectiveCoherent then
    "bundle_incoherent_poll_action"
  else if !contractCoherent then
    "bundle_incoherent_contract"
  else if contractMatch then
    "bundle_ready"
  else
    "bundle_contract_mismatch"

theorem effectiveExecutionHandoffBundleDecision_actual_ready
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String) :
    effectiveExecutionHandoffBundleDecision
      batch queueRows baselinePollToken
      effectiveExecutionContractVersion
      (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
      generatedAt = "bundle_ready" := by
  have heff :
      pollActionResponseEffectiveCoherent batch queueRows baselinePollToken generatedAt = true :=
    pollActionResponseEffectiveCoherent_true batch queueRows baselinePollToken generatedAt
  have hcoh :
      effectiveExecutionContractCoherent batch queueRows baselinePollToken generatedAt = true :=
    effectiveExecutionContractCoherent_true batch queueRows baselinePollToken generatedAt
  have hmatch :
      effectiveExecutionContractMatches
          batch queueRows baselinePollToken
          effectiveExecutionContractVersion
          (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
          generatedAt = true :=
    effectiveExecutionContractMatches_actual_true batch queueRows baselinePollToken generatedAt
  simp [effectiveExecutionHandoffBundleDecision, heff, hcoh, hmatch]

theorem effectiveExecutionHandoffBundleDecision_bad_hash_mismatch
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String) :
    effectiveExecutionHandoffBundleDecision
      batch queueRows baselinePollToken
      effectiveExecutionContractVersion
      "bad-hash"
      generatedAt = "bundle_contract_mismatch" := by
  have heff :
      pollActionResponseEffectiveCoherent batch queueRows baselinePollToken generatedAt = true :=
    pollActionResponseEffectiveCoherent_true batch queueRows baselinePollToken generatedAt
  have hcoh :
      effectiveExecutionContractCoherent batch queueRows baselinePollToken generatedAt = true :=
    effectiveExecutionContractCoherent_true batch queueRows baselinePollToken generatedAt
  have hmatch :
      effectiveExecutionContractMatches
          batch queueRows baselinePollToken
          effectiveExecutionContractVersion
          "bad-hash"
          generatedAt = false :=
    effectiveExecutionContractMatches_bad_hash_false batch queueRows baselinePollToken generatedAt
  simp [effectiveExecutionHandoffBundleDecision, heff, hcoh, hmatch]

def effectiveExecutionHandoffBundleDecisionCode
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (expectedVersion : String)
    (expectedHash : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : Nat :=
  let decision := effectiveExecutionHandoffBundleDecision
    batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  if decision = "bundle_ready" then
    1
  else if decision = "bundle_contract_mismatch" then
    2
  else if decision = "bundle_incoherent_poll_action" then
    3
  else if decision = "bundle_incoherent_contract" then
    4
  else
    0

theorem effectiveExecutionHandoffBundleDecisionCode_actual_ready
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String) :
    effectiveExecutionHandoffBundleDecisionCode
      batch queueRows baselinePollToken
      effectiveExecutionContractVersion
      (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
      generatedAt = 1 := by
  have hready :
      effectiveExecutionHandoffBundleDecision
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
        generatedAt = "bundle_ready" :=
    effectiveExecutionHandoffBundleDecision_actual_ready
      batch queueRows baselinePollToken generatedAt
  simp [effectiveExecutionHandoffBundleDecisionCode, hready]

theorem effectiveExecutionHandoffBundleDecisionCode_bad_hash_mismatch
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String) :
    effectiveExecutionHandoffBundleDecisionCode
      batch queueRows baselinePollToken
      effectiveExecutionContractVersion
      "bad-hash"
      generatedAt = 2 := by
  have hdecision :
      effectiveExecutionHandoffBundleDecision
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        "bad-hash"
        generatedAt = "bundle_contract_mismatch" :=
    effectiveExecutionHandoffBundleDecision_bad_hash_mismatch batch queueRows baselinePollToken generatedAt
  simp [effectiveExecutionHandoffBundleDecisionCode, hdecision]

def effectiveExecutionHandoffDispatchMode
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (expectedVersion : String)
    (expectedHash : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  let decision := effectiveExecutionHandoffBundleDecision
    batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  if decision = "bundle_ready" then
    "dispatch_execute"
  else if decision = "bundle_contract_mismatch" then
    "dispatch_refresh_contract"
  else if decision = "bundle_incoherent_poll_action" then
    "dispatch_poll_reconcile"
  else if decision = "bundle_incoherent_contract" then
    "dispatch_contract_reconcile"
  else
    "dispatch_hold"

theorem effectiveExecutionHandoffDispatchMode_actual_execute
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String) :
    effectiveExecutionHandoffDispatchMode
      batch queueRows baselinePollToken
      effectiveExecutionContractVersion
      (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
      generatedAt = "dispatch_execute" := by
  have hready :
      effectiveExecutionHandoffBundleDecision
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
        generatedAt = "bundle_ready" :=
    effectiveExecutionHandoffBundleDecision_actual_ready
      batch queueRows baselinePollToken generatedAt
  simp [effectiveExecutionHandoffDispatchMode, hready]

theorem effectiveExecutionHandoffDispatchMode_bad_hash_refresh
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String) :
    effectiveExecutionHandoffDispatchMode
      batch queueRows baselinePollToken
      effectiveExecutionContractVersion
      "bad-hash"
      generatedAt = "dispatch_refresh_contract" := by
  have hdecision :
      effectiveExecutionHandoffBundleDecision
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        "bad-hash"
        generatedAt = "bundle_contract_mismatch" :=
    effectiveExecutionHandoffBundleDecision_bad_hash_mismatch batch queueRows baselinePollToken generatedAt
  simp [effectiveExecutionHandoffDispatchMode, hdecision]

def effectiveExecutionHandoffDispatchModeCode
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (expectedVersion : String)
    (expectedHash : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : Nat :=
  let dispatchMode := effectiveExecutionHandoffDispatchMode
    batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  if dispatchMode = "dispatch_execute" then
    1
  else if dispatchMode = "dispatch_refresh_contract" then
    2
  else if dispatchMode = "dispatch_poll_reconcile" then
    3
  else if dispatchMode = "dispatch_contract_reconcile" then
    4
  else
    0

theorem effectiveExecutionHandoffDispatchModeCode_actual_execute
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String) :
    effectiveExecutionHandoffDispatchModeCode
      batch queueRows baselinePollToken
      effectiveExecutionContractVersion
      (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
      generatedAt = 1 := by
  have hdispatch :
      effectiveExecutionHandoffDispatchMode
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
        generatedAt = "dispatch_execute" :=
    effectiveExecutionHandoffDispatchMode_actual_execute
      batch queueRows baselinePollToken generatedAt
  simp [effectiveExecutionHandoffDispatchModeCode, hdispatch]

theorem effectiveExecutionHandoffDispatchModeCode_bad_hash_refresh
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String) :
    effectiveExecutionHandoffDispatchModeCode
      batch queueRows baselinePollToken
      effectiveExecutionContractVersion
      "bad-hash"
      generatedAt = 2 := by
  have hdispatch :
      effectiveExecutionHandoffDispatchMode
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        "bad-hash"
        generatedAt = "dispatch_refresh_contract" :=
    effectiveExecutionHandoffDispatchMode_bad_hash_refresh batch queueRows baselinePollToken generatedAt
  simp [effectiveExecutionHandoffDispatchModeCode, hdispatch]

def effectiveExecutionHandoffBundleAction
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (expectedVersion : String)
    (expectedHash : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  let decision := effectiveExecutionHandoffBundleDecision
    batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  let dispatchMode := effectiveExecutionHandoffDispatchMode
    batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  if decision = "bundle_ready" && dispatchMode = "dispatch_execute" then
    "action_execute_now"
  else if decision = "bundle_contract_mismatch" && dispatchMode = "dispatch_refresh_contract" then
    "action_refresh_contract"
  else if decision = "bundle_incoherent_poll_action" && dispatchMode = "dispatch_poll_reconcile" then
    "action_reconcile_poll"
  else if decision = "bundle_incoherent_contract" && dispatchMode = "dispatch_contract_reconcile" then
    "action_reconcile_contract"
  else
    "action_hold"

theorem effectiveExecutionHandoffBundleAction_actual_execute
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String) :
    effectiveExecutionHandoffBundleAction
      batch queueRows baselinePollToken
      effectiveExecutionContractVersion
      (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
      generatedAt = "action_execute_now" := by
  have hready :
      effectiveExecutionHandoffBundleDecision
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
        generatedAt = "bundle_ready" :=
    effectiveExecutionHandoffBundleDecision_actual_ready
      batch queueRows baselinePollToken generatedAt
  have hdispatch :
      effectiveExecutionHandoffDispatchMode
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
        generatedAt = "dispatch_execute" :=
    effectiveExecutionHandoffDispatchMode_actual_execute
      batch queueRows baselinePollToken generatedAt
  simp [effectiveExecutionHandoffBundleAction, hready, hdispatch]

theorem effectiveExecutionHandoffBundleAction_bad_hash_refresh
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String) :
    effectiveExecutionHandoffBundleAction
      batch queueRows baselinePollToken
      effectiveExecutionContractVersion
      "bad-hash"
      generatedAt = "action_refresh_contract" := by
  have hdecision :
      effectiveExecutionHandoffBundleDecision
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        "bad-hash"
        generatedAt = "bundle_contract_mismatch" :=
    effectiveExecutionHandoffBundleDecision_bad_hash_mismatch batch queueRows baselinePollToken generatedAt
  have hdispatch :
      effectiveExecutionHandoffDispatchMode
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        "bad-hash"
        generatedAt = "dispatch_refresh_contract" :=
    effectiveExecutionHandoffDispatchMode_bad_hash_refresh batch queueRows baselinePollToken generatedAt
  simp [effectiveExecutionHandoffBundleAction, hdecision, hdispatch]

def effectiveExecutionHandoffBundleActionCode
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (expectedVersion : String)
    (expectedHash : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : Nat :=
  let action := effectiveExecutionHandoffBundleAction
    batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  if action = "action_execute_now" then
    1
  else if action = "action_refresh_contract" then
    2
  else if action = "action_reconcile_poll" then
    3
  else if action = "action_reconcile_contract" then
    4
  else
    0

theorem effectiveExecutionHandoffBundleActionCode_actual_execute
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String) :
    effectiveExecutionHandoffBundleActionCode
      batch queueRows baselinePollToken
      effectiveExecutionContractVersion
      (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
      generatedAt = 1 := by
  have haction :
      effectiveExecutionHandoffBundleAction
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
        generatedAt = "action_execute_now" :=
    effectiveExecutionHandoffBundleAction_actual_execute
      batch queueRows baselinePollToken generatedAt
  simp [effectiveExecutionHandoffBundleActionCode, haction]

theorem effectiveExecutionHandoffBundleActionCode_bad_hash_refresh
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String) :
    effectiveExecutionHandoffBundleActionCode
      batch queueRows baselinePollToken
      effectiveExecutionContractVersion
      "bad-hash"
      generatedAt = 2 := by
  have haction :
      effectiveExecutionHandoffBundleAction
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        "bad-hash"
        generatedAt = "action_refresh_contract" :=
    effectiveExecutionHandoffBundleAction_bad_hash_refresh batch queueRows baselinePollToken generatedAt
  simp [effectiveExecutionHandoffBundleActionCode, haction]

def effectiveExecutionHandoffBundleRoutingFingerprint
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (expectedVersion : String)
    (expectedHash : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  let decisionCode := effectiveExecutionHandoffBundleDecisionCode
    batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  let dispatchModeCode := effectiveExecutionHandoffDispatchModeCode
    batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  let actionCode := effectiveExecutionHandoffBundleActionCode
    batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  "bundle_routing_fingerprint_v1|decision=" ++ toString decisionCode ++
    "|dispatch=" ++ toString dispatchModeCode ++
    "|action=" ++ toString actionCode

theorem effectiveExecutionHandoffBundleRoutingFingerprint_actual_execute
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String) :
    effectiveExecutionHandoffBundleRoutingFingerprint
      batch queueRows baselinePollToken
      effectiveExecutionContractVersion
      (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
      generatedAt = "bundle_routing_fingerprint_v1|decision=1|dispatch=1|action=1" := by
  have hdecision :
      effectiveExecutionHandoffBundleDecisionCode
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
        generatedAt = 1 :=
    effectiveExecutionHandoffBundleDecisionCode_actual_ready
      batch queueRows baselinePollToken generatedAt
  have hdispatch :
      effectiveExecutionHandoffDispatchModeCode
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
        generatedAt = 1 :=
    effectiveExecutionHandoffDispatchModeCode_actual_execute
      batch queueRows baselinePollToken generatedAt
  have haction :
      effectiveExecutionHandoffBundleActionCode
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
        generatedAt = 1 :=
    effectiveExecutionHandoffBundleActionCode_actual_execute
      batch queueRows baselinePollToken generatedAt
  have hnorm :
      "bundle_routing_fingerprint_v1|decision=" ++ toString 1 ++ "|dispatch=" ++ toString 1 ++
          "|action=" ++ toString 1 =
        "bundle_routing_fingerprint_v1|decision=1|dispatch=1|action=1" := by
    native_decide
  simpa [effectiveExecutionHandoffBundleRoutingFingerprint, hdecision, hdispatch, haction] using hnorm

theorem effectiveExecutionHandoffBundleRoutingFingerprint_bad_hash
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String) :
    effectiveExecutionHandoffBundleRoutingFingerprint
      batch queueRows baselinePollToken
      effectiveExecutionContractVersion
      "bad-hash"
      generatedAt = "bundle_routing_fingerprint_v1|decision=2|dispatch=2|action=2" := by
  have hdecision :
      effectiveExecutionHandoffBundleDecisionCode
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        "bad-hash"
        generatedAt = 2 :=
    effectiveExecutionHandoffBundleDecisionCode_bad_hash_mismatch batch queueRows baselinePollToken generatedAt
  have hdispatch :
      effectiveExecutionHandoffDispatchModeCode
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        "bad-hash"
        generatedAt = 2 :=
    effectiveExecutionHandoffDispatchModeCode_bad_hash_refresh batch queueRows baselinePollToken generatedAt
  have haction :
      effectiveExecutionHandoffBundleActionCode
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        "bad-hash"
        generatedAt = 2 :=
    effectiveExecutionHandoffBundleActionCode_bad_hash_refresh batch queueRows baselinePollToken generatedAt
  have hnorm :
      "bundle_routing_fingerprint_v1|decision=" ++ toString 2 ++ "|dispatch=" ++ toString 2 ++
          "|action=" ++ toString 2 =
        "bundle_routing_fingerprint_v1|decision=2|dispatch=2|action=2" := by
    native_decide
  simpa [effectiveExecutionHandoffBundleRoutingFingerprint, hdecision, hdispatch, haction] using hnorm

def effectiveExecutionHandoffBundleRoutingKey
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (expectedVersion : String)
    (expectedHash : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : Nat :=
  let decisionCode := effectiveExecutionHandoffBundleDecisionCode
    batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  let dispatchModeCode := effectiveExecutionHandoffDispatchModeCode
    batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  let actionCode := effectiveExecutionHandoffBundleActionCode
    batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  decisionCode * 100 + dispatchModeCode * 10 + actionCode

theorem effectiveExecutionHandoffBundleRoutingKey_actual_execute
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String) :
    effectiveExecutionHandoffBundleRoutingKey
      batch queueRows baselinePollToken
      effectiveExecutionContractVersion
      (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
      generatedAt = 111 := by
  have hdecision :
      effectiveExecutionHandoffBundleDecisionCode
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
        generatedAt = 1 :=
    effectiveExecutionHandoffBundleDecisionCode_actual_ready
      batch queueRows baselinePollToken generatedAt
  have hdispatch :
      effectiveExecutionHandoffDispatchModeCode
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
        generatedAt = 1 :=
    effectiveExecutionHandoffDispatchModeCode_actual_execute
      batch queueRows baselinePollToken generatedAt
  have haction :
      effectiveExecutionHandoffBundleActionCode
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
        generatedAt = 1 :=
    effectiveExecutionHandoffBundleActionCode_actual_execute
      batch queueRows baselinePollToken generatedAt
  simp [effectiveExecutionHandoffBundleRoutingKey, hdecision, hdispatch, haction]

theorem effectiveExecutionHandoffBundleRoutingKey_bad_hash
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String) :
    effectiveExecutionHandoffBundleRoutingKey
      batch queueRows baselinePollToken
      effectiveExecutionContractVersion
      "bad-hash"
      generatedAt = 222 := by
  have hdecision :
      effectiveExecutionHandoffBundleDecisionCode
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        "bad-hash"
        generatedAt = 2 :=
    effectiveExecutionHandoffBundleDecisionCode_bad_hash_mismatch batch queueRows baselinePollToken generatedAt
  have hdispatch :
      effectiveExecutionHandoffDispatchModeCode
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        "bad-hash"
        generatedAt = 2 :=
    effectiveExecutionHandoffDispatchModeCode_bad_hash_refresh batch queueRows baselinePollToken generatedAt
  have haction :
      effectiveExecutionHandoffBundleActionCode
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        "bad-hash"
        generatedAt = 2 :=
    effectiveExecutionHandoffBundleActionCode_bad_hash_refresh batch queueRows baselinePollToken generatedAt
  simp [effectiveExecutionHandoffBundleRoutingKey, hdecision, hdispatch, haction]

structure BundleRoutingCodes where
  decisionCode : Nat
  dispatchModeCode : Nat
  actionCode : Nat
deriving DecidableEq, Repr

def decodeBundleRoutingKey (key : Nat) : BundleRoutingCodes :=
  let decisionCode := key / 100
  let rem := key % 100
  let dispatchModeCode := rem / 10
  let actionCode := rem % 10
  { decisionCode := decisionCode, dispatchModeCode := dispatchModeCode, actionCode := actionCode }

def encodeBundleRoutingCodes (codes : BundleRoutingCodes) : Nat :=
  codes.decisionCode * 100 + codes.dispatchModeCode * 10 + codes.actionCode

theorem decodeBundleRoutingKey_111 :
    decodeBundleRoutingKey 111 = { decisionCode := 1, dispatchModeCode := 1, actionCode := 1 } := by
  native_decide

theorem encode_decodeBundleRoutingKey_111 :
    encodeBundleRoutingCodes (decodeBundleRoutingKey 111) = 111 := by
  native_decide

theorem encode_decodeBundleRoutingKey_222 :
    encodeBundleRoutingCodes (decodeBundleRoutingKey 222) = 222 := by
  native_decide

def bundleRoutingKeyRoundTripCoherent (key : Nat) : Bool :=
  encodeBundleRoutingCodes (decodeBundleRoutingKey key) = key

theorem bundleRoutingKeyRoundTripCoherent_111_true :
    bundleRoutingKeyRoundTripCoherent 111 = true := by
  native_decide

theorem bundleRoutingKeyRoundTripCoherent_222_true :
    bundleRoutingKeyRoundTripCoherent 222 = true := by
  native_decide

def renderBundleRoutingCodesSummary (codes : BundleRoutingCodes) : String :=
  String.intercalate "|"
    [
      "decision=" ++ toString codes.decisionCode,
      "dispatch=" ++ toString codes.dispatchModeCode,
      "action=" ++ toString codes.actionCode
    ]

def effectiveExecutionHandoffDecodedRoutingCodes
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (expectedVersion : String)
    (expectedHash : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : BundleRoutingCodes :=
  decodeBundleRoutingKey
    (effectiveExecutionHandoffBundleRoutingKey
      batch queueRows baselinePollToken expectedVersion expectedHash generatedAt)

def effectiveExecutionHandoffDecodedRoutingCodesSummary
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (expectedVersion : String)
    (expectedHash : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  renderBundleRoutingCodesSummary
    (effectiveExecutionHandoffDecodedRoutingCodes
      batch queueRows baselinePollToken expectedVersion expectedHash generatedAt)

def effectiveExecutionHandoffBundleRoutingRoundTripCoherent
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (expectedVersion : String)
    (expectedHash : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : Bool :=
  bundleRoutingKeyRoundTripCoherent
    (effectiveExecutionHandoffBundleRoutingKey
      batch queueRows baselinePollToken expectedVersion expectedHash generatedAt)

def effectiveExecutionHandoffRoutingDiagnosticsConsistent
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (expectedVersion : String)
    (expectedHash : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : Bool :=
  let decisionCode := effectiveExecutionHandoffBundleDecisionCode
    batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  let dispatchModeCode := effectiveExecutionHandoffDispatchModeCode
    batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  let actionCode := effectiveExecutionHandoffBundleActionCode
    batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  let fingerprint := effectiveExecutionHandoffBundleRoutingFingerprint
    batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  let key := effectiveExecutionHandoffBundleRoutingKey
    batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  let decoded := decodeBundleRoutingKey key
  let expectedFingerprint :=
    "bundle_routing_fingerprint_v1|decision=" ++ toString decisionCode ++
      "|dispatch=" ++ toString dispatchModeCode ++
      "|action=" ++ toString actionCode
  (fingerprint = expectedFingerprint) &&
    (key = decisionCode * 100 + dispatchModeCode * 10 + actionCode) &&
    (decoded.decisionCode = decisionCode) &&
    (decoded.dispatchModeCode = dispatchModeCode) &&
    (decoded.actionCode = actionCode) &&
    (bundleRoutingKeyRoundTripCoherent key)

theorem effectiveExecutionHandoffRoutingDiagnosticsConsistent_actual_true
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String) :
    effectiveExecutionHandoffRoutingDiagnosticsConsistent
      batch queueRows baselinePollToken
      effectiveExecutionContractVersion
      (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
      generatedAt = true := by
  have hdecision :
      effectiveExecutionHandoffBundleDecisionCode
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
        generatedAt = 1 :=
    effectiveExecutionHandoffBundleDecisionCode_actual_ready batch queueRows baselinePollToken generatedAt
  have hdispatch :
      effectiveExecutionHandoffDispatchModeCode
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
        generatedAt = 1 :=
    effectiveExecutionHandoffDispatchModeCode_actual_execute batch queueRows baselinePollToken generatedAt
  have haction :
      effectiveExecutionHandoffBundleActionCode
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
        generatedAt = 1 :=
    effectiveExecutionHandoffBundleActionCode_actual_execute batch queueRows baselinePollToken generatedAt
  have hfingerprint :
      effectiveExecutionHandoffBundleRoutingFingerprint
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
        generatedAt = "bundle_routing_fingerprint_v1|decision=1|dispatch=1|action=1" :=
    effectiveExecutionHandoffBundleRoutingFingerprint_actual_execute batch queueRows baselinePollToken generatedAt
  have hkey :
      effectiveExecutionHandoffBundleRoutingKey
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
        generatedAt = 111 :=
    effectiveExecutionHandoffBundleRoutingKey_actual_execute batch queueRows baselinePollToken generatedAt
  have hnormStr :
      "bundle_routing_fingerprint_v1|decision=1|dispatch=1|action=1" =
        "bundle_routing_fingerprint_v1|decision=" ++ toString 1 ++
          "|dispatch=" ++ toString 1 ++
          "|action=" ++ toString 1 := by
    native_decide
  have hdecDecision : (decodeBundleRoutingKey 111).decisionCode = 1 := by
    native_decide
  have hdecDispatch : (decodeBundleRoutingKey 111).dispatchModeCode = 1 := by
    native_decide
  have hdecAction : (decodeBundleRoutingKey 111).actionCode = 1 := by
    native_decide
  have hround111 : bundleRoutingKeyRoundTripCoherent 111 = true := by
    simpa using bundleRoutingKeyRoundTripCoherent_111_true
  simp [
    effectiveExecutionHandoffRoutingDiagnosticsConsistent,
    hdecision,
    hdispatch,
    haction,
    hfingerprint,
    hkey,
    hnormStr,
    hdecDecision,
    hdecDispatch,
    hdecAction,
    hround111
  ]

theorem effectiveExecutionHandoffRoutingDiagnosticsConsistent_bad_hash_true
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String) :
    effectiveExecutionHandoffRoutingDiagnosticsConsistent
      batch queueRows baselinePollToken
      effectiveExecutionContractVersion
      "bad-hash"
      generatedAt = true := by
  have hdecision :
      effectiveExecutionHandoffBundleDecisionCode
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        "bad-hash"
        generatedAt = 2 :=
    effectiveExecutionHandoffBundleDecisionCode_bad_hash_mismatch batch queueRows baselinePollToken generatedAt
  have hdispatch :
      effectiveExecutionHandoffDispatchModeCode
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        "bad-hash"
        generatedAt = 2 :=
    effectiveExecutionHandoffDispatchModeCode_bad_hash_refresh batch queueRows baselinePollToken generatedAt
  have haction :
      effectiveExecutionHandoffBundleActionCode
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        "bad-hash"
        generatedAt = 2 :=
    effectiveExecutionHandoffBundleActionCode_bad_hash_refresh batch queueRows baselinePollToken generatedAt
  have hfingerprint :
      effectiveExecutionHandoffBundleRoutingFingerprint
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        "bad-hash"
        generatedAt = "bundle_routing_fingerprint_v1|decision=2|dispatch=2|action=2" :=
    effectiveExecutionHandoffBundleRoutingFingerprint_bad_hash batch queueRows baselinePollToken generatedAt
  have hkey :
      effectiveExecutionHandoffBundleRoutingKey
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        "bad-hash"
        generatedAt = 222 :=
    effectiveExecutionHandoffBundleRoutingKey_bad_hash batch queueRows baselinePollToken generatedAt
  have hnormStr :
      "bundle_routing_fingerprint_v1|decision=2|dispatch=2|action=2" =
        "bundle_routing_fingerprint_v1|decision=" ++ toString 2 ++
          "|dispatch=" ++ toString 2 ++
          "|action=" ++ toString 2 := by
    native_decide
  have hdecDecision : (decodeBundleRoutingKey 222).decisionCode = 2 := by
    native_decide
  have hdecDispatch : (decodeBundleRoutingKey 222).dispatchModeCode = 2 := by
    native_decide
  have hdecAction : (decodeBundleRoutingKey 222).actionCode = 2 := by
    native_decide
  have hround222 : bundleRoutingKeyRoundTripCoherent 222 = true := by
    simpa using bundleRoutingKeyRoundTripCoherent_222_true
  simp [
    effectiveExecutionHandoffRoutingDiagnosticsConsistent,
    hdecision,
    hdispatch,
    haction,
    hfingerprint,
    hkey,
    hnormStr,
    hdecDecision,
    hdecDispatch,
    hdecAction,
    hround222
  ]

def renderEffectiveExecutionHandoffRoutingDiagnosticsSummary
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (expectedVersion : String)
    (expectedHash : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  let consistent := effectiveExecutionHandoffRoutingDiagnosticsConsistent
    batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  let decisionCode := effectiveExecutionHandoffBundleDecisionCode
    batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  let dispatchModeCode := effectiveExecutionHandoffDispatchModeCode
    batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  let actionCode := effectiveExecutionHandoffBundleActionCode
    batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  let key := effectiveExecutionHandoffBundleRoutingKey
    batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  if consistent then
    "routing_diagnostics_consistent=true"
  else
    String.intercalate "|"
      [
        "routing_diagnostics_consistent=false",
        "decision_code=" ++ toString decisionCode,
        "dispatch_mode_code=" ++ toString dispatchModeCode,
        "action_code=" ++ toString actionCode,
        "routing_key=" ++ toString key
      ]

theorem renderEffectiveExecutionHandoffRoutingDiagnosticsSummary_actual_true
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String) :
    renderEffectiveExecutionHandoffRoutingDiagnosticsSummary
      batch queueRows baselinePollToken
      effectiveExecutionContractVersion
      (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
      generatedAt = "routing_diagnostics_consistent=true" := by
  have hconsistent :
      effectiveExecutionHandoffRoutingDiagnosticsConsistent
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
        generatedAt = true :=
    effectiveExecutionHandoffRoutingDiagnosticsConsistent_actual_true
      batch queueRows baselinePollToken generatedAt
  simp [renderEffectiveExecutionHandoffRoutingDiagnosticsSummary, hconsistent]

theorem renderEffectiveExecutionHandoffRoutingDiagnosticsSummary_bad_hash_true
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String) :
    renderEffectiveExecutionHandoffRoutingDiagnosticsSummary
      batch queueRows baselinePollToken
      effectiveExecutionContractVersion
      "bad-hash"
      generatedAt = "routing_diagnostics_consistent=true" := by
  have hconsistent :
      effectiveExecutionHandoffRoutingDiagnosticsConsistent
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        "bad-hash"
        generatedAt = true :=
    effectiveExecutionHandoffRoutingDiagnosticsConsistent_bad_hash_true
      batch queueRows baselinePollToken generatedAt
  simp [renderEffectiveExecutionHandoffRoutingDiagnosticsSummary, hconsistent]

def renderEffectiveExecutionHandoffRoutingDiagnosticsMarker
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (expectedVersion : String)
    (expectedHash : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  "routing_diagnostics_consistent=" ++
    toString
      (effectiveExecutionHandoffRoutingDiagnosticsConsistent
        batch queueRows baselinePollToken expectedVersion expectedHash generatedAt)

theorem renderEffectiveExecutionHandoffRoutingDiagnosticsMarker_actual_true
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String) :
    renderEffectiveExecutionHandoffRoutingDiagnosticsMarker
      batch queueRows baselinePollToken
      effectiveExecutionContractVersion
      (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
      generatedAt = "routing_diagnostics_consistent=true" := by
  have hconsistent :
      effectiveExecutionHandoffRoutingDiagnosticsConsistent
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
        generatedAt = true :=
    effectiveExecutionHandoffRoutingDiagnosticsConsistent_actual_true
      batch queueRows baselinePollToken generatedAt
  have hnorm :
      "routing_diagnostics_consistent=" ++ toString true = "routing_diagnostics_consistent=true" := by
    native_decide
  simp [renderEffectiveExecutionHandoffRoutingDiagnosticsMarker, hconsistent, hnorm]

theorem renderEffectiveExecutionHandoffRoutingDiagnosticsMarker_bad_hash_true
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String) :
    renderEffectiveExecutionHandoffRoutingDiagnosticsMarker
      batch queueRows baselinePollToken
      effectiveExecutionContractVersion
      "bad-hash"
      generatedAt = "routing_diagnostics_consistent=true" := by
  have hconsistent :
      effectiveExecutionHandoffRoutingDiagnosticsConsistent
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        "bad-hash"
        generatedAt = true :=
    effectiveExecutionHandoffRoutingDiagnosticsConsistent_bad_hash_true
      batch queueRows baselinePollToken generatedAt
  have hnorm :
      "routing_diagnostics_consistent=" ++ toString true = "routing_diagnostics_consistent=true" := by
    native_decide
  simp [renderEffectiveExecutionHandoffRoutingDiagnosticsMarker, hconsistent, hnorm]

def renderEffectiveExecutionHandoffRoutingDiagnosticsJsonFields
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (expectedVersion : String)
    (expectedHash : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  let consistent := effectiveExecutionHandoffRoutingDiagnosticsConsistent
    batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  let summary := renderEffectiveExecutionHandoffRoutingDiagnosticsSummary
    batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  String.intercalate ""
    [
      "\"routingDiagnosticsConsistent\":", toString consistent, ",",
      "\"routingDiagnosticsSummary\":\"", escapeJsonField summary, "\","
    ]

theorem renderEffectiveExecutionHandoffRoutingDiagnosticsJsonFields_actual
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String) :
    renderEffectiveExecutionHandoffRoutingDiagnosticsJsonFields
      batch queueRows baselinePollToken
      effectiveExecutionContractVersion
      (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
      generatedAt =
      "\"routingDiagnosticsConsistent\":true,\"routingDiagnosticsSummary\":\"routing_diagnostics_consistent=true\"," := by
  have hconsistent :
      effectiveExecutionHandoffRoutingDiagnosticsConsistent
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
        generatedAt = true :=
    effectiveExecutionHandoffRoutingDiagnosticsConsistent_actual_true
      batch queueRows baselinePollToken generatedAt
  have hsummary :
      renderEffectiveExecutionHandoffRoutingDiagnosticsSummary
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
        generatedAt = "routing_diagnostics_consistent=true" :=
    renderEffectiveExecutionHandoffRoutingDiagnosticsSummary_actual_true
      batch queueRows baselinePollToken generatedAt
  have hnorm :
      String.intercalate ""
          [
            "\"routingDiagnosticsConsistent\":", toString true, ",",
            "\"routingDiagnosticsSummary\":\"",
            escapeJsonField "routing_diagnostics_consistent=true", "\","
          ] =
        "\"routingDiagnosticsConsistent\":true,\"routingDiagnosticsSummary\":\"routing_diagnostics_consistent=true\"," := by
    native_decide
  simpa [renderEffectiveExecutionHandoffRoutingDiagnosticsJsonFields, hconsistent, hsummary] using hnorm

theorem renderEffectiveExecutionHandoffRoutingDiagnosticsJsonFields_bad_hash
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String) :
    renderEffectiveExecutionHandoffRoutingDiagnosticsJsonFields
      batch queueRows baselinePollToken
      effectiveExecutionContractVersion
      "bad-hash"
      generatedAt =
      "\"routingDiagnosticsConsistent\":true,\"routingDiagnosticsSummary\":\"routing_diagnostics_consistent=true\"," := by
  have hconsistent :
      effectiveExecutionHandoffRoutingDiagnosticsConsistent
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        "bad-hash"
        generatedAt = true :=
    effectiveExecutionHandoffRoutingDiagnosticsConsistent_bad_hash_true
      batch queueRows baselinePollToken generatedAt
  have hsummary :
      renderEffectiveExecutionHandoffRoutingDiagnosticsSummary
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        "bad-hash"
        generatedAt = "routing_diagnostics_consistent=true" :=
    renderEffectiveExecutionHandoffRoutingDiagnosticsSummary_bad_hash_true
      batch queueRows baselinePollToken generatedAt
  have hnorm :
      String.intercalate ""
          [
            "\"routingDiagnosticsConsistent\":", toString true, ",",
            "\"routingDiagnosticsSummary\":\"",
            escapeJsonField "routing_diagnostics_consistent=true", "\","
          ] =
        "\"routingDiagnosticsConsistent\":true,\"routingDiagnosticsSummary\":\"routing_diagnostics_consistent=true\"," := by
    native_decide
  simpa [renderEffectiveExecutionHandoffRoutingDiagnosticsJsonFields, hconsistent, hsummary] using hnorm

def renderEffectiveExecutionHandoffBundleJsonRoutingEnvelope
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (expectedVersion : String)
    (expectedHash : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  let bundleRoutingKey := effectiveExecutionHandoffBundleRoutingKey
    batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  let decodedRoutingCodes := decodeBundleRoutingKey bundleRoutingKey
  let decodedRoutingCodesSummary := renderBundleRoutingCodesSummary decodedRoutingCodes
  let bundleRoutingRoundTripCoherent := bundleRoutingKeyRoundTripCoherent bundleRoutingKey
  String.intercalate ""
    [
      "\"bundleRoutingRoundTripCoherent\":", toString bundleRoutingRoundTripCoherent, ",",
      renderEffectiveExecutionHandoffRoutingDiagnosticsJsonFields
        batch queueRows baselinePollToken expectedVersion expectedHash generatedAt,
      "\"bundleRoutingCodes\":{",
      "\"decisionCode\":", toString decodedRoutingCodes.decisionCode, ",",
      "\"dispatchModeCode\":", toString decodedRoutingCodes.dispatchModeCode, ",",
      "\"actionCode\":", toString decodedRoutingCodes.actionCode,
      "},",
      "\"bundleRoutingCodesSummary\":\"", escapeJsonField decodedRoutingCodesSummary, "\","
    ]

theorem renderEffectiveExecutionHandoffBundleJsonRoutingEnvelope_actual
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String) :
    renderEffectiveExecutionHandoffBundleJsonRoutingEnvelope
      batch queueRows baselinePollToken
      effectiveExecutionContractVersion
      (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
      generatedAt =
      "\"bundleRoutingRoundTripCoherent\":true,\"routingDiagnosticsConsistent\":true,\"routingDiagnosticsSummary\":\"routing_diagnostics_consistent=true\",\"bundleRoutingCodes\":{\"decisionCode\":1,\"dispatchModeCode\":1,\"actionCode\":1},\"bundleRoutingCodesSummary\":\"decision=1|dispatch=1|action=1\"," := by
  have hkey :
      effectiveExecutionHandoffBundleRoutingKey
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
        generatedAt = 111 :=
    effectiveExecutionHandoffBundleRoutingKey_actual_execute batch queueRows baselinePollToken generatedAt
  have hround :
      bundleRoutingKeyRoundTripCoherent
        (effectiveExecutionHandoffBundleRoutingKey
          batch queueRows baselinePollToken
          effectiveExecutionContractVersion
          (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
          generatedAt) = true := by
    simpa [hkey] using bundleRoutingKeyRoundTripCoherent_111_true
  have hfields :
      renderEffectiveExecutionHandoffRoutingDiagnosticsJsonFields
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
        generatedAt =
        "\"routingDiagnosticsConsistent\":true,\"routingDiagnosticsSummary\":\"routing_diagnostics_consistent=true\"," :=
    renderEffectiveExecutionHandoffRoutingDiagnosticsJsonFields_actual
      batch queueRows baselinePollToken generatedAt
  have hsummary :
      renderBundleRoutingCodesSummary
        (decodeBundleRoutingKey
          (effectiveExecutionHandoffBundleRoutingKey
            batch queueRows baselinePollToken
            effectiveExecutionContractVersion
            (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
            generatedAt)) = "decision=1|dispatch=1|action=1" := by
    simpa [hkey] using (by native_decide :
      renderBundleRoutingCodesSummary (decodeBundleRoutingKey 111) = "decision=1|dispatch=1|action=1")
  have hnorm :
      String.intercalate ""
          [
            "\"bundleRoutingRoundTripCoherent\":", toString true, ",",
            "\"routingDiagnosticsConsistent\":true,\"routingDiagnosticsSummary\":\"routing_diagnostics_consistent=true\",",
            "\"bundleRoutingCodes\":{",
            "\"decisionCode\":", toString 1, ",",
            "\"dispatchModeCode\":", toString 1, ",",
            "\"actionCode\":", toString 1,
            "},",
            "\"bundleRoutingCodesSummary\":\"", escapeJsonField "decision=1|dispatch=1|action=1", "\","
          ] =
        "\"bundleRoutingRoundTripCoherent\":true,\"routingDiagnosticsConsistent\":true,\"routingDiagnosticsSummary\":\"routing_diagnostics_consistent=true\",\"bundleRoutingCodes\":{\"decisionCode\":1,\"dispatchModeCode\":1,\"actionCode\":1},\"bundleRoutingCodesSummary\":\"decision=1|dispatch=1|action=1\"," := by
    native_decide
  simpa [renderEffectiveExecutionHandoffBundleJsonRoutingEnvelope, hround, hfields, hsummary, hkey] using hnorm

theorem renderEffectiveExecutionHandoffBundleJsonRoutingEnvelope_bad_hash
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String) :
    renderEffectiveExecutionHandoffBundleJsonRoutingEnvelope
      batch queueRows baselinePollToken
      effectiveExecutionContractVersion
      "bad-hash"
      generatedAt =
      "\"bundleRoutingRoundTripCoherent\":true,\"routingDiagnosticsConsistent\":true,\"routingDiagnosticsSummary\":\"routing_diagnostics_consistent=true\",\"bundleRoutingCodes\":{\"decisionCode\":2,\"dispatchModeCode\":2,\"actionCode\":2},\"bundleRoutingCodesSummary\":\"decision=2|dispatch=2|action=2\"," := by
  have hkey :
      effectiveExecutionHandoffBundleRoutingKey
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        "bad-hash"
        generatedAt = 222 :=
    effectiveExecutionHandoffBundleRoutingKey_bad_hash batch queueRows baselinePollToken generatedAt
  have hround :
      bundleRoutingKeyRoundTripCoherent
        (effectiveExecutionHandoffBundleRoutingKey
          batch queueRows baselinePollToken
          effectiveExecutionContractVersion
          "bad-hash"
          generatedAt) = true := by
    simpa [hkey] using bundleRoutingKeyRoundTripCoherent_222_true
  have hfields :
      renderEffectiveExecutionHandoffRoutingDiagnosticsJsonFields
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        "bad-hash"
        generatedAt =
        "\"routingDiagnosticsConsistent\":true,\"routingDiagnosticsSummary\":\"routing_diagnostics_consistent=true\"," :=
    renderEffectiveExecutionHandoffRoutingDiagnosticsJsonFields_bad_hash
      batch queueRows baselinePollToken generatedAt
  have hsummary :
      renderBundleRoutingCodesSummary
        (decodeBundleRoutingKey
          (effectiveExecutionHandoffBundleRoutingKey
            batch queueRows baselinePollToken
            effectiveExecutionContractVersion
            "bad-hash"
            generatedAt)) = "decision=2|dispatch=2|action=2" := by
    simpa [hkey] using (by native_decide :
      renderBundleRoutingCodesSummary (decodeBundleRoutingKey 222) = "decision=2|dispatch=2|action=2")
  have hnorm :
      String.intercalate ""
          [
            "\"bundleRoutingRoundTripCoherent\":", toString true, ",",
            "\"routingDiagnosticsConsistent\":true,\"routingDiagnosticsSummary\":\"routing_diagnostics_consistent=true\",",
            "\"bundleRoutingCodes\":{",
            "\"decisionCode\":", toString 2, ",",
            "\"dispatchModeCode\":", toString 2, ",",
            "\"actionCode\":", toString 2,
            "},",
            "\"bundleRoutingCodesSummary\":\"", escapeJsonField "decision=2|dispatch=2|action=2", "\","
          ] =
        "\"bundleRoutingRoundTripCoherent\":true,\"routingDiagnosticsConsistent\":true,\"routingDiagnosticsSummary\":\"routing_diagnostics_consistent=true\",\"bundleRoutingCodes\":{\"decisionCode\":2,\"dispatchModeCode\":2,\"actionCode\":2},\"bundleRoutingCodesSummary\":\"decision=2|dispatch=2|action=2\"," := by
    native_decide
  simpa [renderEffectiveExecutionHandoffBundleJsonRoutingEnvelope, hround, hfields, hsummary, hkey] using hnorm

def renderEffectiveExecutionHandoffBundleJsonRoutingIntegrationChunkFromParts
    (bundleRoutingFingerprint : String)
    (bundleRoutingKey : Nat)
    (bundleRoutingEnvelope : String)
    (pollToken : String) : String :=
  String.intercalate ""
    [
      "\"bundleRoutingFingerprint\":\"", escapeJsonField bundleRoutingFingerprint, "\",",
      "\"bundleRoutingKey\":", toString bundleRoutingKey, ",",
      bundleRoutingEnvelope,
      "\"pollToken\":\"", escapeJsonField pollToken, "\","
    ]

def renderEffectiveExecutionHandoffBundleJsonRoutingIntegrationChunk
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (expectedVersion : String)
    (expectedHash : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  let bundleRoutingFingerprint := effectiveExecutionHandoffBundleRoutingFingerprint
    batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  let bundleRoutingKey := effectiveExecutionHandoffBundleRoutingKey
    batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  let bundleRoutingEnvelope := renderEffectiveExecutionHandoffBundleJsonRoutingEnvelope
    batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  renderEffectiveExecutionHandoffBundleJsonRoutingIntegrationChunkFromParts
    bundleRoutingFingerprint
    bundleRoutingKey
    bundleRoutingEnvelope
    (controlPlanePollingToken batch queueRows generatedAt)

theorem renderEffectiveExecutionHandoffBundleJsonRoutingIntegrationChunk_actual
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String) :
    renderEffectiveExecutionHandoffBundleJsonRoutingIntegrationChunk
      batch queueRows baselinePollToken
      effectiveExecutionContractVersion
      (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
      generatedAt =
      String.intercalate ""
        [
          "\"bundleRoutingFingerprint\":\"",
          escapeJsonField "bundle_routing_fingerprint_v1|decision=1|dispatch=1|action=1",
          "\",",
          "\"bundleRoutingKey\":",
          toString 111,
          ",",
          "\"bundleRoutingRoundTripCoherent\":true,\"routingDiagnosticsConsistent\":true,\"routingDiagnosticsSummary\":\"routing_diagnostics_consistent=true\",\"bundleRoutingCodes\":{\"decisionCode\":1,\"dispatchModeCode\":1,\"actionCode\":1},\"bundleRoutingCodesSummary\":\"decision=1|dispatch=1|action=1\",",
          "\"pollToken\":\"",
          escapeJsonField (controlPlanePollingToken batch queueRows generatedAt),
          "\","
        ] := by
  have hfingerprint :
      effectiveExecutionHandoffBundleRoutingFingerprint
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
        generatedAt = "bundle_routing_fingerprint_v1|decision=1|dispatch=1|action=1" :=
    effectiveExecutionHandoffBundleRoutingFingerprint_actual_execute
      batch queueRows baselinePollToken generatedAt
  have hkey :
      effectiveExecutionHandoffBundleRoutingKey
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
        generatedAt = 111 :=
    effectiveExecutionHandoffBundleRoutingKey_actual_execute
      batch queueRows baselinePollToken generatedAt
  have henvelope :
      renderEffectiveExecutionHandoffBundleJsonRoutingEnvelope
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        (effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt)
        generatedAt =
      "\"bundleRoutingRoundTripCoherent\":true,\"routingDiagnosticsConsistent\":true,\"routingDiagnosticsSummary\":\"routing_diagnostics_consistent=true\",\"bundleRoutingCodes\":{\"decisionCode\":1,\"dispatchModeCode\":1,\"actionCode\":1},\"bundleRoutingCodesSummary\":\"decision=1|dispatch=1|action=1\"," :=
    renderEffectiveExecutionHandoffBundleJsonRoutingEnvelope_actual
      batch queueRows baselinePollToken generatedAt
  simp [
    renderEffectiveExecutionHandoffBundleJsonRoutingIntegrationChunk,
    renderEffectiveExecutionHandoffBundleJsonRoutingIntegrationChunkFromParts,
    hfingerprint,
    hkey,
    henvelope
  ]

theorem renderEffectiveExecutionHandoffBundleJsonRoutingIntegrationChunk_bad_hash
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String) :
    renderEffectiveExecutionHandoffBundleJsonRoutingIntegrationChunk
      batch queueRows baselinePollToken
      effectiveExecutionContractVersion
      "bad-hash"
      generatedAt =
      String.intercalate ""
        [
          "\"bundleRoutingFingerprint\":\"",
          escapeJsonField "bundle_routing_fingerprint_v1|decision=2|dispatch=2|action=2",
          "\",",
          "\"bundleRoutingKey\":",
          toString 222,
          ",",
          "\"bundleRoutingRoundTripCoherent\":true,\"routingDiagnosticsConsistent\":true,\"routingDiagnosticsSummary\":\"routing_diagnostics_consistent=true\",\"bundleRoutingCodes\":{\"decisionCode\":2,\"dispatchModeCode\":2,\"actionCode\":2},\"bundleRoutingCodesSummary\":\"decision=2|dispatch=2|action=2\",",
          "\"pollToken\":\"",
          escapeJsonField (controlPlanePollingToken batch queueRows generatedAt),
          "\","
        ] := by
  have hfingerprint :
      effectiveExecutionHandoffBundleRoutingFingerprint
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        "bad-hash"
        generatedAt = "bundle_routing_fingerprint_v1|decision=2|dispatch=2|action=2" :=
    effectiveExecutionHandoffBundleRoutingFingerprint_bad_hash
      batch queueRows baselinePollToken generatedAt
  have hkey :
      effectiveExecutionHandoffBundleRoutingKey
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        "bad-hash"
        generatedAt = 222 :=
    effectiveExecutionHandoffBundleRoutingKey_bad_hash
      batch queueRows baselinePollToken generatedAt
  have henvelope :
      renderEffectiveExecutionHandoffBundleJsonRoutingEnvelope
        batch queueRows baselinePollToken
        effectiveExecutionContractVersion
        "bad-hash"
        generatedAt =
      "\"bundleRoutingRoundTripCoherent\":true,\"routingDiagnosticsConsistent\":true,\"routingDiagnosticsSummary\":\"routing_diagnostics_consistent=true\",\"bundleRoutingCodes\":{\"decisionCode\":2,\"dispatchModeCode\":2,\"actionCode\":2},\"bundleRoutingCodesSummary\":\"decision=2|dispatch=2|action=2\"," :=
    renderEffectiveExecutionHandoffBundleJsonRoutingEnvelope_bad_hash
      batch queueRows baselinePollToken generatedAt
  simp [
    renderEffectiveExecutionHandoffBundleJsonRoutingIntegrationChunk,
    renderEffectiveExecutionHandoffBundleJsonRoutingIntegrationChunkFromParts,
    hfingerprint,
    hkey,
    henvelope
  ]

def renderEffectiveExecutionHandoffBundleJson
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (expectedVersion : String)
    (expectedHash : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  let contract := renderEffectiveExecutionContractJson batch queueRows baselinePollToken generatedAt
  let contractMatch := renderEffectiveExecutionContractMatchJson
    batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  let matchSummary := renderEffectiveExecutionContractMatchSummary
    batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  let effectiveCoherent := pollActionResponseEffectiveCoherent batch queueRows baselinePollToken generatedAt
  let contractCoherent := effectiveExecutionContractCoherent batch queueRows baselinePollToken generatedAt
  let bundleConsistent :=
    effectiveCoherent && contractCoherent &&
      (effectiveExecutionContractMatches
        batch queueRows baselinePollToken expectedVersion expectedHash generatedAt)
  let bundleDecision :=
    effectiveExecutionHandoffBundleDecision
      batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  let bundleDecisionCode :=
    effectiveExecutionHandoffBundleDecisionCode
      batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  let bundleDispatchMode :=
    effectiveExecutionHandoffDispatchMode
      batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  let bundleDispatchModeCode :=
    effectiveExecutionHandoffDispatchModeCode
      batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  let bundleAction :=
    effectiveExecutionHandoffBundleAction
      batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  let bundleActionCode :=
    effectiveExecutionHandoffBundleActionCode
      batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  let bundleRoutingFingerprint :=
    effectiveExecutionHandoffBundleRoutingFingerprint
      batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  let bundleRoutingKey :=
    effectiveExecutionHandoffBundleRoutingKey
      batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  let bundleRoutingIntegrationChunk := renderEffectiveExecutionHandoffBundleJsonRoutingIntegrationChunk
    batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  let decodedRoutingCodes := decodeBundleRoutingKey bundleRoutingKey
  let decodedRoutingCodesSummary := renderBundleRoutingCodesSummary decodedRoutingCodes
  let bundleRoutingRoundTripCoherent := bundleRoutingKeyRoundTripCoherent bundleRoutingKey
  let bundleSummary :=
    if bundleConsistent then
      String.intercalate "|"
        [
          "effective_execution_handoff_bundle_consistent=true",
          "bundle_decision=" ++ bundleDecision,
          "bundle_decision_code=" ++ toString bundleDecisionCode,
          "dispatch_mode=" ++ bundleDispatchMode,
          "dispatch_mode_code=" ++ toString bundleDispatchModeCode,
          "bundle_action=" ++ bundleAction,
          "bundle_action_code=" ++ toString bundleActionCode,
          "bundle_routing_fingerprint=" ++ bundleRoutingFingerprint,
          "bundle_routing_key=" ++ toString bundleRoutingKey,
          "bundle_routing_codes=" ++ decodedRoutingCodesSummary,
          "bundle_routing_roundtrip_coherent=" ++ toString bundleRoutingRoundTripCoherent,
          renderEffectiveExecutionHandoffRoutingDiagnosticsMarker
            batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
        ]
    else
      String.intercalate "|"
        [
          "effective_execution_handoff_bundle_consistent=false",
          "effective_coherent=" ++ toString effectiveCoherent,
          "contract_coherent=" ++ toString contractCoherent,
          "bundle_decision=" ++ bundleDecision,
          "bundle_decision_code=" ++ toString bundleDecisionCode,
          "dispatch_mode=" ++ bundleDispatchMode,
          "dispatch_mode_code=" ++ toString bundleDispatchModeCode,
          "bundle_action=" ++ bundleAction,
          "bundle_action_code=" ++ toString bundleActionCode,
          "bundle_routing_fingerprint=" ++ bundleRoutingFingerprint,
          "bundle_routing_key=" ++ toString bundleRoutingKey,
          "bundle_routing_codes=" ++ decodedRoutingCodesSummary,
          "bundle_routing_roundtrip_coherent=" ++ toString bundleRoutingRoundTripCoherent,
          renderEffectiveExecutionHandoffRoutingDiagnosticsMarker
            batch queueRows baselinePollToken expectedVersion expectedHash generatedAt,
          matchSummary
        ]
  String.intercalate ""
    [
      "{",
      "\"schema\":\"heytingveil.execution.handoff_bundle.v1\",",
      "\"generatedAt\":\"", escapeJsonField generatedAt, "\",",
      "\"baselinePollToken\":\"", escapeJsonField baselinePollToken, "\",",
      "\"effectiveCoherent\":", toString effectiveCoherent, ",",
      "\"effectiveExecutionContractCoherent\":", toString contractCoherent, ",",
      "\"bundleConsistent\":", toString bundleConsistent, ",",
      "\"bundleDecision\":\"", escapeJsonField bundleDecision, "\",",
      "\"bundleDecisionCode\":", toString bundleDecisionCode, ",",
      "\"bundleDispatchMode\":\"", escapeJsonField bundleDispatchMode, "\",",
      "\"bundleDispatchModeCode\":", toString bundleDispatchModeCode, ",",
      "\"bundleAction\":\"", escapeJsonField bundleAction, "\",",
      "\"bundleActionCode\":", toString bundleActionCode, ",",
      bundleRoutingIntegrationChunk,
      "\"matchSummary\":\"", escapeJsonField matchSummary, "\",",
      "\"bundleSummary\":\"", escapeJsonField bundleSummary, "\",",
      "\"effectiveExecutionContract\":", contract, ",",
      "\"effectiveExecutionContractMatch\":", contractMatch,
      "}"
    ]

def effectiveExecutionHandoffBundleConsistent
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (expectedVersion : String)
    (expectedHash : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : Bool :=
  (pollActionResponseEffectiveCoherent batch queueRows baselinePollToken generatedAt) &&
    (effectiveExecutionContractCoherent batch queueRows baselinePollToken generatedAt) &&
    (effectiveExecutionContractMatches
      batch queueRows baselinePollToken expectedVersion expectedHash generatedAt)

def renderEffectiveExecutionHandoffBundleSummary
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (expectedVersion : String)
    (expectedHash : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  let effectiveCoherent := pollActionResponseEffectiveCoherent batch queueRows baselinePollToken generatedAt
  let contractCoherent := effectiveExecutionContractCoherent batch queueRows baselinePollToken generatedAt
  let matchSummary := renderEffectiveExecutionContractMatchSummary
    batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  let consistent :=
    effectiveExecutionHandoffBundleConsistent
      batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  let decision :=
    effectiveExecutionHandoffBundleDecision
      batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  let decisionCode :=
    effectiveExecutionHandoffBundleDecisionCode
      batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  let dispatchMode :=
    effectiveExecutionHandoffDispatchMode
      batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  let dispatchModeCode :=
    effectiveExecutionHandoffDispatchModeCode
      batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  let bundleAction :=
    effectiveExecutionHandoffBundleAction
      batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  let bundleActionCode :=
    effectiveExecutionHandoffBundleActionCode
      batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  let bundleRoutingFingerprint :=
    effectiveExecutionHandoffBundleRoutingFingerprint
      batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  let bundleRoutingKey :=
    effectiveExecutionHandoffBundleRoutingKey
      batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
  let decodedRoutingCodes := decodeBundleRoutingKey bundleRoutingKey
  let decodedRoutingCodesSummary := renderBundleRoutingCodesSummary decodedRoutingCodes
  let bundleRoutingRoundTripCoherent := bundleRoutingKeyRoundTripCoherent bundleRoutingKey
  if consistent then
    String.intercalate "|"
      [
        "effective_execution_handoff_bundle_consistent=true",
        "bundle_decision=" ++ decision,
        "bundle_decision_code=" ++ toString decisionCode,
        "dispatch_mode=" ++ dispatchMode,
        "dispatch_mode_code=" ++ toString dispatchModeCode,
        "bundle_action=" ++ bundleAction,
        "bundle_action_code=" ++ toString bundleActionCode,
        "bundle_routing_fingerprint=" ++ bundleRoutingFingerprint,
        "bundle_routing_key=" ++ toString bundleRoutingKey,
        "bundle_routing_codes=" ++ decodedRoutingCodesSummary,
        "bundle_routing_roundtrip_coherent=" ++ toString bundleRoutingRoundTripCoherent,
        renderEffectiveExecutionHandoffRoutingDiagnosticsMarker
          batch queueRows baselinePollToken expectedVersion expectedHash generatedAt
      ]
  else
    String.intercalate "|"
      [
        "effective_execution_handoff_bundle_consistent=false",
        "effective_coherent=" ++ toString effectiveCoherent,
        "contract_coherent=" ++ toString contractCoherent,
        "bundle_decision=" ++ decision,
        "bundle_decision_code=" ++ toString decisionCode,
        "dispatch_mode=" ++ dispatchMode,
        "dispatch_mode_code=" ++ toString dispatchModeCode,
        "bundle_action=" ++ bundleAction,
        "bundle_action_code=" ++ toString bundleActionCode,
        "bundle_routing_fingerprint=" ++ bundleRoutingFingerprint,
        "bundle_routing_key=" ++ toString bundleRoutingKey,
        "bundle_routing_codes=" ++ decodedRoutingCodesSummary,
        "bundle_routing_roundtrip_coherent=" ++ toString bundleRoutingRoundTripCoherent,
        renderEffectiveExecutionHandoffRoutingDiagnosticsMarker
          batch queueRows baselinePollToken expectedVersion expectedHash generatedAt,
        matchSummary
      ]

def pollActionDigest
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  String.intercalate "|"
    [
      "heytingveil.intake.control_plane_poll_action_response.v1",
      effectiveAction batch queueRows baselinePollToken generatedAt,
      effectiveReason batch queueRows baselinePollToken generatedAt,
      effectiveStatus batch queueRows baselinePollToken generatedAt,
      effectiveStatusClass batch queueRows baselinePollToken generatedAt,
      toString (effectiveExecutionAllowed batch queueRows baselinePollToken generatedAt),
      effectiveExecutionDirective batch queueRows baselinePollToken generatedAt,
      effectiveRunnerEnvelope batch queueRows baselinePollToken generatedAt,
      effectiveExecutionContractVersion,
      effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt,
      toString (effectiveFetchHandoff batch queueRows baselinePollToken generatedAt),
      effectiveFetchTarget batch queueRows baselinePollToken generatedAt,
      effectiveNextStep batch queueRows baselinePollToken generatedAt,
      bridgeGateReason batch,
      controlPlanePollingToken batch queueRows generatedAt
    ]

def pollActionResponseSchema : String :=
  "heytingveil.intake.control_plane_poll_action_response.v1"

def renderDispatchRemediationPollActionResponseJson
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (baselinePollToken : String)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  let action := pollAction batch queueRows baselinePollToken generatedAt
  let reason := pollActionReason batch queueRows baselinePollToken generatedAt
  let effective := effectiveAction batch queueRows baselinePollToken generatedAt
  let effectiveReason' := effectiveReason batch queueRows baselinePollToken generatedAt
  let effectiveStatus' := effectiveStatus batch queueRows baselinePollToken generatedAt
  let effectiveStatusClass' := effectiveStatusClass batch queueRows baselinePollToken generatedAt
  let effectiveExecutionAllowed' := effectiveExecutionAllowed batch queueRows baselinePollToken generatedAt
  let effectiveExecutionDirective' := effectiveExecutionDirective batch queueRows baselinePollToken generatedAt
  let effectiveRunnerEnvelope' := effectiveRunnerEnvelope batch queueRows baselinePollToken generatedAt
  let effectiveExecutionContractVersion' := effectiveExecutionContractVersion
  let effectiveExecutionContractHash' := effectiveExecutionContractHash batch queueRows baselinePollToken generatedAt
  String.intercalate ""
    [
      "{",
      "\"schema\":\"", escapeJsonField pollActionResponseSchema, "\",",
      "\"generatedAt\":\"", escapeJsonField generatedAt, "\",",
      "\"action\":\"", escapeJsonField action, "\",",
      "\"effectiveAction\":\"", escapeJsonField effective, "\",",
      "\"reason\":\"", escapeJsonField reason, "\",",
      "\"effectiveReason\":\"", escapeJsonField effectiveReason', "\",",
      "\"effectiveStatus\":\"", escapeJsonField effectiveStatus', "\",",
      "\"effectiveStatusClass\":\"", escapeJsonField effectiveStatusClass', "\",",
      "\"effectiveExecutionAllowed\":", toString effectiveExecutionAllowed', ",",
      "\"effectiveExecutionDirective\":\"", escapeJsonField effectiveExecutionDirective', "\",",
      "\"effectiveRunnerEnvelope\":\"", escapeJsonField effectiveRunnerEnvelope', "\",",
      "\"effectiveExecutionContractVersion\":\"", escapeJsonField effectiveExecutionContractVersion', "\",",
      "\"effectiveExecutionContractHash\":\"", escapeJsonField effectiveExecutionContractHash', "\",",
      "\"fetchHandoff\":", toString (fetchHandoffDirective batch queueRows baselinePollToken generatedAt), ",",
      "\"fetchTarget\":\"", escapeJsonField (fetchTarget batch queueRows baselinePollToken generatedAt), "\",",
      "\"effectiveFetchHandoff\":", toString (effectiveFetchHandoff batch queueRows baselinePollToken generatedAt), ",",
      "\"effectiveFetchTarget\":\"", escapeJsonField (effectiveFetchTarget batch queueRows baselinePollToken generatedAt), "\",",
      "\"nextStep\":\"", escapeJsonField (pollNextStep batch queueRows baselinePollToken generatedAt), "\",",
      "\"effectiveNextStep\":\"", escapeJsonField (effectiveNextStep batch queueRows baselinePollToken generatedAt), "\",",
      "\"bridgeGateAllowsExecution\":", toString (bridgeGateAllowsExecution batch), ",",
      "\"bridgeGateReason\":\"", escapeJsonField (bridgeGateReason batch), "\",",
      "\"unresolvedBridgeSpecs\":", renderStringJsonList (unresolvedBridgeSpecLabels batch), ",",
      "\"actionDigest\":\"", escapeJsonField (pollActionDigest batch queueRows baselinePollToken generatedAt), "\",",
      "\"coherent\":", toString (pollActionResponseCoherent batch queueRows baselinePollToken generatedAt), ",",
      "\"effectiveCoherent\":", toString (pollActionResponseEffectiveCoherent batch queueRows baselinePollToken generatedAt), ",",
      "\"effectiveExecutionContractSummary\":\"",
        escapeJsonField (renderEffectiveExecutionContractCoherenceSummary batch queueRows baselinePollToken generatedAt), "\",",
      "\"effectiveExecutionContract\":",
        renderEffectiveExecutionContractJson batch queueRows baselinePollToken generatedAt, ",",
      "\"pollResponse\":", renderDispatchRemediationPollResponseJson batch queueRows baselinePollToken generatedAt,
      "}"
    ]

def renderDispatchRemediationControlPlaneConsistencySummary
    (batch : DispatchBatch)
    (queueRows : List LabeledRemediationPacketRow)
    (generatedAt : String := "1970-01-01T00:00:00Z") : String :=
  "quick_consistent_with_handoff=" ++ toString (quickConsistentWithHandoff batch queueRows generatedAt)

end DispatchBatch
end Intake
end HeytingVeil
end HeytingLean
