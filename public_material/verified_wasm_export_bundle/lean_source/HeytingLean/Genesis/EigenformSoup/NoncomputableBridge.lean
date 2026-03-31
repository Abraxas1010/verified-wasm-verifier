import HeytingLean.Genesis.EigenformSoup.Runner
import HeytingLean.Genesis.EigenformSoup.Extraction
import HeytingLean.Genesis.EigenformSoup.BridgeCommitment

/-!
# Genesis.EigenformSoup.NoncomputableBridge

Bridge surface from noncomputable soup semantics to executable protocol lanes.

This module does not attempt to execute noncomputable `runSoup*` terms at runtime.
Instead, it exposes theorems and a compact bridge-card schema that can be emitted
as an artifact and referenced by executable protocol manifests.
-/

namespace HeytingLean.Genesis.EigenformSoup

private def jsonEscapeChar (c : Char) : String :=
  if c = '\"' then
    "\\\""
  else if c = '\\' then
    "\\\\"
  else if c = '\n' then
    "\\n"
  else if c = '\r' then
    "\\r"
  else if c = '\t' then
    "\\t"
  else
    String.singleton c

private def jsonEscape (s : String) : String :=
  String.join (s.data.map jsonEscapeChar)

private def rowJson (r : TheoremBridgeRow) : String :=
  String.intercalate ""
    [ "{"
    , s!"\"theorem_id\":\"{jsonEscape r.theoremId}\","
    , s!"\"source_path\":\"{jsonEscape r.sourcePath}\","
    , s!"\"role\":\"{jsonEscape r.role}\","
    , s!"\"proof_object_digest_sha256\":\"{jsonEscape r.proofObjectDigestSha256}\""
    , "}"
    ]

/-- Bridge card JSON payload exported for protocol manifests. -/
def bridgeCardJson : String :=
  let rows := String.intercalate "," (theoremBridgeRows.map rowJson)
  String.intercalate ""
    [ "{"
    , s!"\"schema\":\"{bridgeCardSchema}\","
    , "\"lane\":\"noncomputable_bridge\","
    , s!"\"proof_obligation_commitment_schema\":\"{proofObligationCommitmentSchema}\","
    , s!"\"proof_object_digest_scheme\":\"{proofObjectDigestScheme}\","
    , s!"\"proof_obligation_commitment_sha256\":\"{proofObligationCommitmentSha256}\","
    , "\"notes\":\"Theorem obligations connect noncomputable soup semantics to executable lanes.\","
    , s!"\"theorem_rows\":[{rows}]"
    , "}"
    ]

/-- SHA-256 digest of the exported bridge card payload. -/
def bridgeCardSha256 : String :=
  HeytingLean.Util.SHA256.sha256Hex bridgeCardJson.toUTF8

theorem theoremBridgeRows_nonempty : theoremBridgeRows ≠ [] := by
  simp [theoremBridgeRows]

/-- Bridge alias for trace length theorem used by executable manifest tooling. -/
theorem bridge_runSoupTrace_length
    (nuc : SoupNucleus) (cfg : SoupConfig) :
    (runSoupTrace nuc cfg).length = cfg.fuel + 1 :=
  runSoupTrace_length nuc cfg

/-- Bridge alias for snapshot length theorem used by executable manifest tooling. -/
theorem bridge_runSoupTraceSnapshots_length
    (nuc : SoupNucleus) (cfg : SoupConfig) :
    (runSoupTraceSnapshots nuc cfg).length = cfg.fuel + 1 :=
  runSoupTraceSnapshots_length nuc cfg

/-- Bridge alias for stabilized-support soundness. -/
theorem bridge_runSoup_sound
    (nuc : SoupNucleus) (cfg : SoupConfig) (S : Support)
    (hS : S ∈ (runSoup nuc cfg).stabilized) :
    isEigenform nuc S :=
  runSoup_sound nuc cfg S hS

/-- Bridge alias for extraction stage-correctness. -/
theorem bridge_compileSoupCAB_allStagesCorrect
    (nuc : SoupNucleus) (cfg : SoupConfig) :
    (compileSoupCAB nuc cfg).allStagesCorrect = true :=
  compileSoupCAB_allStagesCorrect nuc cfg

end HeytingLean.Genesis.EigenformSoup
