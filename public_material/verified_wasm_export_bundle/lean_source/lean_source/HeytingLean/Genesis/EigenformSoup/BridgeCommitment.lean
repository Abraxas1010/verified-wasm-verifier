import HeytingLean.Util.SHA

/-!
# Genesis.EigenformSoup.BridgeCommitment

Shared theorem-obligation commitment material for LES noncomputable bridge
artifacts and extraction/certification outputs.
-/

namespace HeytingLean.Genesis.EigenformSoup

/-- One theorem bridge row exported in the bridge card artifact. -/
structure TheoremBridgeRow where
  theoremId : String
  sourcePath : String
  role : String
  proofObjectDigestSha256 : String
deriving Repr, Inhabited

/-- Stable schema id for the noncomputable bridge card artifact. -/
def bridgeCardSchema : String :=
  "HeytingLean/LESNoncomputableBridge.v1"

/-- Stable schema id for theorem-obligation commitment material. -/
def proofObligationCommitmentSchema : String :=
  "les_proof_obligation_material_v1"

/-- Stable digest scheme id for theorem proof-object digests. -/
def proofObjectDigestScheme : String :=
  "lean_proof_object_v1"

/-- Canonical theorem bridge rows for LES protocol alignment. -/
def theoremBridgeRows : List TheoremBridgeRow :=
  [ { theoremId := "runSoupTrace_length"
      sourcePath := "lean/HeytingLean/Genesis/EigenformSoup/Runner.lean"
      role := "trace_length_contract"
      proofObjectDigestSha256 := "226e59d97f38e9cf2b3428d5d8dc1048fee4aaff31118332c0b416b91b4a9aed" }
  , { theoremId := "runSoupTraceSnapshots_length"
      sourcePath := "lean/HeytingLean/Genesis/EigenformSoup/Runner.lean"
      role := "snapshot_length_contract"
      proofObjectDigestSha256 := "5272bf5f82e74c6ebf451c2886e9c07f9ce27e38741feb3a771556f3d5280e06" }
  , { theoremId := "runSoup_sound"
      sourcePath := "lean/HeytingLean/Genesis/EigenformSoup/Runner.lean"
      role := "stabilized_eigenform_soundness"
      proofObjectDigestSha256 := "4d9b3de31ff33b1dc7c6c69d3ba76912ef5c44228ecb5d51ade7aa67f929ad68" }
  , { theoremId := "compileSoupCAB_allStagesCorrect"
      sourcePath := "lean/HeytingLean/Genesis/EigenformSoup/Extraction.lean"
      role := "extraction_pipeline_stage_soundness"
      proofObjectDigestSha256 := "4a29bd153ea624ae703f41d7fbacf9a1d5b34d23475a62299674babbe1bf1991" }
  , { theoremId := "compileSoupCAB_cCode_has_stabilizedCount"
      sourcePath := "lean/HeytingLean/Genesis/EigenformSoup/Extraction.lean"
      role := "extraction_payload_alignment"
      proofObjectDigestSha256 := "6191d062008d1c3a7cb57d9fa604e2c50d5653160cc3c1855df8038395911b9c" }
  ]

private def theoremBridgeRowMaterial (r : TheoremBridgeRow) : String :=
  s!"{r.theoremId}|{r.sourcePath}|{r.role}|{r.proofObjectDigestSha256}"

/-- Canonical material payload for theorem-obligation commitments. -/
def proofObligationCommitmentMaterial : String :=
  let rows := String.intercalate ";" (theoremBridgeRows.map theoremBridgeRowMaterial)
  s!"schema={bridgeCardSchema}|lane=noncomputable_bridge|proof_schema={proofObligationCommitmentSchema}|proof_object_scheme={proofObjectDigestScheme}|rows={rows}"

/-- SHA-256 digest for theorem-obligation commitments. -/
def proofObligationCommitmentSha256 : String :=
  HeytingLean.Util.SHA256.sha256Hex proofObligationCommitmentMaterial.toUTF8

end HeytingLean.Genesis.EigenformSoup
