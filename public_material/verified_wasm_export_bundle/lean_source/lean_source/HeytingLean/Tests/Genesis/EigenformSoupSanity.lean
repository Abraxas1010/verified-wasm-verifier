import HeytingLean.Genesis

/-!
# Genesis EigenformSoup Sanity
-/

namespace HeytingLean.Tests.Genesis

open HeytingLean.Genesis.EigenformSoup

#check collapsePolicy
#check generateElements
#check runSoup
#check runtimeTrace
#check runtimeTraceAux_length
#check runSoupTrace
#check runSoupTraceAux_length
#check runSoupTrace_length
#check runSoupTraceSnapshots
#check runSoupTraceSnapshots_length
#check traceSnapshotChecksum
#check bridgeCardSchema
#check theoremBridgeRows
#check bridgeCardJson
#check bridgeCardSha256
#check proofObligationCommitmentSchema
#check proofObjectDigestScheme
#check proofObligationCommitmentMaterial
#check proofObligationCommitmentSha256
#check soupProofMaterial_bridgeAnchored
#check soupTraceProofMaterial_bridgeAnchored
#check compileSoupCAB
#check compileSoupTraceCAB
#check compileSoupTraceCAB_cCode_has_traceChecksum
#check compileSoupCAB_stage_relations
#check compileSoupCAB_cCode_has_stabilizedCount
#check compileSoupTraceCAB_allStagesCorrect
#check mkCertifiedSoupCAB_commitment_eq
#check mkCertifiedSoupTraceCAB_commitment_eq
#check collapsePolicy_not_bridgeReady
#check thesis_antithesis_coequal
#check ratchetClick_iff_synthesisMass_pos
#check symbiogenesis_complexity_growth
#check j_ratchet_monotonicity
#check alignsWithJRatchetVocabulary
#check alignsWithJRatchetVocabulary_intro
#check bridge_runSoupTrace_length
#check bridge_runSoupTraceSnapshots_length
#check bridge_runSoup_sound
#check bridge_compileSoupCAB_allStagesCorrect
#check extractionSemanticParityGate
#check extractionSemanticParityGate_holds
#check ws9GateStatus
#check ws9GateStatus_true_of_all_true
#check ws9GateStatus_false_if_r3_false

noncomputable example :
    runDeterministicReport collapsePolicy {} = runDeterministicReport collapsePolicy {} :=
  runDeterministicReport_deterministic collapsePolicy {}

noncomputable example :
    ws9GateStatus collapsePolicy {} { boundaryOk := true, r3Ok := true } = true :=
  ws9GateStatus_true_of_all_true collapsePolicy {}

noncomputable example :
    ws9GateStatus collapsePolicy {} { boundaryOk := true, r3Ok := false } = false :=
  ws9GateStatus_false_if_r3_false collapsePolicy {}

end HeytingLean.Tests.Genesis
