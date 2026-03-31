import Lean.Data.Json
import HeytingLean.ATP.DifferentiableATP.LensGDOrchestrator
import HeytingLean.ATP.DifferentiableATP.KernelVerifier
import HeytingLean.ATP.DifferentiableATP.SheafResolution
import HeytingLean.ATP.ProofNetwork
import HeytingLean.ATP.SheafGluing

/-!
# ATP.DifferentiableATP.FeedbackBridge

Converts differentiable-ATP run results into proof-network + JSON feedback payloads.
-/

namespace HeytingLean
namespace ATP
namespace DifferentiableATP

open Lean
open HeytingLean.Embeddings

private def lensName : LensID → String
  | .omega => "omega"
  | .region => "region"
  | .graph => "graph"
  | .clifford => "clifford"
  | .tensor => "tensor"
  | .topology => "topology"
  | .matula => "matula"

private def gdModeName : GDMode → String
  | .projected => "projected"
  | .retracted => "retracted"

private def trackModeName : TrackMode → String
  | .baseline => "baseline"
  | .kan => "kan"
  | .nca => "nca"
  | .kan_nca => "kan_nca"

private def selectedProbeLens? (seg : LaneSegment) : Option LensID :=
  match seg.laneDecision with
  | .switch lens => some lens
  | .stay => none

private def probeToJson (selectedLens : Option LensID) (p : ProbeResult) : Json :=
  Json.mkObj
    [ ("lens", Json.str (lensName p.lens))
    , ("initial_psr", Json.str (toString p.initialPSR))
    , ("final_psr", Json.str (toString p.finalPSR))
    , ("psr_descent_rate", Json.str (toString p.psrDescentRate))
    , ("initial_io_loss", Json.str (toString p.initialIOLoss))
    , ("final_io_loss", Json.str (toString p.finalIOLoss))
    , ("io_descent_rate", Json.str (toString p.ioDescentRate))
    , ("score", Json.str (toString p.score))
    , ("selected", Json.bool (selectedLens = some p.lens))
    ]

structure FeedbackPayload where
  ok : Bool
  proved : Bool
  reason : String
  selectedTactic : Option String
  theoremName : String
  network : ProofNetwork
  run : Result
  verifier : VerificationResult

private def theoremNameOfGoal (goal : String) : String :=
  s!"differentiable_goal_{hash goal}"

private def buildNetwork (goal : String) (run : Result) (verifier : VerificationResult) : ProofNetwork :=
  let rec go (segments : List LaneSegment) (g : ProofNetwork) (prev : Option Nat) : ProofNetwork :=
    match segments with
    | [] => g
    | seg :: rest =>
        let label := s!"differentiable::{lensName seg.lens}"
        let (g1, id) := g.addNode seg.lens label
        let g2 := g1.setNodeGoal id (some goal)
        let g3 :=
          match prev with
          | some p => ATP.addWitnessedGlueEdge g2 p id "cross_lens_transport"
          | none => g2
        go rest g3 (some id)
  let g0 := go run.segments {} none
  let lastId :=
    match run.segments.reverse with
    | [] => none
    | seg :: _ =>
        g0.nodes.find? (fun n => n.lens = seg.lens) |>.map (fun n => n.id)
  match lastId with
  | none => g0
  | some id =>
      if verifier.ok then
        let artifact : ProofArtifact :=
          {
            theoremName := theoremNameOfGoal goal
            theoremStatement := some goal
            replayScript := verifier.verifiedTactic
            sheafWitnesses := run.laneHistory.map lensName
          }
        g0.setNodeOutcome id (.proved artifact)
      else
        let blockedCert : BlockedCertificate :=
          {
            obstructionClass := "differentiable_solver_unverified"
            suggestedLenses := run.laneHistory
            obligations := ["kernel_verification_failed"]
            notes := [verifier.reason]
          }
        g0.setNodeOutcome id (.blockedCertified blockedCert)

def buildPayload (goal : String) (run : Result) (verifier : VerificationResult) : FeedbackPayload :=
  let proved := verifier.ok
  {
    ok := run.ok
    proved := proved
    reason := if proved then "proved" else verifier.reason
    selectedTactic := verifier.verifiedTactic
    theoremName := theoremNameOfGoal goal
    network := buildNetwork goal run verifier
    run := run
    verifier := verifier
  }

private def laneSegmentToJson (seg : LaneSegment) : Json :=
  let selectedLens := selectedProbeLens? seg
  let probes := Json.arr <| seg.gradientProbes.toArray.map (probeToJson selectedLens)
  Json.mkObj
    [ ("lens", Json.str (lensName seg.lens))
    , ("loss", Json.str (toString seg.state.currentLoss))
    , ("psr_loss", Json.str (toString seg.psrLoss))
    , ("dialectic_loss", Json.str (toString seg.dialecticLoss))
    , ("occam_loss", Json.str (toString seg.occamLoss))
    , ("psr_dynamics_loss", Json.str (toString seg.psrDynamicsLoss))
    , ("curriculum_weight", Json.str (toString seg.curriculumWeight))
    , ("sheaf_resolution", Json.num seg.sheafResolution)
    , ("sheaf_basis_size", Json.num seg.sheafBasisSize)
    , ("iterations", Json.num seg.state.iteration)
    , ("verdict", Json.str seg.verdict.reason)
    , ("stuck", Json.bool seg.verdict.stuck)
    , ("converged", Json.bool seg.verdict.converged)
    , ("psr_converged", Json.bool seg.verdict.psrConverged)
    , ("monotonicity_score", Json.str (toString seg.verdict.monotonicityScore))
    , ("attention_keywords", Json.arr <| seg.attentionKeywords.toArray.map Json.str)
    , ("premise_hints_used", Json.arr <| seg.premiseHintsUsed.toArray.map Json.str)
    , ("gradient_probes", probes)
    , ("multiway_mode", Json.bool seg.multiwayMode)
    , ("track_mode", Json.str (trackModeName seg.trackMode))
    , ("track_converged", Json.bool seg.trackConverged)
    , ("track_cell_count", Json.num seg.trackCellCount)
    , ("track_stability_score", Json.str (toString seg.trackStabilityScore))
    , ("track_symbolic_summaries", Json.arr <| seg.symbolicSummaries.toArray.map Json.str)
    , ("progress_score", Json.str (toString seg.progressScore))
    , ("tactic_diversity_index", Json.str (toString seg.tacticDiversityIndex))
    , ("best_tactic", Json.str <| (seg.candidates.headD (decodeComb .K)).tactic)
    ]

def payloadToJson (p : FeedbackPayload) : Json :=
  let historyJson := Json.arr <| p.run.laneHistory.toArray.map (fun lens => Json.str (lensName lens))
  let segmentsJson := Json.arr <| p.run.segments.toArray.map laneSegmentToJson
  let allProbes : List Json :=
    p.run.segments.foldl
      (fun acc seg =>
        acc ++ seg.gradientProbes.map (fun probe =>
          let selectedLens := selectedProbeLens? seg
          Json.mkObj
            [ ("segment_lens", Json.str (lensName seg.lens))
            , ("lens", Json.str (lensName probe.lens))
            , ("psr_descent_rate", Json.str (toString probe.psrDescentRate))
            , ("io_descent_rate", Json.str (toString probe.ioDescentRate))
            , ("score", Json.str (toString probe.score))
            , ("selected", Json.bool (selectedLens = some probe.lens))
            ]))
      []
  let allProbesJson := Json.arr <| allProbes.toArray
  let proofArtifactJson :=
    if p.proved then
      Json.mkObj
        [ ("theorem_name", Json.str p.theoremName)
        , ("statement", Json.str p.run.goal)
        , ("replay_tactic", match p.selectedTactic with | some t => Json.str t | none => Json.null)
        ]
    else
      Json.null
  let blockedJson :=
    if p.proved then Json.null
    else
      Json.mkObj
        [ ("obstruction_class", Json.str "differentiable_solver_unverified")
        , ("reason", Json.str p.reason)
        ]
  Json.mkObj
    [ ("ok", Json.bool p.ok)
    , ("proved", Json.bool p.proved)
    , ("reason", Json.str p.reason)
    , ("theorem_name", Json.str p.theoremName)
    , ("selected_tactic", match p.selectedTactic with | some t => Json.str t | none => Json.null)
    , ("lane_history", historyJson)
    , ("lane_changes_used", Json.num p.run.laneChangesUsed)
    , ("final_lens", Json.str (lensName p.run.finalLens))
    , ("transport_used", Json.bool p.run.transportUsed)
    , ("use_sheaf_transport", Json.bool p.run.useSheafTransport)
    , ("multiway_mode", Json.bool p.run.useMultiwayGD)
    , ("gd_mode", Json.str (gdModeName p.run.gdMode))
    , ("track_mode", Json.str (trackModeName p.run.trackMode))
    , ("track_converged", Json.bool p.run.trackConverged)
    , ("track_cell_count", Json.num p.run.trackCellCount)
    , ("track_stability_score", Json.str (toString p.run.trackStabilityScore))
    , ("track_symbolic_summaries", Json.arr <| p.run.symbolicSummaries.toArray.map Json.str)
    , ("progress_score", Json.str (toString p.run.progressScore))
    , ("tactic_diversity_index", Json.str (toString p.run.tacticDiversityIndex))
    , ("psr_loss", Json.str (toString p.run.psrLoss))
    , ("dialectic_loss", Json.str (toString p.run.dialecticLoss))
    , ("occam_loss", Json.str (toString p.run.occamLoss))
    , ("psr_dynamics_loss", Json.str (toString p.run.psrDynamicsLoss))
    , ("psr_converged", Json.bool p.run.psrConverged)
    , ("monotonicity_score", Json.str (toString p.run.monotonicityScore))
    , ("sheaf_final_resolution", Json.num p.run.sheafFinalResolution)
    , ("sheaf_final_basis_size", Json.num p.run.sheafFinalBasisSize)
    , ("attention_keywords", Json.arr <| p.run.attentionKeywords.toArray.map Json.str)
    , ("premise_hints_used", Json.arr <| p.run.premiseHintsUsed.toArray.map Json.str)
    , ("gradient_probes", allProbesJson)
    , ("categorical_bridge", Json.mkObj
        [ ("algebra_hom_witness", Json.bool p.run.categoricalEvidence.algebraHomWitness)
        , ("step_preserves_evidence", Json.bool p.run.categoricalEvidence.stepPreservesEvidence)
        , ("map_fixed_used", Json.bool p.run.categoricalEvidence.mapFixedUsed)
        , ("transport_mode", Json.str p.run.categoricalEvidence.transportMode)
        , ("witness_theorems", Json.arr <| p.run.categoricalEvidence.witnessTheorems.toArray.map Json.str)
        ])
    , ("segments", segmentsJson)
    , ("verifier", toJson p.verifier)
    , ("proof_artifact", proofArtifactJson)
    , ("blocked_certificate", blockedJson)
    , ("proof_network", Json.mkObj
        [ ("node_count", Json.num (ProofNetwork.nodeCount p.network))
        , ("edge_count", Json.num (ProofNetwork.edgeCount p.network))
        ])
    ]

end DifferentiableATP
end ATP
end HeytingLean
