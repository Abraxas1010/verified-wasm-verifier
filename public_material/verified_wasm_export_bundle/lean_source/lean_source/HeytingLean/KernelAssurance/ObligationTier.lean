import HeytingLean.KernelAssurance.ObligationChecker
import HeytingLean.KernelAssurance.Tier

namespace HeytingLean.KernelAssurance

open Lean

def canGrantObligationSliceReplayed
    (coverage : ObligationCoverageReport)
    (replay : ObligationReplayReport) : Bool :=
  coverage.obligationsTotal > 0 &&
  coverage.supportedObligations > 0 &&
  replay.bundleDigestValid &&
  replay.failed = 0 &&
  replay.checked = coverage.supportedObligations &&
  coverage.obligationsTotal =
    coverage.supportedObligations + coverage.blockedObligations + coverage.unclassifiedObligations

def canGrantObligationSliceCheckerCertified
    (coverage : ObligationCoverageReport)
    (replay : ObligationReplayReport)
    (checker : ObligationCheckerReport) : Bool :=
  canGrantObligationSliceReplayed coverage replay &&
  coverage.loweringFormallyVerified &&
  checker.bundleDigestValid &&
  checker.failed = 0 &&
  checker.checked = coverage.obligationsTotal &&
  coverage.blockedObligations = 0 &&
  coverage.unclassifiedObligations = 0 &&
  coverage.blockedFamilyCount = 0 &&
  coverage.unclassifiedFamilyCount = 0

def decideObligationTier
    (requested : AssuranceTier)
    (coverage : ObligationCoverageReport)
    (replay : ObligationReplayReport)
    (checker : ObligationCheckerReport) : TierDecision :=
  match requested with
  | .none =>
      { requested := requested, granted := .none, reason := "No obligation assurance tier requested." }
  | .slice_replayed =>
      if canGrantObligationSliceReplayed coverage replay then
        { requested := requested
          granted := .slice_replayed
          reason := "CPU truth-lane obligation replay succeeded for the supported exported slice." }
      else
        { requested := requested
          granted := .none
          reason := "Obligation replay gate failed for the requested slice." }
  | .slice_checker_certified =>
      if canGrantObligationSliceCheckerCertified coverage replay checker then
        { requested := requested
          granted := .slice_checker_certified
          reason := "Obligation replay and checker gates both closed with no blocked or unclassified obligation families." }
      else if canGrantObligationSliceReplayed coverage replay then
        { requested := requested
          granted := .slice_replayed
          reason := "Obligation checker-certified gate failed; replay-only tier remains valid." }
      else
        { requested := requested
          granted := .none
          reason := "Neither obligation replay nor checker tier is valid for this slice." }

end HeytingLean.KernelAssurance
