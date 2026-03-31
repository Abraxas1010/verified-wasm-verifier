import HeytingLean.KernelAssurance.Checker

namespace HeytingLean.KernelAssurance

open Lean

inductive AssuranceTier where
  | none
  | slice_replayed
  | slice_checker_certified
  deriving Repr, Inhabited, BEq, DecidableEq, ToJson, FromJson

instance : ToString AssuranceTier where
  toString
    | .none => "none"
    | .slice_replayed => "slice_replayed"
    | .slice_checker_certified => "slice_checker_certified"

def AssuranceTier.ofString? : String → Option AssuranceTier
  | "none" => some .none
  | "slice_replayed" => some .slice_replayed
  | "slice_checker_certified" => some .slice_checker_certified
  | _ => none

structure TierDecision where
  requested : AssuranceTier
  granted : AssuranceTier
  reason : String
  deriving Repr, Inhabited, BEq, ToJson, FromJson

def canGrantSliceReplayed (coverage : CoverageReport) (replay : ReplayReport) : Bool :=
  coverage.declsTotal > 0 &&
  coverage.supportedDecls > 0 &&
  replay.bundleDigestValid &&
  replay.failed = 0 &&
  replay.checked = coverage.supportedDecls &&
  coverage.declsTotal = coverage.supportedDecls + coverage.blockedDecls + coverage.unclassifiedDecls

def canGrantSliceCheckerCertified
    (coverage : CoverageReport)
    (replay : ReplayReport)
    (checker : CheckerReport) : Bool :=
  canGrantSliceReplayed coverage replay &&
  checker.bundleDigestValid &&
  checker.failed = 0 &&
  checker.checked = coverage.declsTotal &&
  coverage.blockedDecls = 0 &&
  coverage.unclassifiedDecls = 0 &&
  coverage.blockedFamilyCount = 0 &&
  coverage.unclassifiedFamilyCount = 0

def decideTier
    (requested : AssuranceTier)
    (coverage : CoverageReport)
    (replay : ReplayReport)
    (checker : CheckerReport) : TierDecision :=
  match requested with
  | .none =>
      { requested := requested, granted := .none, reason := "No assurance tier requested." }
  | .slice_replayed =>
      if canGrantSliceReplayed coverage replay then
        { requested := requested, granted := .slice_replayed, reason := "CPU truth-lane replay succeeded for the supported slice." }
      else
        { requested := requested, granted := .none, reason := "Replay gate failed for the requested slice." }
  | .slice_checker_certified =>
      if canGrantSliceCheckerCertified coverage replay checker then
        { requested := requested, granted := .slice_checker_certified, reason := "Replay and checker gates both closed with no blocked or unclassified families." }
      else if canGrantSliceReplayed coverage replay then
        { requested := requested, granted := .slice_replayed, reason := "Checker-certified gate failed; replay-only tier remains valid." }
      else
        { requested := requested, granted := .none, reason := "Neither replay nor checker tier is valid for this slice." }

end HeytingLean.KernelAssurance
