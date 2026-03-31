import HeytingLean.Tests.KernelAssurance.ObligationFixture

namespace HeytingLean.Tests.KernelAssurance.Obligation

open Lean
open HeytingLean.KernelAssurance
open HeytingLean.Tests.KernelAssurance

example : familyOfVerificationMode "whnf_call" = .whnf := rfl
example : statusOfObligation supportedArtifact.obligations[0]! = .supported := rfl
example : statusOfObligation mixedArtifact.obligations[2]! = .blocked := rfl
example : statusOfObligation mixedArtifact.obligations[3]! = .unclassified := rfl

example : supportedArtifact.obligationsTotal = 3 := rfl
example : supportedArtifact.omittedTraceEntries = 0 := rfl

example : (ObligationCoverageReport.ofBundle supportedObligationBundle).blockedObligations = 0 := by native_decide
example : (ObligationCoverageReport.ofBundle mixedObligationBundle).blockedObligations = 1 := by native_decide
example : (ObligationCoverageReport.ofBundle mixedObligationBundle).unclassifiedObligations = 1 := by native_decide

example :
    (ObligationCoverageReport.ofBundleWithSourcePayload
      sourceScopeBundle (some sourceScopePayload)).discoveredObligations = 2 := by
  native_decide

example :
    (ObligationCoverageReport.ofBundleWithSourcePayload
      sourceScopeBundle (some sourceScopePayload)).exportedObligations = 1 := by
  native_decide

example :
    (ObligationCoverageReport.ofBundleWithSourcePayload
      sourceScopeBundle (some sourceScopePayload)).blockedObligations = 1 := by
  native_decide

example : (ObligationReplayReport.ofBundle supportedObligationBundle).failed = 0 := by native_decide
example : (ObligationReplayReport.ofBundle mixedObligationBundle).skippedBlocked = 1 := by native_decide
example : (ObligationReplayReport.ofBundle mixedObligationBundle).skippedUnclassified = 1 := by native_decide

example : (ObligationCheckerReport.ofBundle supportedObligationBundle).failed = 0 := by native_decide
example : (ObligationCheckerReport.ofBundle tamperedObligationBundle).tamperFailures > 0 := by native_decide

example :
    (decideObligationTier
      .slice_checker_certified
      (ObligationCoverageReport.ofBundle supportedObligationBundle)
      (ObligationReplayReport.ofBundle supportedObligationBundle)
      (ObligationCheckerReport.ofBundle supportedObligationBundle)).granted = .slice_checker_certified := by
  native_decide

example :
    (decideObligationTier
      .slice_checker_certified
      (ObligationCoverageReport.ofBundle mixedObligationBundle)
      (ObligationReplayReport.ofBundle mixedObligationBundle)
      (ObligationCheckerReport.ofBundle mixedObligationBundle)).granted = .slice_replayed := by
  native_decide

example :
    (decideObligationTier
      .slice_checker_certified
      (ObligationCoverageReport.ofBundleWithSourcePayload
        sourceScopeBundle (some sourceScopePayload))
      (ObligationReplayReport.ofBundle sourceScopeBundle)
      (ObligationCheckerReport.ofBundle sourceScopeBundle)).granted = .none := by
  native_decide

end HeytingLean.Tests.KernelAssurance.Obligation
