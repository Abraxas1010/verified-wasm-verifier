import HeytingLean.ATP.DifferentiableATP.ClosedLoopSynthesis

/-!
Compile-time sanity checks for closed-loop differentiable ATP synthesis.
-/

namespace HeytingLean
namespace Tests
namespace ATP

open HeytingLean.ATP.DifferentiableATP

#check feedbackFromVerification
#check rewardShapingHints
#check closedLoopRun

private def vrOk : VerificationResult :=
  {
    ok := true
    verifiedTactic := some "exact True.intro"
    attempts := [
      {
        tactic := "exact True.intro"
        wrapperPath := ".tmp/test.lean"
        rc := 0
        ok := true
        stdout := ""
        stderr := ""
      }
    ]
    reason := "kernel_verified"
  }

private def vrFail : VerificationResult :=
  {
    ok := false
    verifiedTactic := none
    attempts := [
      {
        tactic := "simp"
        wrapperPath := ".tmp/test1.lean"
        rc := 1
        ok := false
        stdout := ""
        stderr := "failed"
      },
      {
        tactic := "aesop"
        wrapperPath := ".tmp/test2.lean"
        rc := 1
        ok := false
        stdout := ""
        stderr := "failed"
      }
    ]
    reason := "no_candidate_verified"
  }

example : (feedbackFromVerification vrOk).verified = true := rfl

example : "exact" ∈ rewardShapingHints {} (feedbackFromVerification vrOk) [] 0 := by
  native_decide

example : (rewardShapingHints {} (feedbackFromVerification vrFail) [] 0).length > 0 := by
  native_decide

end ATP
end Tests
end HeytingLean
