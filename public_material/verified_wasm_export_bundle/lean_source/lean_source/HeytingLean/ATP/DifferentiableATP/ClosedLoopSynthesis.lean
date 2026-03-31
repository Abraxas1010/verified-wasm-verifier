import HeytingLean.ATP.DifferentiableATP.GoalEncoder
import HeytingLean.ATP.DifferentiableATP.KernelVerifier
import HeytingLean.ATP.DifferentiableATP.LensGDOrchestrator

/-!
# ATP.DifferentiableATP.ClosedLoopSynthesis

Closed-loop differentiable synthesis:
open-loop run -> kernel verification -> feedback shaping -> rerun.
-/

namespace HeytingLean
namespace ATP
namespace DifferentiableATP

open HeytingLean.Embeddings

structure VerifierFeedback where
  verified : Bool
  verifiedTactic : Option String
  failedTactics : List String
  attemptCount : Nat
  deriving Repr

def feedbackFromVerification (vr : VerificationResult) : VerifierFeedback :=
  {
    verified := vr.ok
    verifiedTactic := vr.verifiedTactic
    failedTactics := (vr.attempts.filter (fun a => !a.ok)).map (fun a => a.tactic)
    attemptCount := vr.attempts.length
  }

private def hintAllowedChar (c : Char) : Bool :=
  c.isAlphanum || c = '.' || c = '_' || c = '\''

private def normalizeHint (hint : String) : String :=
  hint.trim

private def validHint (hint : String) : Bool :=
  let h := normalizeHint hint
  !h.isEmpty && h.data.all hintAllowedChar

private def tacticTokens (tactic : String) : List String :=
  let words := tactic.split (fun c => c.isWhitespace || c = '[' || c = ']' || c = '(' || c = ')' || c = ',' || c = ':')
  ((words.map normalizeHint).filter validHint).eraseDups

structure ClosedLoopConfig where
  maxVerifyRounds : Nat := 3
  gdStepsPerRound : Nat := 10
  rewardDecay : Rat := (1 : Rat) / 2
  hintBudget : Nat := 6
  deriving Repr

private def roundHintBudget (cfg : ClosedLoopConfig) (round : Nat) : Nat :=
  let base := max 1 cfg.hintBudget
  if cfg.rewardDecay < 1 then
    max 1 (base / (round + 1))
  else
    base

def rewardShapingHints
    (cfg : ClosedLoopConfig)
    (feedback : VerifierFeedback)
    (contextHints : List String)
    (round : Nat) : List String :=
  let boosted : List String :=
    if feedback.verified then
      match feedback.verifiedTactic with
      | some tac => tacticTokens tac
      | none => []
    else
      let failures :=
        (feedback.failedTactics.foldl (fun acc tac => acc ++ tacticTokens tac) []).eraseDups
      if failures.isEmpty then ["simp", "aesop"] else failures
  let limited := boosted.take (roundHintBudget cfg round)
  ((contextHints.map normalizeHint).filter validHint ++ limited).eraseDups

structure ClosedLoopRound where
  round : Nat
  contextHints : List String
  run : Result
  verifier : VerificationResult
  feedback : VerifierFeedback

structure ClosedLoopResult where
  proved : Bool
  reason : String
  verifiedTactic : Option String
  openLoopResult : Result
  openLoopVerification : VerificationResult
  rounds : List ClosedLoopRound
  totalGDSteps : Nat
  totalVerifyAttempts : Nat
  finalRun : Result
  finalVerification : VerificationResult

private def runRound
    (goal : String)
    (cfg : OrchestratorConfig)
    (round : Nat)
    (contextHints : List String) : IO ClosedLoopRound := do
  let runResult := run goal cfg contextHints
  let verifier ← verify goal runResult.bestCandidates cfg.decodeTopK
  let fb := feedbackFromVerification verifier
  pure {
    round := round
    contextHints := contextHints
    run := runResult
    verifier := verifier
    feedback := fb
  }

def closedLoopRun
    (goal : String)
    (cfg : OrchestratorConfig := {})
    (clCfg : ClosedLoopConfig := {})
    (contextHints : List String := []) : IO ClosedLoopResult := do
  let openRun := run goal cfg contextHints
  let openVerifier ← verify goal openRun.bestCandidates cfg.decodeTopK
  if openVerifier.ok then
    return {
      proved := true
      reason := "open_loop_verified"
      verifiedTactic := openVerifier.verifiedTactic
      openLoopResult := openRun
      openLoopVerification := openVerifier
      rounds := []
      totalGDSteps := 0
      totalVerifyAttempts := openVerifier.attempts.length
      finalRun := openRun
      finalVerification := openVerifier
    }

  let roundCfg : OrchestratorConfig := { cfg with maxIterations := max 1 clCfg.gdStepsPerRound }
  let rec go
      (fuel : Nat)
      (round : Nat)
      (hints : List String)
      (revRounds : List ClosedLoopRound)
      (lastRun : Result)
      (lastVerifier : VerificationResult) : IO (List ClosedLoopRound × Result × VerificationResult) := do
    match fuel with
    | 0 => pure (revRounds.reverse, lastRun, lastVerifier)
    | Nat.succ fuel' => do
        let one ← runRound goal roundCfg round hints
        if one.feedback.verified then
          pure ((one :: revRounds).reverse, one.run, one.verifier)
        else
          let nextHints := rewardShapingHints clCfg one.feedback hints round
          go fuel' (round + 1) nextHints (one :: revRounds) one.run one.verifier
  termination_by fuel

  let (rounds, finalRun, finalVerifier) ← go clCfg.maxVerifyRounds 0 contextHints [] openRun openVerifier
  let totalAttempts :=
    openVerifier.attempts.length +
      rounds.foldl (fun acc r => acc + r.feedback.attemptCount) 0
  let totalSteps := rounds.length * (max 1 clCfg.gdStepsPerRound)
  let proved := finalVerifier.ok
  let reason :=
    if proved then
      "closed_loop_verified"
    else if rounds.isEmpty then
      "closed_loop_exhausted_no_rounds"
    else
      "closed_loop_exhausted"
  return {
    proved := proved
    reason := reason
    verifiedTactic := finalVerifier.verifiedTactic
    openLoopResult := openRun
    openLoopVerification := openVerifier
    rounds := rounds
    totalGDSteps := totalSteps
    totalVerifyAttempts := totalAttempts
    finalRun := finalRun
    finalVerification := finalVerifier
  }

end DifferentiableATP
end ATP
end HeytingLean
