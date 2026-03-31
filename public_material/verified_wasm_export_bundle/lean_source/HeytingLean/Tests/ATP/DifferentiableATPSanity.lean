import HeytingLean.ATP.DifferentiableATP.GoalEncoder
import HeytingLean.ATP.DifferentiableATP.CombToExpr
import HeytingLean.ATP.DifferentiableATP.TacticDecoder
import HeytingLean.ATP.DifferentiableATP.ConvergenceOracle
import HeytingLean.ATP.DifferentiableATP.LensGDOrchestrator
import HeytingLean.ATP.DifferentiableATP.KernelVerifier
import HeytingLean.ATP.DifferentiableATP.FeedbackBridge
import HeytingLean.ATP.DifferentiableATP.CategoricalBridge
import HeytingLean.ATP.DifferentiableATP.TypeLoss
import HeytingLean.ATP.DifferentiableATP.OracleEncoder
import HeytingLean.ATP.DifferentiableATP.KANTacticSelector
import HeytingLean.ATP.DifferentiableATP.GraphNCA
import HeytingLean.ATP.DifferentiableATP.KANNCA
import HeytingLean.ATP.DifferentiableATP.SearchTree
import HeytingLean.PathIntegral.Adapter
import HeytingLean.LoF.Combinators.Differential.KAN

/-!
Compile-time sanity checks for the differentiable ATP extension modules.
-/

namespace HeytingLean
namespace Tests
namespace ATP

open HeytingLean.ATP.DifferentiableATP
open HeytingLean.LoF.Combinators.Differential
open HeytingLean.LoF.Combinators.Differential.Compute

#check encodeGoal
#check decodeFromWeights
#check ConvergenceOracle.evaluate
#check run
#check verify
#check buildPayload
#check encoderHom
#check diffATPTrainingStep
#check gradientDescentLoopRetracted
#check diffATPAsKoopmanNBA
#check psrLoss
#check structuralGoalHash
#check oracleEncode
#check HeytingLean.LoF.Combinators.Differential.Compute.toFormalSum
#check HeytingLean.LoF.Combinators.Differential.Compute.toFormalSum_app_single_single
#check HeytingLean.LoF.Combinators.Differential.Compute.normalize_idempotent
#check HeytingLean.LoF.Combinators.Differential.Compute.app_correspondence
#check HeytingLean.LoF.Combinators.Differential.Compute.dot_correspondence
#check HeytingLean.LoF.Combinators.Differential.Compute.steps_correspondence
#check HeytingLean.LoF.Combinators.Differential.Compute.stepsIter_correspondence
#check HeytingLean.LoF.Combinators.Differential.Compute.l2NormSq_nonneg
#check HeytingLean.LoF.Combinators.Differential.Compute.liftFeatures
#check HeytingLean.LoF.Combinators.Differential.Compute.exactStepIOCoordGrad
#check HeytingLean.LoF.Combinators.Differential.Compute.softL2Diff_nonneg
#check HeytingLean.LoF.Combinators.Differential.KAN.KANEdge.eval
#check HeytingLean.LoF.Combinators.Differential.KAN.KANetwork.forward
#check HeytingLean.LoF.Combinators.Differential.KAN.KANetwork.backward
#check decodeFromKANWeights
#check decodeFromKANWeightsWithGoal
#check runNCA
#check runKANNCA
#check hierarchicalSubgoalReward
#check trainKANOnEnrichedGoals
#check HeytingLean.PathIntegral.Adapter.searchNodeToProofState
#check HeytingLean.PathIntegral.Adapter.runPathIntegralSearch

example : (encodeGoal "⊢ True").examples.length = 1 := by
  decide

example : (encodeGoal "⊢ True").basis.length > 0 := by
  native_decide

example : structuralGoalHash "⊢ True" ≠ structuralGoalHash "⊢ False" := by
  native_decide

example : combToTactic .K = "exact True.intro" := by
  rfl

example : combToTactic .S = "simp" := by
  rfl

example : combToTactic .Y = "aesop" := by
  rfl

example : (decodeFromLearnedWeights (encodeGoal "⊢ True").initial 4 3).length > 0 := by
  native_decide

private def sampledTactics : List String :=
  [
    combToTactic .K,
    combToTactic .S,
    combToTactic .Y,
    combToTactic (.app .K .K),
    combToTactic (.app .K .S),
    combToTactic (.app .K .Y),
    combToTactic (.app .S .K),
    combToTactic (.app .S .S),
    combToTactic (.app .S .Y),
    combToTactic (.app .Y .K),
    combToTactic (.app .Y .S),
    combToTactic (.app .Y .Y),
    combToTactic (.app (.app .S .K) .K),
    combToTactic (.app (.app .S .K) .S),
    combToTactic (.app (.app .S .K) .Y),
    combToTactic (.app (.app .K .S) .K),
    combToTactic (.app (.app .K .S) .S),
    combToTactic (.app (.app .Y .K) .K)
  ]

example : sampledTactics.eraseDups.length ≥ 15 := by
  native_decide

example : (decodeFromKANWeights (encodeGoal "⊢ True").initial 4).length > 0 := by
  native_decide

example : (decodeFromKANWeightsWithGoal (encodeGoal "⊢ True").initial "⊢ True" 4).length > 0 := by
  native_decide

example :
    (runNCA defaultNCAUpdateRule (encodeGoal "⊢ True").initial 4 ((1 : Rat) / 1000)).candidates.length > 0 := by
  native_decide

example :
    (runNCA defaultNCAUpdateRule (encodeGoal "⊢ True").initial 4 ((1 : Rat) / 1000) (kanGoalFeatures "⊢ True")).candidates.length > 0 := by
  native_decide

example : (encodeGoal "⊢ True").basis.length ≥ 8 := by
  native_decide

example :
    (encodeGoal "⊢ ∀ n : Nat, n + 1 > n").initial ≠ (encodeGoal "⊢ True ∧ True").initial := by
  native_decide

private def countFeatureFlags (f : GoalFeatures) : Nat :=
  [f.hasForall, f.hasExists, f.hasArrow, f.hasIff, f.hasAnd, f.hasOr, f.hasNot, f.hasEq,
    f.hasNat, f.hasInt, f.hasReal, f.hasList, f.hasFinset, f.hasSet, f.hasPlus, f.hasMul, f.hasLt,
    f.hasLe, f.hasTrue, f.hasFalse, f.hasComposition, f.hasInduction].foldl
      (fun acc b => if b then acc + 1 else acc) 0

private def richGoal : String :=
  "⊢ ∀ n : Nat, ∃ m : Nat, ((n + 1 = m) ∧ (n < m)) ∨ ((¬ False) ↔ True)"

example : countFeatureFlags (goalFeatures richGoal) ≥ 10 := by
  native_decide

example : hierarchicalSubgoalReward 2 3 = ((2 : Rat) / 3) := by
  native_decide

example : hierarchicalSubgoalReward 3 3 = ((3 : Rat) / 3) + ((1 : Rat) / 2) := by
  native_decide

example : hierarchicalSubgoalReward 5 3 = ((3 : Rat) / 3) + ((1 : Rat) / 2) := by
  native_decide

example : hierarchicalSubgoalReward 0 0 = 0 := by
  native_decide

example : hierarchicalSubgoalReward 3 3 (compositionBonus := 1) = 2 := by
  native_decide

end ATP
end Tests
end HeytingLean
