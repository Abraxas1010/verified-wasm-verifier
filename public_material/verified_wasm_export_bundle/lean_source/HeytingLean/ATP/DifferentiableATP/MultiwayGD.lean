import HeytingLean.ATP.DifferentiableATP.CoreOps
import HeytingLean.ATP.DifferentiableATP.SheafResolution
import HeytingLean.ATP.DifferentiableATP.SheafTransport
import HeytingLean.ATP.DifferentiableATP.CategoricalBridge
import HeytingLean.ATP.DifferentiableATP.TacticDecoder
import HeytingLean.LoF.Combinators.Differential.Loss
import HeytingLean.Embeddings.CrossLensTransport

/-!
# ATP.DifferentiableATP.MultiwayGD

Lock-and-continue macro loop over the step-based multiway objective.
-/

namespace HeytingLean
namespace ATP
namespace DifferentiableATP

open HeytingLean.Embeddings
open HeytingLean.LoF
open HeytingLean.LoF.Combinators.Differential
open HeytingLean.LoF.Combinators.Differential.Compute

structure MacroConfig where
  maxMacroSteps : Nat := 5
  innerIterations : Nat := 20
  lockTopK : Nat := 6
  simplifyDepth : Nat := 3
  stepFuel : Nat := 1
  softKernelDepth : Nat := 3
  learningRate : Rat := (1 : Rat) / 5
  simplicityWeight : Rat := (1 : Rat) / 100
  tacticScoreWeight : Rat := (1 : Rat) / 50
  tacticTopK : Nat := 4
  convergenceThreshold : Rat := (1 : Rat) / 100
  exactGradient : Bool := true
  useLearnedTactics : Bool := false
  useReachLoss : Bool := false
  reachFuel : Nat := 2
  reachWeight : Rat := (1 : Rat) / 10
  deriving Repr

structure MacroState where
  currentState : FSum
  examples : List IOExample
  lockedHistory : List FSum
  macroStep : Nat
  lossHistory : List Rat
  converged : Bool
  reason : String

/-- Simplify dominant terms and lock as the next macro state. -/
def lockAndSimplify (topK simplifyDepth : Nat) (state : FSum) : FSum :=
  pruneFSum (max 1 topK) (threshold := (1 : Rat) / 1000) (simplifyFSum simplifyDepth state)

private def stepGDLoop
    (depth fuel : Nat)
    (exactGradient : Bool)
    (simplicityWeight : Rat)
    (tacticScoreWeight : Rat)
    (tacticTopK : Nat)
    (useLearnedTactics : Bool)
    (useReachLoss : Bool)
    (reachFuel : Nat)
    (reachWeight : Rat)
    (lr : Rat)
    (params : List Comb)
    (maxIter : Nat)
    (state : FSum)
    (examples : List IOExample) : GDState :=
  let rec go : Nat → Nat → FSum → List Rat → GDState
    | 0, iter, w, lossHist =>
        let base := combinedStepIOLoss depth fuel simplicityWeight w examples
        let tacticAux :=
          if useLearnedTactics then
            tacticScoreWeight * tacticScoreLoss w defaultLearnedTacticEntries (max 1 tacticTopK) depth
          else
            0
        let reachAux :=
          if useReachLoss then
            reachWeight * reachLossDataset (max 1 reachFuel) w examples
          else
            0
        let l := base + tacticAux + reachAux
        { iteration := iter, currentWeights := w, currentLoss := l, lossHistory := (l :: lossHist).reverse }
    | Nat.succ remaining, iter, w, lossHist =>
        let base := combinedStepIOLoss depth fuel simplicityWeight w examples
        let tacticAux :=
          if useLearnedTactics then
            tacticScoreWeight * tacticScoreLoss w defaultLearnedTacticEntries (max 1 tacticTopK) depth
          else
            0
        let reachAux :=
          if useReachLoss then
            reachWeight * reachLossDataset (max 1 reachFuel) w examples
          else
            0
        let l := base + tacticAux + reachAux
        let ioGrad :=
          if exactGradient then
            exactStepIOCoordGrad depth fuel params w examples
          else
            stepIOCoordGrad depth fuel params w examples
        let simplicityGrad := simplicityCoordGrad params w
        let tacticGrad :=
          if useLearnedTactics then
            tacticScoreLossGrad params w defaultLearnedTacticEntries (max 1 tacticTopK) depth
          else
            []
        let reachGrad :=
          if useReachLoss then
            reachCoordGrad (max 1 reachFuel) params w examples
          else
            []
        let grad :=
          add ioGrad (add (smul simplicityWeight simplicityGrad)
            (add (smul tacticScoreWeight tacticGrad) (smul reachWeight reachGrad)))
        let truncGrad := grad.map (fun tc => (tc.1, truncRat tc.2))
        let w' := (sub w (smul lr truncGrad)).map (fun tc => (tc.1, truncRat tc.2))
        go remaining (iter + 1) w' (l :: lossHist)
  go (max 1 maxIter) 0 (projectToFixedWeights nucleusR state) []

private def runInnerGD
    (cfg : MacroConfig)
    (params : List Comb)
    (state : FSum)
    (examples : List IOExample) : GDState :=
  stepGDLoop
    (max 1 cfg.softKernelDepth)
    (max 1 cfg.stepFuel)
    cfg.exactGradient
    cfg.simplicityWeight
    cfg.tacticScoreWeight
    (max 1 cfg.tacticTopK)
    cfg.useLearnedTactics
    cfg.useReachLoss
    (max 1 cfg.reachFuel)
    cfg.reachWeight
    cfg.learningRate
    params
    (max 1 cfg.innerIterations)
    state
    examples

private def macroStepFn (cfg : MacroConfig) (params : List Comb) (ms : MacroState) : MacroState :=
  let gdResult := runInnerGD cfg params ms.currentState ms.examples
  let finalLoss := gdResult.currentLoss
  let locked := lockAndSimplify cfg.lockTopK cfg.simplifyDepth gdResult.currentWeights
  let improved :=
    match ms.lossHistory with
    | [] => true
    | prevLoss :: _ => finalLoss < prevLoss
  let converged := finalLoss ≤ cfg.convergenceThreshold
  {
    currentState := locked
    examples := ms.examples
    lockedHistory := locked :: ms.lockedHistory
    macroStep := ms.macroStep + 1
    lossHistory := finalLoss :: ms.lossHistory
    converged := converged
    reason := if converged then "target_reached" else if !improved then "no_improvement" else "in_progress"
  }

def multiwayMacroLoop
    (cfg : MacroConfig)
    (params : List Comb)
    (initial : FSum)
    (examples : List IOExample) : MacroState :=
  let init : MacroState :=
    {
      currentState := initial
      examples := examples
      lockedHistory := []
      macroStep := 0
      lossHistory := []
      converged := false
      reason := "starting"
    }
  let rec go : Nat → MacroState → MacroState
    | 0, ms =>
        if ms.converged then ms else { ms with reason := "macro_budget_exhausted" }
    | Nat.succ fuel, ms =>
        if ms.converged then
          ms
        else
          let ms' := macroStepFn cfg params ms
          if ms'.converged || ms'.reason = "no_improvement" then ms' else go fuel ms'
  go (max 1 cfg.maxMacroSteps) init

/-- Transport macro state across lenses and retry macro optimization. -/
def multiwayTransportAndRetry
    (cfg : MacroConfig)
    (ms : MacroState)
    (currentLens nextLens : LensID)
    (useSheafTransport : Bool) : MacroState :=
  let transported :=
    if useSheafTransport then
      LaxCrossLensTransport.forward sheafTransport currentLens nextLens ms.currentState
    else
      CrossLensTransport.forward categoricalTransport currentLens nextLens ms.currentState
  let newParams := basisForLens nextLens
  multiwayMacroLoop cfg newParams transported ms.examples

private def dedupByTactic (rows : List DecodedCandidate) : List DecodedCandidate :=
  rows.foldl
    (fun acc row => if acc.any (fun x => x.tactic = row.tactic) then acc else acc ++ [row])
    []

/-- Decode top multiway-optimized terms directly into tactic candidates. -/
def extractTacticCandidates (topK : Nat) (state : FSum) : List DecodedCandidate :=
  let rows := decodeFromLearnedWeights state (max 1 topK) 3
  let merged := dedupByTactic rows
  if merged.isEmpty then [decodeComb .K, decodeComb .S] else merged

end DifferentiableATP
end ATP
end HeytingLean
