import HeytingLean.ATP.DifferentiableATP.TacticDecoder
import HeytingLean.ATP.DifferentiableATP.GoalEncoder
import HeytingLean.LoF.Combinators.Rewriting.StepAtCompute

/-!
# ATP.DifferentiableATP.GraphNCA

Track B runtime surface:
- graph NCA over SKY reduction neighborhoods,
- local update/grow/prune loop,
- tactic extraction from stable high-mass cells.
-/

namespace HeytingLean
namespace ATP
namespace DifferentiableATP

open HeytingLean.LoF
open HeytingLean.LoF.Combinators.Differential
open HeytingLean.LoF.Combinators.Differential.Compute

private def clamp01 (r : Rat) : Rat :=
  if r < 0 then 0 else if r > 1 then 1 else r

private def arrayGetRat (xs : Array Rat) (i : Nat) : Rat :=
  xs.getD i 0

private def vecAdd (a b : Array Rat) : Array Rat :=
  ((List.range (max a.size b.size)).map (fun i => a.getD i 0 + b.getD i 0)).toArray

private def vecScale (r : Rat) (a : Array Rat) : Array Rat :=
  a.map (fun x => r * x)

private def vecMean (rows : List (Array Rat)) (dim : Nat) : Array Rat :=
  if rows.isEmpty then
    Array.replicate dim 0
  else
    let summed := rows.foldl (fun acc row => vecAdd acc row) (Array.replicate dim 0)
    vecScale ((1 : Rat) / (Int.ofNat rows.length : Rat)) summed

private def listSumRat (xs : List Rat) : Rat :=
  xs.foldl (fun acc x => acc + x) 0

private def boolToRat (b : Bool) : Rat :=
  if b then 1 else 0

/-- Goal-conditioned NCA feature signal (compact and stable over textual goals). -/
def ncaGoalFeaturesFromGoal (goal : String) : Array Rat :=
  let f := goalFeatures goal
  #[
    boolToRat f.hasForall,
    boolToRat f.hasExists,
    boolToRat f.hasArrow + boolToRat f.hasIff,
    boolToRat f.hasAnd + boolToRat f.hasOr + boolToRat f.hasNot,
    boolToRat f.hasEq,
    boolToRat f.hasNat,
    boolToRat f.hasInt,
    boolToRat f.hasReal,
    boolToRat f.hasPlus,
    boolToRat f.hasMul,
    boolToRat f.hasLt + boolToRat f.hasLe,
    boolToRat f.hasPow,
    (Int.ofNat f.quantifierDepth : Rat) / 5,
    (Int.ofNat (f.tokenCount % 11) : Rat) / 10
  ]

structure NCACell where
  term : Comb
  weight : Rat
  features : Array Rat
  tacticLogits : Array Rat
  alive : Rat
  age : Nat
  deriving Repr

structure NCAState where
  cells : List NCACell
  step : Nat
  goalFeatures : Array Rat
  deriving Repr

structure NCAUpdateRule where
  featureDim : Nat := 14
  tacticDim : Nat := 8
  decayRate : Rat := (1 : Rat) / 20
  growthScale : Rat := (1 : Rat) / 10
  aliveThreshold : Rat := (1 : Rat) / 10
  maxCells : Nat := 64
  deriving Repr

def defaultNCAUpdateRule : NCAUpdateRule := {}

structure NCAPerturbConfig where
  step : Nat := 0
  dropAlive : Rat := (1 : Rat) / 3
  seed : Nat := 0
  deriving Repr

structure LearnableNCAUpdateRule where
  base : NCAUpdateRule := defaultNCAUpdateRule
  senseWeights : Array Rat := #[1, 1, 1, 1]
  updateWeights : Array Rat := #[1, 1, 1, 1]
  growthWeights : Array Rat := #[1, 1]
  deriving Repr

def defaultLearnableNCAUpdateRule : LearnableNCAUpdateRule := {}

private def initCell (rule : NCAUpdateRule) (t : Comb) (w : Rat := 1) : NCACell :=
  {
    term := t
    weight := w
    features := Array.replicate (max 1 rule.featureDim) 0
    tacticLogits := Array.replicate (max 1 rule.tacticDim) 0
    alive := 1
    age := 0
  }

private def findCellByTerm? (cells : List NCACell) (t : Comb) : Option NCACell :=
  cells.find? (fun c => c.term = t)

/-- Local perception: aggregate one-step successor neighborhood statistics. -/
def perceiveNeighbors (rule : NCAUpdateRule) (state : NCAState) (cell : NCACell) : Array Rat :=
  let succTerms := (Comb.stepEdgesList cell.term).map Prod.snd
  let neighbors := succTerms.filterMap (fun t => findCellByTerm? state.cells t)
  let dim := max 3 rule.featureDim
  if neighbors.isEmpty then
    Array.replicate dim 0
  else
    let meanFeat := vecMean (neighbors.map (fun c => c.features)) dim
    let meanWeight := listSumRat (neighbors.map (fun c => absRat c.weight)) / (Int.ofNat neighbors.length : Rat)
    let meanAlive := listSumRat (neighbors.map (fun c => clamp01 c.alive)) / (Int.ofNat neighbors.length : Rat)
    let count := (Int.ofNat neighbors.length : Rat)
    meanFeat.set! 0 meanWeight |>.set! 1 meanAlive |>.set! 2 count

private def blendFeatures (old perceived : Array Rat) : Array Rat :=
  let dim := max old.size perceived.size
  ((List.range dim).map (fun i =>
    let a := old.getD i 0
    let b := perceived.getD i 0
    (a + b) / 2)).toArray

def NCAUpdateRule.apply
    (rule : NCAUpdateRule)
    (cell : NCACell)
    (perception : Array Rat)
    (goalFeatures : Array Rat) : NCACell :=
  let meanW := arrayGetRat perception 0
  let meanAlive := arrayGetRat perception 1
  let goalW := arrayGetRat goalFeatures 0
  let goalAlive := arrayGetRat goalFeatures 1
  let newWeight := (1 - rule.decayRate) * cell.weight + rule.growthScale * meanW + (rule.growthScale / 4) * goalW
  let newAlive := clamp01 ((1 - rule.decayRate) * cell.alive + (rule.growthScale * meanAlive) + (rule.growthScale / 2) * goalAlive)
  let newFeatures := blendFeatures (blendFeatures cell.features perception) goalFeatures
  let newLogits := blendFeatures cell.tacticLogits newFeatures
  {
    cell with
    weight := newWeight
    alive := newAlive
    features := newFeatures
    tacticLogits := newLogits
    age := cell.age + 1
  }

private def perturbCellsAux
    (cells : List NCACell)
    (drop : Rat)
    (seed : Nat)
    (idx : Nat := 0) : List NCACell :=
  match cells with
  | [] => []
  | c :: tl =>
      let hit := ((idx + seed) % 2 = 0)
      let c' :=
        if hit then
          {
            c with
            alive := clamp01 (c.alive * (1 - drop))
            weight := c.weight * (1 - drop / 2)
          }
        else
          c
      c' :: perturbCellsAux tl drop seed (idx + 1)

private def perturbState (state : NCAState) (cfg : NCAPerturbConfig) : NCAState :=
  { state with cells := perturbCellsAux state.cells (clamp01 cfg.dropAlive) cfg.seed }

private def learnWeight (xs : Array Rat) (i : Nat) : Rat :=
  xs.getD i 1

private def weightedPerception (rule : LearnableNCAUpdateRule) (state : NCAState) (cell : NCACell) : Array Rat :=
  let p := perceiveNeighbors rule.base state cell
  let s0 := learnWeight rule.senseWeights 0
  let s1 := learnWeight rule.senseWeights 1
  let s2 := learnWeight rule.senseWeights 2
  let s3 := learnWeight rule.senseWeights 3
  let baseMean := (arrayGetRat p 0 + arrayGetRat p 1 + arrayGetRat p 2) / 3
  p.set! 0 (s0 * arrayGetRat p 0)
    |>.set! 1 (s1 * arrayGetRat p 1)
    |>.set! 2 (s2 * arrayGetRat p 2)
    |>.set! 3 (s3 * baseMean)

private def learnableApply
    (rule : LearnableNCAUpdateRule)
    (cell : NCACell)
    (perception : Array Rat)
    (goalFeatures : Array Rat) : NCACell :=
  let meanW := arrayGetRat perception 0
  let meanAlive := arrayGetRat perception 1
  let goalW := arrayGetRat goalFeatures 0
  let goalAlive := arrayGetRat goalFeatures 1
  let u0 := learnWeight rule.updateWeights 0
  let u1 := learnWeight rule.updateWeights 1
  let u2 := learnWeight rule.updateWeights 2
  let u3 := learnWeight rule.updateWeights 3
  let g0 := learnWeight rule.growthWeights 0
  let g1 := learnWeight rule.growthWeights 1
  let newWeight :=
    (1 - rule.base.decayRate) * cell.weight
      + rule.base.growthScale * (u0 * meanW + u1 * goalW)
  let newAlive :=
    clamp01 ((1 - rule.base.decayRate) * cell.alive + rule.base.growthScale * (u2 * meanAlive + u3 * goalAlive))
  let blendedGoal := blendFeatures cell.features goalFeatures
  let growthMean := (g0 + g1) / 2
  let newFeatures := blendFeatures (blendFeatures blendedGoal perception) (Array.replicate blendedGoal.size growthMean)
  let newLogits := blendFeatures cell.tacticLogits newFeatures
  {
    cell with
    weight := newWeight
    alive := newAlive
    features := newFeatures
    tacticLogits := newLogits
    age := cell.age + 1
  }

private def learnableSpawnFromCell
    (rule : LearnableNCAUpdateRule)
    (cells : List NCACell)
    (cell : NCACell) : List NCACell :=
  let succTerms := (Comb.stepEdgesList cell.term).map Prod.snd
  let growth := learnWeight rule.growthWeights 0
  succTerms.filterMap (fun t =>
    if cells.any (fun c => c.term = t) then
      none
    else
      some (initCell rule.base t ((cell.weight * rule.base.growthScale * growth) / 2)))

def learnableNCAStep (rule : LearnableNCAUpdateRule) (state : NCAState) : NCAState :=
  let updated := state.cells.map (fun c => learnableApply rule c (weightedPerception rule state c) state.goalFeatures)
  let seeded := updated.foldl (fun acc c => acc ++ learnableSpawnFromCell rule acc c) updated
  let trimmed := seeded.take (max 1 rule.base.maxCells)
  let pruned := trimmed.filter (fun c => c.alive >= rule.base.aliveThreshold)
  { state with cells := pruned, step := state.step + 1 }

private def spawnFromCell (rule : NCAUpdateRule) (cells : List NCACell) (cell : NCACell) : List NCACell :=
  let succTerms := (Comb.stepEdgesList cell.term).map Prod.snd
  succTerms.filterMap (fun t =>
    if cells.any (fun c => c.term = t) then
      none
    else
      some (initCell rule t ((cell.weight * rule.growthScale) / 2)))

def growCells (rule : NCAUpdateRule) (state : NCAState) : NCAState :=
  let seeded := state.cells.foldl (fun acc c => acc ++ spawnFromCell rule acc c) state.cells
  let trimmed := seeded.take (max 1 rule.maxCells)
  { state with cells := trimmed }

def pruneCells (state : NCAState) (threshold : Rat) : NCAState :=
  { state with cells := state.cells.filter (fun c => c.alive >= threshold) }

def ncaStep (rule : NCAUpdateRule) (state : NCAState) : NCAState :=
  let updated := state.cells.map (fun c => rule.apply c (perceiveNeighbors rule state c) state.goalFeatures)
  let grown := growCells rule { state with cells := updated, step := state.step + 1 }
  pruneCells grown rule.aliveThreshold

private def totalMass (state : NCAState) : Rat :=
  listSumRat (state.cells.map (fun c => absRat (c.weight * c.alive)))

def isStable (prev curr : NCAState) (tolerance : Rat) : Bool :=
  absRat (totalMass curr - totalMass prev) ≤ tolerance

private def rankCellInsert (x : NCACell × Rat) : List (NCACell × Rat) → List (NCACell × Rat)
  | [] => [x]
  | hd :: tl =>
      if x.2 > hd.2 then x :: hd :: tl else hd :: rankCellInsert x tl

def extractTactics (state : NCAState) (topK : Nat := 4) : List DecodedCandidate :=
  let ranked :=
    state.cells.foldl
      (fun acc c => rankCellInsert (c, absRat (c.weight * c.alive)) acc)
      []
  let rows := (ranked.take (max 1 topK)).map (fun row =>
    {
      comb := row.1.term
      tactic := combToTactic row.1.term
      source := s!"graph_nca::{combName row.1.term}"
      confidence := row.2
    })
  if rows.isEmpty then [decodeComb .K, decodeComb .S] else rows

structure NCAOutcome where
  finalState : NCAState
  converged : Bool
  stepsUsed : Nat
  stabilityScore : Rat
  candidates : List DecodedCandidate
  deriving Repr

def initNCAState (rule : NCAUpdateRule) (seed : FSum) (goalFeatures : Array Rat := #[]) : NCAState :=
  let cells :=
    if seed.isEmpty then
      [initCell rule .K 1]
    else
      (seed.take (max 1 rule.maxCells)).map (fun tc => initCell rule tc.1 tc.2)
  { cells := cells, step := 0, goalFeatures := goalFeatures }

def runNCA
    (rule : NCAUpdateRule)
    (seed : FSum)
    (maxSteps : Nat := 12)
    (tolerance : Rat := (1 : Rat) / 1000)
    (goalFeatures : Array Rat := #[])
    (perturb : Option NCAPerturbConfig := none) : NCAOutcome :=
  let init := initNCAState rule seed goalFeatures
  let rec go : Nat → Nat → NCAState → NCAState → Bool × Nat × NCAState
    | 0, used, _prev, curr => (true, used, curr)
    | Nat.succ fuel, used, _prev, curr =>
        let curr' :=
          match perturb with
          | some p =>
              if used = p.step then perturbState curr p else curr
          | none => curr
        let next := ncaStep rule curr'
        if isStable curr' next tolerance then
          (true, used + 1, next)
        else
          go fuel (used + 1) curr next
  let (ok, steps, final) := go (max 1 maxSteps) 0 init init
  let score := if ok then 1 else (1 : Rat) / (Int.ofNat (steps + 1) : Rat)
  {
    finalState := final
    converged := ok
    stepsUsed := steps
    stabilityScore := score
    candidates := extractTactics final 4
  }

private def tacticScore (expected : String) (rows : List DecodedCandidate) : Rat :=
  let score :=
    rows.foldl
      (fun acc row =>
        if row.tactic = expected then
          max acc (row.confidence / (1 + absRat row.confidence))
        else
          acc)
      0
  clamp01 score

private def trainingLoss
    (rule : LearnableNCAUpdateRule)
    (samples : List (String × String))
    (maxSteps : Nat := 10)
    (tol : Rat := (1 : Rat) / 1000) : Rat :=
  if samples.isEmpty then
    0
  else
    let total :=
      samples.foldl
        (fun acc sample =>
          let goal := sample.1
          let expected := sample.2
          let enc := encodeGoal goal .omega [] none
          let init := initNCAState rule.base enc.initial (ncaGoalFeaturesFromGoal goal)
          let rec go : Nat → NCAState → NCAState
            | 0, curr => curr
            | Nat.succ fuel, curr =>
                let next := learnableNCAStep rule curr
                if isStable curr next tol then next else go fuel next
          let final := go (max 1 maxSteps) init
          let score := tacticScore expected (extractTactics final 4)
          let miss := 1 - score
          acc + miss * miss)
        0
    total / (Int.ofNat samples.length : Rat)

structure TrainingTraceEntry where
  iteration : Nat
  lossBefore : Rat
  gradNorms : Array Rat
  paramsBefore : Array Rat
  paramsAfter : Array Rat
  deriving Repr

private def learnableParams (rule : LearnableNCAUpdateRule) : Array Rat :=
  rule.senseWeights ++ rule.updateWeights ++ rule.growthWeights

private def setLearnableParam (rule : LearnableNCAUpdateRule) (idx : Nat) (value : Rat) : LearnableNCAUpdateRule :=
  let ns := rule.senseWeights.size
  let nu := rule.updateWeights.size
  if idx < ns then
    { rule with senseWeights := rule.senseWeights.set! idx value }
  else if idx < ns + nu then
    { rule with updateWeights := rule.updateWeights.set! (idx - ns) value }
  else
    { rule with growthWeights := rule.growthWeights.set! (idx - ns - nu) value }

def trainNCARule
    (samples : List (String × String))
    (base : LearnableNCAUpdateRule := defaultLearnableNCAUpdateRule)
    (iterations : Nat := 12)
    (learningRate : Rat := (1 : Rat) / 100)
    (epsilon : Rat := (1 : Rat) / 1000)
    (sampleBudget : Nat := 9)
    (paramBudget : Nat := 10)
    (lossMaxSteps : Nat := 10) : LearnableNCAUpdateRule × Rat × List TrainingTraceEntry :=
  let eps := if epsilon = 0 then (1 : Rat) / 1000 else epsilon
  let cappedSamples :=
    if samples.isEmpty then
      samples
    else
      samples.take (max 1 sampleBudget)
  let cappedIters := max 1 iterations
  let rec trainIter : Nat → Nat → LearnableNCAUpdateRule → List TrainingTraceEntry →
      LearnableNCAUpdateRule × List TrainingTraceEntry
    | 0, _, rule, trace => (rule, trace.reverse)
    | Nat.succ fuel, iterIdx, rule, trace =>
        let params := learnableParams rule
        let paramCount := min params.size (max 1 paramBudget)
        let lossBefore := trainingLoss rule cappedSamples (max 1 lossMaxSteps)
        let paramsBefore := params.extract 0 paramCount
        let (updated, grads) :=
          (List.range paramCount).foldl
            (fun (acc : LearnableNCAUpdateRule × Array Rat) i =>
              let (r, gs) := acc
              let pi := (learnableParams r).getD i 0
              let rPlus := setLearnableParam r i (pi + eps)
              let rMinus := setLearnableParam r i (pi - eps)
              let lPlus := trainingLoss rPlus cappedSamples (max 1 lossMaxSteps)
              let lMinus := trainingLoss rMinus cappedSamples (max 1 lossMaxSteps)
              let grad := truncRat ((lPlus - lMinus) / (2 * eps))
              (setLearnableParam r i (truncRat (pi - learningRate * grad)), gs.push grad))
            (rule, #[])
        let paramsAfter := (learnableParams updated).extract 0 paramCount
        let entry : TrainingTraceEntry :=
          { iteration := iterIdx
            lossBefore := lossBefore
            gradNorms := grads
            paramsBefore := paramsBefore
            paramsAfter := paramsAfter }
        trainIter fuel (iterIdx + 1) updated (entry :: trace)
  let (trained, trace) := trainIter cappedIters 0 base []
  let loss := trainingLoss trained cappedSamples (max 1 lossMaxSteps)
  (trained, loss, trace)

def runLearnableNCA
    (rule : LearnableNCAUpdateRule)
    (seed : FSum)
    (maxSteps : Nat := 12)
    (tolerance : Rat := (1 : Rat) / 1000)
    (goalFeatures : Array Rat := #[])
    (perturb : Option NCAPerturbConfig := none) : NCAOutcome :=
  let init := initNCAState rule.base seed goalFeatures
  let rec go : Nat → Nat → NCAState → NCAState → Bool × Nat × NCAState
    | 0, used, _prev, curr => (true, used, curr)
    | Nat.succ fuel, used, _prev, curr =>
        let curr' :=
          match perturb with
          | some p =>
              if used = p.step then perturbState curr p else curr
          | none => curr
        let next := learnableNCAStep rule curr'
        if isStable curr' next tolerance then
          (true, used + 1, next)
        else
          go fuel (used + 1) curr next
  let (ok, steps, final) := go (max 1 maxSteps) 0 init init
  let score := if ok then 1 else (1 : Rat) / (Int.ofNat (steps + 1) : Rat)
  {
    finalState := final
    converged := ok
    stepsUsed := steps
    stabilityScore := score
    candidates := extractTactics final 4
  }

def stateToFSum (state : NCAState) : FSum :=
  normalize <| state.cells.map (fun c => (c.term, c.weight * c.alive))


end DifferentiableATP
end ATP
end HeytingLean
