import HeytingLean.ATP.DifferentiableATP.TacticDecoder
import HeytingLean.ATP.DifferentiableATP.GoalEncoder
import HeytingLean.ATP.DifferentiableATP.GraphNCA
import HeytingLean.ATP.DifferentiableATP.RewardSignal
import HeytingLean.LoF.Combinators.Differential.KAN

/-!
# ATP.DifferentiableATP.KANTacticSelector

Track A runtime surface:
- KAN tactic scoring over differentiable proof state features,
- warm-start initialization from the static tactic table,
- symbolic summaries for post-hoc regression/explainability.
-/

namespace HeytingLean
namespace ATP
namespace DifferentiableATP

open HeytingLean.LoF
open HeytingLean.LoF.Combinators.Differential
open HeytingLean.LoF.Combinators.Differential.Compute
open HeytingLean.LoF.Combinators.Differential.KAN

inductive RoutingTrainingArm where
  | c
  | a
  | b
  | ac
  deriving Repr, DecidableEq

/-- Update this constant when running isolated arm benchmarks. -/
private def activeRoutingTrainingArm : RoutingTrainingArm := .a

private def armUseContrastive : Bool :=
  activeRoutingTrainingArm = .c || activeRoutingTrainingArm = .ac

private def armUseGoalBias : Bool :=
  activeRoutingTrainingArm = .a || activeRoutingTrainingArm = .ac

private def armUseEdgeTraining : Bool :=
  activeRoutingTrainingArm = .b

structure KANTacticSelector where
  network : KANetwork
  tacticNames : Array String
  tacticPatterns : Array Comb
  temperature : Rat := 1
  featureDim : Nat := 14
  /-- Legacy per-tactic scalar bias (kept for backwards compatibility). -/
  tacticBias : Array Rat := #[]
  /-- Goal-conditioned bias matrix: [tacticIdx × featureDim]. -/
  tacticBiasWeights : Array (Array Rat) := #[]
  adaptShiftScale : Rat := 1
  adaptWidenScale : Rat := 1
  adaptGainScale : Rat := 1
  deriving Repr

private def rankInsert (row : String × Comb × Rat) : List (String × Comb × Rat) → List (String × Comb × Rat)
  | [] => [row]
  | hd :: tl =>
      if row.2.2 > hd.2.2 then row :: hd :: tl else hd :: rankInsert row tl

private def dedupByTactic (rows : List DecodedCandidate) : List DecodedCandidate :=
  rows.foldl
    (fun acc row => if acc.any (fun x => x.tactic = row.tactic) then acc else acc ++ [row])
    []

private def normalizeByTemp (temperature score : Rat) : Rat :=
  if temperature <= 0 then score else score / temperature

private def boolToRat (b : Bool) : Rat :=
  if b then 1 else 0

/-- Fixed-size, structurally meaningful features from current FSum state. -/
def kanFeaturesFromState (w : FSum) : Array Rat :=
  #[
    l2NormSq w,
    dot w (single .K 1),
    dot w (single .S 1),
    dot w (single .Y 1),
    dot w (single (.app .S .K) 1),
    dot w (single (.app .K .S) 1),
    dot w (single (.app .S .S) 1),
    dot w (single (.app .Y .K) 1),
    0, 0, 0, 0, 0, 0
  ]

/-- Compact goal-conditioned feature vector (same width as state features). -/
def kanGoalFeatures (goal : String) : Array Rat :=
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

private def mergeStateGoalFeatures (stateFeat goalFeat : Array Rat) : Array Rat :=
  let dim := max stateFeat.size goalFeat.size
  ((List.range dim).map (fun i => (stateFeat.getD i 0 + goalFeat.getD i 0) / 2)).toArray

private def zeroBiasWeights (tacticCount featureDim : Nat) : Array (Array Rat) :=
  Array.replicate tacticCount (Array.replicate (max 1 featureDim) 0)

private def ensureBiasSize (sel : KANTacticSelector) : Array Rat :=
  if sel.tacticBias.size = sel.tacticNames.size then
    sel.tacticBias
  else
    Array.replicate sel.tacticNames.size 0

private def normalizeBiasWeightRow (featureDim : Nat) (row : Array Rat) : Array Rat :=
  if row.size = featureDim then
    row
  else
    ((List.range (max 1 featureDim)).map (fun i => row.getD i 0)).toArray

private def ensureBiasWeightsSize (sel : KANTacticSelector) : Array (Array Rat) :=
  if sel.tacticBiasWeights.size = sel.tacticNames.size then
    sel.tacticBiasWeights.map (normalizeBiasWeightRow sel.featureDim)
  else
    zeroBiasWeights sel.tacticNames.size sel.featureDim

private def hasGoalBiasWeights (sel : KANTacticSelector) : Bool :=
  sel.tacticBiasWeights.size = sel.tacticNames.size

private def goalConditionedBias (sel : KANTacticSelector) (goalFeat : Array Rat) : Array Rat :=
  let weights := ensureBiasWeightsSize sel
  weights.map (fun row =>
    let dim := min row.size goalFeat.size
    (List.range dim).foldl (fun acc i => acc + row.getD i 0 * goalFeat.getD i 0) 0)

private def applyBias (sel : KANTacticSelector) (logits : Array Rat) : Array Rat :=
  let bias := ensureBiasSize sel
  let dim := max logits.size bias.size
  ((List.range dim).map (fun i => logits.getD i 0 + bias.getD i 0)).toArray

private def applyGoalBias (sel : KANTacticSelector) (logits : Array Rat) (goalFeat : Array Rat) : Array Rat :=
  let bias := goalConditionedBias sel goalFeat
  let dim := max logits.size bias.size
  ((List.range dim).map (fun i => logits.getD i 0 + bias.getD i 0)).toArray

private def scaleGoalFeatures (sel : KANTacticSelector) (goalFeat : Array Rat) : Array Rat :=
  #[
    goalFeat.getD 0 0 * sel.adaptShiftScale,
    goalFeat.getD 1 0 * sel.adaptShiftScale,
    goalFeat.getD 2 0 * sel.adaptWidenScale,
    goalFeat.getD 3 0 * sel.adaptGainScale,
    goalFeat.getD 4 0,
    goalFeat.getD 5 0,
    goalFeat.getD 6 0,
    goalFeat.getD 7 0,
    goalFeat.getD 8 0,
    goalFeat.getD 9 0,
    goalFeat.getD 10 0,
    goalFeat.getD 11 0,
    goalFeat.getD 12 0 * sel.adaptShiftScale,
    goalFeat.getD 13 0
  ]

private def adaptLayerEdge (sel : KANTacticSelector) (goalFeat : Array Rat) (e : KANEdge) : KANEdge :=
  let adaptive := (AdaptiveKANEdge.fromEdge e).adaptByFeatures (scaleGoalFeatures sel goalFeat)
  adaptive.toEdge

private def adaptLayer (sel : KANTacticSelector) (goalFeat : Array Rat) (layer : KANLayer) : KANLayer :=
  let rows :=
    layer.edges.map (fun row =>
      row.map (adaptLayerEdge sel goalFeat))
  { layer with edges := rows }

def adaptCentersToGoal (sel : KANTacticSelector) (goalFeat : Array Rat) : KANTacticSelector :=
  let layers := sel.network.layers.map (adaptLayer sel goalFeat)
  { sel with network := { layers := layers } }

private def warmStartNet : KANetwork :=
  defaultKANetwork 14 (max 1 tacticTable.length)

def warmStartSelector : KANTacticSelector :=
  let names := (tacticTable.map (fun row => row.tactic)).toArray
  let pats := (tacticTable.map (fun row => row.pattern)).toArray
  {
    network := warmStartNet
    tacticNames := names
    tacticPatterns := pats
    temperature := 1
    featureDim := 14
    tacticBias := Array.replicate names.size 0
    tacticBiasWeights := zeroBiasWeights names.size 14
  }

def KANTacticSelector.scoreFeatures (sel : KANTacticSelector) (features : Array Rat) : Array Rat :=
  let f :=
    if features.size = sel.featureDim then
      features
    else
      ((List.range sel.featureDim).map (fun i => features.getD i 0)).toArray
  applyBias sel (sel.network.forward f)

def KANTacticSelector.scoreFeaturesWithGoal
    (sel : KANTacticSelector)
    (features : Array Rat)
    (goalFeat : Array Rat) : Array Rat :=
  let f :=
    if features.size = sel.featureDim then
      features
    else
      ((List.range sel.featureDim).map (fun i => features.getD i 0)).toArray
  let logits := sel.network.forward f
  if armUseGoalBias && hasGoalBiasWeights sel then
    applyGoalBias sel logits goalFeat
  else
    applyBias sel logits

def KANTacticSelector.rankState
    (sel : KANTacticSelector)
    (w : FSum)
    (topK : Nat := 4) : List (String × Comb × Rat) :=
  let features := kanFeaturesFromState w
  let features := mergeStateGoalFeatures features (Array.replicate features.size 0)
  let logits := sel.scoreFeatures features
  let rows :=
    (List.range sel.tacticNames.size).foldl
      (fun acc i =>
        let name := sel.tacticNames.getD i "simp"
        let pat := sel.tacticPatterns.getD i .S
        let conf := absRat (normalizeByTemp sel.temperature (logits.getD i 0))
        rankInsert (name, pat, conf) acc)
      []
  rows.take (max 1 topK)

def KANTacticSelector.rankStateWithGoal
    (sel : KANTacticSelector)
    (w : FSum)
    (goal : String)
    (topK : Nat := 4) : List (String × Comb × Rat) :=
  let goalFeat := kanGoalFeatures goal
  let features := mergeStateGoalFeatures (kanFeaturesFromState w) goalFeat
  let logits := sel.scoreFeaturesWithGoal features goalFeat
  let rows :=
    (List.range sel.tacticNames.size).foldl
      (fun acc i =>
        let name := sel.tacticNames.getD i "simp"
        let pat := sel.tacticPatterns.getD i .S
        let conf := absRat (normalizeByTemp sel.temperature (logits.getD i 0))
        rankInsert (name, pat, conf) acc)
      []
  rows.take (max 1 topK)

def KANTacticSelector.rankStateWithGoalFeatures
    (sel : KANTacticSelector)
    (w : FSum)
    (goalFeat : Array Rat)
    (topK : Nat := 4) : List (String × Comb × Rat) :=
  let features := mergeStateGoalFeatures (kanFeaturesFromState w) goalFeat
  let logits := sel.scoreFeaturesWithGoal features goalFeat
  let rows :=
    (List.range sel.tacticNames.size).foldl
      (fun acc i =>
        let name := sel.tacticNames.getD i "simp"
        let pat := sel.tacticPatterns.getD i .S
        let conf := absRat (normalizeByTemp sel.temperature (logits.getD i 0))
        rankInsert (name, pat, conf) acc)
      []
  rows.take (max 1 topK)

def decodeFromKANWeights
    (w : FSum)
    (k : Nat := 4)
    (selector : KANTacticSelector := warmStartSelector) : List DecodedCandidate :=
  let ranked := selector.rankState w (max 1 k)
  let rows := ranked.map (fun row =>
    {
      comb := row.2.1
      tactic := row.1
      source := "kan_selector"
      confidence := row.2.2
    })
  if rows.isEmpty then decodeFromWeights w k else rows

def decodeFromKANWeightsWithGoal
    (w : FSum)
    (goal : String)
    (k : Nat := 4)
    (selector : KANTacticSelector := warmStartSelector) : List DecodedCandidate :=
  let goalFeat := kanGoalFeatures goal
  let ranked := (adaptCentersToGoal selector goalFeat).rankStateWithGoalFeatures w goalFeat (max 1 k)
  let rows := ranked.map (fun row =>
    {
      comb := row.2.1
      tactic := row.1
      source := "kan_selector_goal"
      confidence := row.2.2
    })
  if rows.isEmpty then decodeFromKANWeights w k selector else rows

private def compositionSuffixesForGoal (goal : String) : List String :=
  let f := goalFeatures goal
  let arithmetic :=
    if f.hasEq && (f.hasNat || f.hasInt || f.hasReal || f.hasPlus || f.hasMul) then
      ["ring", "omega", "linarith", "norm_num"]
    else
      []
  let logic :=
    if f.hasAnd || f.hasOr || f.hasNot || f.hasArrow || f.hasIff then
      ["tauto", "simp", "aesop"]
    else
      ["simp"]
  let introChains :=
    if f.hasForall && f.hasEq && (f.hasPlus || f.hasMul || f.hasNat || f.hasInt || f.hasReal) then
      [ "intro; ring"
      , "intro; omega"
      , "intro; linarith"
      , "constructor; intro; ring"
      , "constructor; intro; omega"
      ]
    else if f.hasAnd then
      ["constructor; omega", "constructor; tauto", "constructor; simp"]
    else
      []
  let nestedSplits :=
    if f.hasAnd then
      ["constructor; constructor; omega", "constructor; constructor; simp"]
    else
      []
  (arithmetic ++ logic ++ introChains ++ nestedSplits ++ ["decide"]).eraseDups

private def isCompositionPrefix (tactic : String) : Bool :=
  tactic.startsWith "intro" || tactic.startsWith "constructor" ||
  tactic.startsWith "cases" || tactic.startsWith "apply" ||
  tactic.startsWith "simp_all" || tactic.startsWith "simp only"

private def syntheticCompositionPrefixes (rows : List DecodedCandidate) : List DecodedCandidate :=
  let anchor :=
    rows.headD
      {
        comb := .K
        tactic := "constructor"
        source := "kan_selector_seed"
        confidence := (1 : Rat) / 5
      }
  [ { anchor with tactic := "constructor", source := "kan_selector_seed::constructor" }
  , { anchor with tactic := "apply And.intro", source := "kan_selector_seed::and_intro" }
  , { anchor with tactic := "intro", source := "kan_selector_seed::intro" }
  ]

private def composeRows (rows : List DecodedCandidate) (goal : String) (budget : Nat) : List DecodedCandidate :=
  let suffixes := compositionSuffixesForGoal goal
  let structural := rows.filter (fun r => isCompositionPrefix r.tactic)
  let prefixes :=
    if structural.isEmpty then
      syntheticCompositionPrefixes rows
    else
      structural ++ syntheticCompositionPrefixes rows
  let raw :=
    prefixes.foldl
      (fun acc row =>
        suffixes.foldl
          (fun acc2 suffix =>
            if row.tactic = suffix || row.tactic.endsWith suffix then acc2
            else
              let baseConf := if row.confidence = 0 then (1 : Rat) / 10 else row.confidence
              acc2 ++
                [{ comb := row.comb
                   tactic := s!"{row.tactic}; {suffix}"
                   source := s!"kan_selector_composed::{suffix}"
                   confidence := baseConf / 2 }])
          acc)
      []
  (dedupByTactic raw).take (max 1 budget)

def decodeFromKANWeightsWithGoalAndCompositions
    (w : FSum)
    (goal : String)
    (k : Nat := 4)
    (compositionBudget : Nat := 6)
    (selector : KANTacticSelector := warmStartSelector) : List DecodedCandidate :=
  let base := decodeFromKANWeightsWithGoal w goal (max 1 k) selector
  let comps := composeRows base goal compositionBudget
  let merged := dedupByTactic (base ++ comps)
  merged.take (max 1 k + max 1 compositionBudget)

def decodeFromKANWeightsWithGoalFeatures
    (w : FSum)
    (goalFeat : Array Rat)
    (k : Nat := 4)
    (selector : KANTacticSelector := warmStartSelector) : List DecodedCandidate :=
  let ranked := (adaptCentersToGoal selector goalFeat).rankStateWithGoalFeatures w goalFeat (max 1 k)
  let rows := ranked.map (fun row =>
    {
      comb := row.2.1
      tactic := row.1
      source := "kan_selector_goal_features"
      confidence := row.2.2
    })
  if rows.isEmpty then decodeFromKANWeights w k selector else rows

def kanSymbolicSummaries
    (selector : KANTacticSelector := warmStartSelector)
    (maxRows : Nat := 6) : List String :=
  selector.network.symbolicSummary (max 1 maxRows)

private def scoreFromConfidence (conf : Rat) : Rat :=
  let raw := conf / (1 + absRat conf)
  if raw < 0 then 0 else if raw > 1 then 1 else raw

private def tacticHead (tactic : String) : String :=
  ((tactic.splitOn ";").headD "").trim

private def tacticAtom (tactic : String) : String :=
  ((tacticHead tactic).splitOn " ").headD ""

private def tacticScore (expected : String) (rows : List (String × Comb × Rat)) : Rat :=
  let expectedTrim := expected.trim
  let expectedHead := tacticHead expectedTrim
  let expectedAtom := tacticAtom expectedTrim
  let exactScore :=
    rows.foldl
      (fun acc row =>
        if row.1 = expectedTrim then
          max acc (scoreFromConfidence row.2.2)
        else
          acc)
      0
  if exactScore > 0 then
    exactScore
  else
    let prefixScore :=
      rows.foldl
        (fun acc row =>
          let rowHead := tacticHead row.1
          let rowAtom := tacticAtom row.1
          let base := scoreFromConfidence row.2.2
          let partialScore :=
            if expectedHead = rowHead then
              base / 2
            else if expectedHead.startsWith rowHead || rowHead.startsWith expectedHead then
              base / 3
            else if expectedAtom = rowAtom && !expectedAtom.isEmpty then
              base / 4
            else
              0
          max acc partialScore)
        0
    if prefixScore < 0 then 0 else if prefixScore > 1 then 1 else prefixScore

structure EnrichedTrainingSample where
  goal : String
  expectedTactic : String
  subgoalsSolved : Nat := 1
  totalSubgoals : Nat := 1
  /- Composition bonus is stored explicitly so downstream search/reporting
  surfaces can reconstruct the enriched sample without flattening away the
  hierarchy signal. -/
  compositionBonus : Rat := (1 : Rat) / 2
  deriving Repr

private def enrichTrainingSample (sample : String × String) : EnrichedTrainingSample :=
  { goal := sample.1
    expectedTactic := sample.2
    subgoalsSolved := 1
    totalSubgoals := 1
    /- Legacy `(goal, tactic)` samples represent direct solved goals. -/
    compositionBonus := 0 }

private def flattenTrainingSample (sample : EnrichedTrainingSample) : String × String :=
  (sample.goal, sample.expectedTactic)

private def isNegativeTrainingSample (sample : EnrichedTrainingSample) : Bool :=
  sample.totalSubgoals > 0 && sample.subgoalsSolved = 0

private def hierarchicalLoss (score : Rat) (sample : EnrichedTrainingSample) : Rat :=
  /-
  Positive samples target score=1 and use hierarchical reward as weight.
  Negative samples (`0/1`) target score=0 so failed tactics get demoted.
  -/
  let completionReward :=
    hierarchicalSubgoalReward sample.subgoalsSolved sample.totalSubgoals sample.compositionBonus
  let baseReward :=
    hierarchicalSubgoalReward sample.subgoalsSolved sample.totalSubgoals 0
  if isNegativeTrainingSample sample then
    let miss := score
    let weight : Rat := (1 : Rat) / 2
    weight * miss * miss
  else
    let miss := 1 - score
    let weight := if completionReward < 1 then baseReward else completionReward
    weight * miss * miss

private def routingInversionPenalty
    (sel : KANTacticSelector)
    (samples : List (String × String))
    (topK : Nat := 6) : Rat :=
  if samples.isEmpty then
    0
  else
    let evalTopK := max (max 1 topK) sel.tacticNames.size
    let total :=
      samples.foldl
        (fun acc sample =>
          let goal := sample.1
          let expected := sample.2
          let goalFeat := kanGoalFeatures goal
          let encoded := encodeGoal goal .omega [] none
          let ranked :=
            (adaptCentersToGoal sel goalFeat).rankStateWithGoalFeatures
              encoded.initial
              goalFeat
              evalTopK
          let top := ranked.headD ("", .K, 0)
          let top1 := top.1
          let top1Conf := top.2.2
          let isInversion :=
            samples.any (fun other =>
              other.2 = top1 && other.2.trim != expected.trim)
          if isInversion then
            acc + absRat top1Conf
          else
            acc)
        0
    total / (Int.ofNat samples.length : Rat)

private def selectorLossEnriched
    (sel : KANTacticSelector)
    (samples : List EnrichedTrainingSample)
    (topK : Nat := 6) : Rat :=
  if samples.isEmpty then
    0
  else
    let evalTopK := max (max 1 topK) sel.tacticNames.size
    let total :=
      samples.foldl
        (fun acc sample =>
          let goal := sample.goal
          let expected := sample.expectedTactic
          let encoded := encodeGoal goal .omega [] none
          let goalFeat := kanGoalFeatures goal
          let ranked :=
            (adaptCentersToGoal sel goalFeat).rankStateWithGoalFeatures
              encoded.initial
              goalFeat
              evalTopK
          let score := tacticScore expected ranked
          acc + hierarchicalLoss score sample)
        0
    let baseLoss := total / (Int.ofNat samples.length : Rat)
    if armUseContrastive then
      let contrastiveWeight : Rat := (1 : Rat) / 2
      baseLoss + contrastiveWeight * routingInversionPenalty sel (samples.map flattenTrainingSample) topK
    else
      baseLoss

private def selectorLoss
    (sel : KANTacticSelector)
    (samples : List (String × String))
    (topK : Nat := 6) : Rat :=
  selectorLossEnriched sel (samples.map enrichTrainingSample) topK

private def setBiasAt (sel : KANTacticSelector) (i : Nat) (v : Rat) : KANTacticSelector :=
  let bias := ensureBiasSize sel
  if bias.isEmpty then
    sel
  else
    { sel with tacticBias := bias.set! (i % bias.size) v }

private def setBiasWeightAt (sel : KANTacticSelector) (tacticIdx featureIdx : Nat) (v : Rat) : KANTacticSelector :=
  let rows := ensureBiasWeightsSize sel
  if rows.isEmpty then
    sel
  else
    let rowIdx := tacticIdx % rows.size
    let row := normalizeBiasWeightRow sel.featureDim (rows.getD rowIdx #[])
    if row.isEmpty then
      sel
    else
      let colIdx := featureIdx % row.size
      let newRow := row.set! colIdx v
      { sel with tacticBiasWeights := rows.set! rowIdx newRow }

private def scaleParams (sel : KANTacticSelector) : Array Rat :=
  #[sel.adaptShiftScale, sel.adaptWidenScale, sel.adaptGainScale]

private def setScaleAt (sel : KANTacticSelector) (i : Nat) (v : Rat) : KANTacticSelector :=
  match i with
  | 0 => { sel with adaptShiftScale := v }
  | 1 => { sel with adaptWidenScale := v }
  | _ => { sel with adaptGainScale := v }

private def defaultEdgeForAccess : KANEdge :=
  { controlPoints := [0], gridMin := -2, gridMax := 2, order := 3 }

private def defaultLayerForAccess : KANLayer :=
  { inputDim := 1, outputDim := 1, edges := #[] }

private def getEdgeCoeff (sel : KANTacticSelector) (layerIdx rowIdx colIdx coeffIdx : Nat) : Rat :=
  let layers := sel.network.layers.toArray
  if layers.isEmpty then
    0
  else
    let li := layerIdx % layers.size
    let layer := layers.getD li defaultLayerForAccess
    if layer.edges.isEmpty then
      0
    else
      let ri := rowIdx % layer.edges.size
      let row := layer.edges.getD ri #[]
      if row.isEmpty then
        0
      else
        let ci := colIdx % row.size
        let edge := row.getD ci defaultEdgeForAccess
        let cps := if edge.controlPoints.isEmpty then [0] else edge.controlPoints
        cps.getD (coeffIdx % cps.length) 0

private def setEdgeCoeff
    (sel : KANTacticSelector)
    (layerIdx rowIdx colIdx coeffIdx : Nat)
    (v : Rat) : KANTacticSelector :=
  let layers := sel.network.layers.toArray
  if layers.isEmpty then
    sel
  else
    let li := layerIdx % layers.size
    let layer := layers.getD li defaultLayerForAccess
    if layer.edges.isEmpty then
      sel
    else
      let ri := rowIdx % layer.edges.size
      let row := layer.edges.getD ri #[]
      if row.isEmpty then
        sel
      else
        let ci := colIdx % row.size
        let edge := row.getD ci defaultEdgeForAccess
        let cps := if edge.controlPoints.isEmpty then [0] else edge.controlPoints
        let cpsArr := cps.toArray
        let coeffPos := coeffIdx % cpsArr.size
        let newCPs := (cpsArr.set! coeffPos v).toList
        let newEdge := { edge with controlPoints := newCPs }
        let newRow := row.set! ci newEdge
        let newEdges := layer.edges.set! ri newRow
        let newLayer := { layer with edges := newEdges }
        let newLayers := layers.set! li newLayer
        { sel with network := { layers := newLayers.toList } }

private def selectParamIndices (size budget : Nat) : List Nat :=
  if size = 0 then
    []
  else
    let cap := max 1 (min size budget)
    if cap >= size then
      List.range size
    else
      let spread := (List.range cap).map (fun i => (i * size) / cap)
      let picked := ((size - 1) :: spread).eraseDups
      picked.take cap

private def findTacticIndex? (tacticNames : Array String) (expected : String) : Option Nat :=
  let expectedTrim := expected.trim
  let expectedHead := tacticHead expectedTrim
  let expectedAtom := tacticAtom expectedTrim
  let idxs := List.range tacticNames.size
  match idxs.find? (fun i => tacticNames.getD i "" = expectedTrim) with
  | some idx => some idx
  | none =>
      match idxs.find? (fun i => tacticHead (tacticNames.getD i "") = expectedHead) with
      | some idx => some idx
      | none =>
          idxs.find? (fun i =>
            let atom := tacticAtom (tacticNames.getD i "")
            atom = expectedAtom && !atom.isEmpty)

private def edgeParamCandidates
    (sel : KANTacticSelector)
    (rowIndices : List Nat)
    (budget : Nat) : List (Nat × Nat × Nat × Nat) :=
  let layers := sel.network.layers.toArray
  if layers.isEmpty then
    []
  else
    let layer := layers.getD 0 defaultLayerForAccess
    if layer.edges.isEmpty then
      []
    else
      let raw :=
        rowIndices.foldl
          (fun acc rowRaw =>
            let rowIdx := rowRaw % layer.edges.size
            let row := layer.edges.getD rowIdx #[]
            if row.isEmpty then
              acc
            else
              let cols := List.range row.size
              cols.foldl
                (fun acc2 colIdx =>
                  let edge := row.getD colIdx defaultEdgeForAccess
                  let cps := if edge.controlPoints.isEmpty then [0] else edge.controlPoints
                  let lastCoeff := cps.length - 1
                  acc2 ++ [(0, rowIdx, colIdx, 0), (0, rowIdx, colIdx, lastCoeff)])
                acc)
          ([] : List (Nat × Nat × Nat × Nat))
      let dedup := raw.eraseDups
      let picks := selectParamIndices dedup.length (max 1 (min dedup.length budget))
      picks.map (fun i => dedup.getD i (0, 0, 0, 0))

private def takeBalancedSamples
    (legacySamples : List EnrichedTrainingSample)
    (enrichedSamples : List EnrichedTrainingSample)
    (sampleBudget : Nat) : List EnrichedTrainingSample :=
  let budget := max 1 sampleBudget
  let pickEnriched (rows : List EnrichedTrainingSample) (cap : Nat) :
      List EnrichedTrainingSample × List EnrichedTrainingSample :=
    let capped := max 1 cap
    let negatives := rows.filter isNegativeTrainingSample
    let positives := rows.filter (fun sample => !isNegativeTrainingSample sample)
    let negativeQuota :=
      min negatives.length
        (if negatives.isEmpty then
          0
        else
          max 1 (capped / 3))
    let negativesTake := min negatives.length negativeQuota
    let positivesTake := min positives.length (capped - negativesTake)
    let picked := positives.take positivesTake ++ negatives.take negativesTake
    let rest := positives.drop positivesTake ++ negatives.drop negativesTake
    if picked.length >= capped then
      (picked.take capped, rest)
    else
      let refillTake := capped - picked.length
      let refill := rest.take refillTake
      (picked ++ refill, rest.drop refill.length)
  if legacySamples.isEmpty then
    (pickEnriched enrichedSamples budget).1
  else if enrichedSamples.isEmpty then
    legacySamples.take budget
  else
    let half := max 1 (budget / 2)
    let legacyTake := min legacySamples.length half
    let enrichedBudget := budget - legacyTake
    let legacyPicked := legacySamples.take legacyTake
    let (enrichedPicked, enrichedRest) := pickEnriched enrichedSamples enrichedBudget
    let seeded := legacyPicked ++ enrichedPicked
    if seeded.length >= budget then
      seeded.take budget
    else
      let refill := legacySamples.drop legacyTake ++ enrichedRest
      seeded ++ refill.take (budget - seeded.length)

def trainKANOnGoals
    (samples : List (String × String))
    (base : KANTacticSelector := warmStartSelector)
    (iterations : Nat := 12)
    (learningRate : Rat := (1 : Rat) / 100)
    (epsilon : Rat := (1 : Rat) / 1000)
    (sampleBudget : Nat := 9)
    (paramBudget : Nat := 16)
    (enrichedSamples : List EnrichedTrainingSample := []) : KANTacticSelector × Rat × List TrainingTraceEntry :=
  let eps := if epsilon = 0 then (1 : Rat) / 1000 else epsilon
  let effectiveParamBudget := if armUseGoalBias then max (max 1 paramBudget) 32 else max 1 paramBudget
  let legacySamples := samples.map enrichTrainingSample
  let cappedSamples := takeBalancedSamples legacySamples enrichedSamples sampleBudget
  let base := { base with tacticBias := ensureBiasSize base, tacticBiasWeights := ensureBiasWeightsSize base }
  let biasSize := (ensureBiasSize base).size
  let requiredBiasIndices :=
    cappedSamples.foldl
      (fun acc sample =>
        match findTacticIndex? base.tacticNames sample.expectedTactic with
        | some idx =>
            if acc.contains idx then acc else acc ++ [idx]
        | none => acc)
      ([] : List Nat)
  let routedBiasRows :=
    if requiredBiasIndices.isEmpty then
      (selectParamIndices base.tacticNames.size (min 2 base.tacticNames.size))
    else
      requiredBiasIndices
  let biasCap := max 1 (min biasSize effectiveParamBudget)
  let coverageBiasIndices := selectParamIndices biasSize biasSize
  let biasIndices := ((routedBiasRows ++ coverageBiasIndices).eraseDups).take biasCap
  let scalarBiasBudget := if armUseGoalBias then 0 else biasIndices.length
  let rawBiasWeightPairs : List (Nat × Nat) :=
    routedBiasRows.foldl
      (fun acc tacticIdx =>
        acc ++ (List.range (max 1 base.featureDim)).map (fun featureIdx => (tacticIdx, featureIdx)))
      ([] : List (Nat × Nat))
  let biasWeightBudget :=
    if armUseGoalBias then
      min rawBiasWeightPairs.length effectiveParamBudget
    else
      0
  let biasWeightPairs := rawBiasWeightPairs.take biasWeightBudget
  let baseBudgetUsed := scalarBiasBudget + biasWeightPairs.length
  let scaleBudget := if effectiveParamBudget > baseBudgetUsed then min 3 (effectiveParamBudget - baseBudgetUsed) else 0
  let edgeBudget := if armUseEdgeTraining then min 8 (max 1 (effectiveParamBudget / 2)) else 0
  let edgeCoords := edgeParamCandidates base routedBiasRows edgeBudget
  let edgeLearningRate := learningRate / 5
  let baselineLoss := selectorLossEnriched base cappedSamples
  let edgeEnabledInit := armUseEdgeTraining && !edgeCoords.isEmpty
  let rec trainIter : Nat → Nat → Bool → Nat → KANTacticSelector → List TrainingTraceEntry →
      KANTacticSelector × List TrainingTraceEntry
    | 0, _, _, _, sel, trace => (sel, trace.reverse)
    | Nat.succ fuel, iterIdx, edgeEnabled, edgeRegressionStreak, sel, trace =>
        let lossBefore := selectorLossEnriched sel cappedSamples
        let bias := ensureBiasSize sel
        let biasWeights := ensureBiasWeightsSize sel
        let scalarParamsBefore := (biasIndices.map (fun i => bias.getD i 0)).toArray
        let weightParamsBefore :=
          (biasWeightPairs.map (fun idx =>
            let row := biasWeights.getD idx.1 (Array.replicate (max 1 sel.featureDim) 0)
            row.getD idx.2 0)).toArray
        let edgeParamsBefore :=
          (edgeCoords.map (fun coord => getEdgeCoeff sel coord.1 coord.2.1 coord.2.2.1 coord.2.2.2)).toArray
        let paramsBefore :=
          (if armUseGoalBias then weightParamsBefore else scalarParamsBefore)
            ++ ((List.range scaleBudget).map (fun i => (scaleParams sel).getD i 1)).toArray
            ++ edgeParamsBefore
        let (afterBias, biasGrads) :=
          if armUseGoalBias then
            biasWeightPairs.foldl
              (fun (acc : KANTacticSelector × Array Rat) idx =>
                let (cur, gs) := acc
                let curWeights := ensureBiasWeightsSize cur
                let row := curWeights.getD idx.1 (Array.replicate (max 1 cur.featureDim) 0)
                let wi := row.getD idx.2 0
                let plusSel := setBiasWeightAt cur idx.1 idx.2 (wi + eps)
                let minusSel := setBiasWeightAt cur idx.1 idx.2 (wi - eps)
                let lPlus := selectorLossEnriched plusSel cappedSamples
                let lMinus := selectorLossEnriched minusSel cappedSamples
                let grad := truncRat ((lPlus - lMinus) / (2 * eps))
                (setBiasWeightAt cur idx.1 idx.2 (wi - learningRate * grad), gs.push grad))
              (sel, #[])
          else
            biasIndices.foldl
              (fun (acc : KANTacticSelector × Array Rat) idx =>
                let (cur, gs) := acc
                let bi := (ensureBiasSize cur).getD idx 0
                let plusSel := setBiasAt cur idx (bi + eps)
                let minusSel := setBiasAt cur idx (bi - eps)
                let lPlus := selectorLossEnriched plusSel cappedSamples
                let lMinus := selectorLossEnriched minusSel cappedSamples
                let grad := truncRat ((lPlus - lMinus) / (2 * eps))
                (setBiasAt cur idx (bi - learningRate * grad), gs.push grad))
              (sel, #[])
        let (afterScale, scaleGrads) :=
          (List.range scaleBudget).foldl
            (fun (acc : KANTacticSelector × Array Rat) i =>
              let (cur, gs) := acc
              let sp := scaleParams cur
              let vi := sp.getD i 1
              let plusSel := setScaleAt cur i (vi + eps)
              let minusSel := setScaleAt cur i (vi - eps)
              let lPlus := selectorLossEnriched plusSel cappedSamples
              let lMinus := selectorLossEnriched minusSel cappedSamples
              let grad := truncRat ((lPlus - lMinus) / (2 * eps))
              (setScaleAt cur i (vi - learningRate * grad), gs.push grad))
            (afterBias, #[])
        let (afterEdge, edgeGrads) :=
          if edgeEnabled && armUseEdgeTraining then
            edgeCoords.foldl
              (fun (acc : KANTacticSelector × Array Rat) coord =>
                let (cur, gs) := acc
                let curCoeff := getEdgeCoeff cur coord.1 coord.2.1 coord.2.2.1 coord.2.2.2
                let plusSel := setEdgeCoeff cur coord.1 coord.2.1 coord.2.2.1 coord.2.2.2 (curCoeff + eps)
                let minusSel := setEdgeCoeff cur coord.1 coord.2.1 coord.2.2.1 coord.2.2.2 (curCoeff - eps)
                let lPlus := selectorLossEnriched plusSel cappedSamples
                let lMinus := selectorLossEnriched minusSel cappedSamples
                let grad := truncRat ((lPlus - lMinus) / (2 * eps))
                (setEdgeCoeff cur coord.1 coord.2.1 coord.2.2.1 coord.2.2.2 (curCoeff - edgeLearningRate * grad), gs.push grad))
              (afterScale, #[])
          else
            (afterScale, #[])
        let lossAfterEdge := selectorLossEnriched afterEdge cappedSamples
        let nextState :=
          if edgeEnabled && armUseEdgeTraining then
            let nextStreak := if lossAfterEdge > baselineLoss then edgeRegressionStreak + 1 else 0
            if nextStreak >= 3 then
              (afterScale, false, 0)
            else
              (afterEdge, true, nextStreak)
          else
            (afterEdge, edgeEnabled, edgeRegressionStreak)
        let next := nextState.1
        let edgeEnabled' := nextState.2.1
        let edgeRegressionStreak' := nextState.2.2
        let nextBias := ensureBiasSize next
        let nextBiasWeights := ensureBiasWeightsSize next
        let scalarParamsAfter := (biasIndices.map (fun i => nextBias.getD i 0)).toArray
        let weightParamsAfter :=
          (biasWeightPairs.map (fun idx =>
            let row := nextBiasWeights.getD idx.1 (Array.replicate (max 1 next.featureDim) 0)
            row.getD idx.2 0)).toArray
        let edgeParamsAfter :=
          (edgeCoords.map (fun coord => getEdgeCoeff next coord.1 coord.2.1 coord.2.2.1 coord.2.2.2)).toArray
        let paramsAfter :=
          (if armUseGoalBias then weightParamsAfter else scalarParamsAfter)
            ++ ((List.range scaleBudget).map (fun i => (scaleParams next).getD i 1)).toArray
            ++ edgeParamsAfter
        let entry : TrainingTraceEntry :=
          { iteration := iterIdx
            lossBefore := lossBefore
            gradNorms := biasGrads ++ scaleGrads ++ edgeGrads
            paramsBefore := paramsBefore
            paramsAfter := paramsAfter }
        trainIter fuel (iterIdx + 1) edgeEnabled' edgeRegressionStreak' next (entry :: trace)
  let (trained, trace) := trainIter (max 1 iterations) 0 edgeEnabledInit 0 base []
  (trained, selectorLossEnriched trained cappedSamples, trace)

def trainKANOnEnrichedGoals
    (samples : List EnrichedTrainingSample)
    (base : KANTacticSelector := warmStartSelector)
    (iterations : Nat := 12)
    (learningRate : Rat := (1 : Rat) / 100)
    (epsilon : Rat := (1 : Rat) / 1000)
    (sampleBudget : Nat := 9)
    (paramBudget : Nat := 16) : KANTacticSelector × Rat × List TrainingTraceEntry :=
  trainKANOnGoals
    []
    base
    iterations
    learningRate
    epsilon
    sampleBudget
    paramBudget
    (enrichedSamples := samples)

def trainOnSamples
    (selector : KANTacticSelector)
    (samples : List (String × String))
    (iterations : Nat := 12)
    (learningRate : Rat := (1 : Rat) / 100)
    (sampleBudget : Nat := 9)
    (paramBudget : Nat := 16) : KANTacticSelector :=
  (trainKANOnGoals
      samples
      selector
      (max 1 iterations)
      learningRate
      ((1 : Rat) / 1000)
      (max 1 sampleBudget)
      (max 1 paramBudget)).1

end DifferentiableATP
end ATP
end HeytingLean
