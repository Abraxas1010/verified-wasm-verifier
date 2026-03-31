import HeytingLean.ATP.DifferentiableATP.LensGDOrchestrator
import HeytingLean.ATP.DifferentiableATP.KANTacticSelector
import HeytingLean.ATP.DifferentiableATP.RewardSignal
import HeytingLean.ATP.DifferentiableATP.ProofStateObserver
import HeytingLean.ATP.DifferentiableATP.ProgressEstimator

/-!
# ATP.DifferentiableATP.SearchTree

Depth-bounded iterative proof search driven by differentiable ATP ranking.
-/

namespace HeytingLean
namespace ATP
namespace DifferentiableATP

open HeytingLean.LoF.Combinators.Differential.Compute

structure SearchNode where
  goal : String
  depth : Nat
  parentTactic : Option String
  preferredTactic : Option String
  groupId : Option Nat
  groupSubgoalIndex : Option Nat
  priorityScore : Rat
  proofScriptRev : List (String × String)
  carry : Option FSum
  deriving Repr

structure SearchConfig where
  maxDepth : Nat := 5
  maxTotalAttempts : Nat := 200
  maxBranches : Nat := 4
  conjunctionBranchBudget : Nat := 6
  parallelSubgoalWorkers : Nat := 1
  gdBudget : Nat := 12
  macroSteps : Nat := 3
  subgoalMaxLaneChanges : Nat := 0
  subgoalLensBudget : Nat := 1
  warmStart : Bool := false
  observerTimeoutSeconds : Nat := 60
  searchTimeoutSeconds : Nat := 0
  deriving Repr

structure SubgoalGroup where
  groupId : Nat
  parentGoal : String
  parentTactic : String
  parentScript : List (String × String)
  subgoals : List String
  solved : List (Nat × List (String × String))
  deriving Repr

structure CandidateRejection where
  nodeGoal : String
  nodeDepth : Nat
  tactic : String
  reason : String
  remainingGoals : List String
  observerStderrExcerpt : String
  deriving Repr

structure SearchResult where
  proved : Bool
  proofScript : List (String × String)
  trainingSamples : List (String × String)
  enrichedTrainingSamples : List EnrichedTrainingSample
  nodesExplored : Nat
  maxDepthReached : Nat
  totalAttempts : Nat
  backtrackCount : Nat
  searchTree : List SearchNode
  candidateRejections : List CandidateRejection
  reason : String

instance : Repr SearchResult where
  reprPrec result _ :=
    Std.Format.text <|
      s!"SearchResult(proved={result.proved}, proofSteps={result.proofScript.length}, " ++
      s!"trainingSamples={result.trainingSamples.length}, " ++
      s!"enrichedTrainingSamples={result.enrichedTrainingSamples.length}, " ++
      s!"nodesExplored={result.nodesExplored}, maxDepthReached={result.maxDepthReached}, " ++
      s!"totalAttempts={result.totalAttempts}, backtrackCount={result.backtrackCount}, " ++
      s!"queuedNodes={result.searchTree.length}, " ++
      s!"candidateRejections={result.candidateRejections.length}, reason={result.reason})"

private def clamp01 (r : Rat) : Rat :=
  if r < 0 then 0 else if r > 1 then 1 else r

private def lossNorm (loss : Rat) : Rat :=
  if loss <= 0 then 0 else loss / (1 + loss)

private def computePriority (progressScore psrLoss : Rat) : Rat :=
  clamp01 (((1 - clamp01 progressScore) * 7 + lossNorm psrLoss * 3) / 10)

private def insertByPriority (node : SearchNode) : List SearchNode → List SearchNode
  | [] => [node]
  | head :: tail =>
      if node.priorityScore < head.priorityScore then
        node :: head :: tail
      else if node.priorityScore = head.priorityScore && node.depth < head.depth then
        node :: head :: tail
      else
        head :: insertByPriority node tail

private def pushQueue (node : SearchNode) (queue : List SearchNode) : List SearchNode :=
  insertByPriority node queue

private def pushMany (nodes : List SearchNode) (queue : List SearchNode) : List SearchNode :=
  nodes.foldl (fun q n => pushQueue n q) queue

private def laneConfigForSearch
    (cfg : SearchConfig)
    (base : OrchestratorConfig) : OrchestratorConfig :=
  { base with
    maxIterations := max 1 cfg.gdBudget
    maxMacroSteps := max 1 cfg.macroSteps
    decodeTopK := max 1 cfg.maxBranches
    maxLaneChanges := cfg.subgoalMaxLaneChanges
    lensBudget := max 1 cfg.subgoalLensBudget
  }

private def boolNat (b : Bool) : Nat :=
  if b then 1 else 0

private def goalShapeKey (goal : String) : String :=
  let f := goalFeatures goal
  String.intercalate "|"
    [ toString (boolNat f.hasForall)
    , toString (boolNat f.hasExists)
    , toString (boolNat f.hasArrow)
    , toString (boolNat f.hasIff)
    , toString (boolNat f.hasAnd)
    , toString (boolNat f.hasOr)
    , toString (boolNat f.hasNot)
    , toString (boolNat f.hasEq)
    , toString (boolNat f.hasNat)
    , toString (boolNat f.hasInt)
    , toString (boolNat f.hasReal)
    , toString (boolNat f.hasList)
    , toString (boolNat f.hasSet)
    , toString f.arrowDepth
    , toString f.quantifierDepth
    , toString f.tokenCount
    ]

private def oneLine (txt : String) : String :=
  String.intercalate " " ((txt.splitOn "\n").map String.trim |>.filter (fun s => !s.isEmpty))

private def hasSubstr (txt needle : String) : Bool :=
  if needle.isEmpty then
    true
  else
    (txt.splitOn needle).length > 1

private def mkRejection
    (node : SearchNode)
    (tactic : String)
    (reason : String)
    (remainingGoals : List String := [])
    (observerStderr : String := "") : CandidateRejection :=
  { nodeGoal := node.goal
    nodeDepth := node.depth
    tactic := tactic
    reason := reason
    remainingGoals := remainingGoals
    observerStderrExcerpt := oneLine observerStderr }

private def mkFailure
    (reason : String)
    (nodesExplored maxDepthReached totalAttempts backtrackCount : Nat)
    (treeRev : List SearchNode)
    (rejectionsRev : List CandidateRejection)
    (trainingSamplesRev : List (String × String))
    (enrichedSamplesRev : List EnrichedTrainingSample) : SearchResult :=
  { proved := false
    proofScript := []
    trainingSamples := trainingSamplesRev.reverse
    enrichedTrainingSamples := enrichedSamplesRev.reverse
    nodesExplored := nodesExplored
    maxDepthReached := maxDepthReached
    totalAttempts := totalAttempts
    backtrackCount := backtrackCount
    searchTree := treeRev.reverse
    candidateRejections := rejectionsRev.reverse
    reason := reason }

private def isObserverSentinel (goal : String) : Bool :=
  goal.trim = "⊢ _observer_unresolved"

private def hasArithmeticSignal (f : GoalFeatures) : Bool :=
  f.hasNat || f.hasInt || f.hasReal || f.hasPlus || f.hasMul || f.hasLt || f.hasLe

private def hasLogicSignal (f : GoalFeatures) : Bool :=
  f.hasArrow || f.hasIff || f.hasAnd || f.hasOr || f.hasNot

private def dedupDecodedByTactic (rows : List DecodedCandidate) : List DecodedCandidate :=
  rows.foldl
    (fun acc row =>
      if acc.any (fun x => x.tactic = row.tactic) then acc else acc ++ [row])
    []

private def preferredStructuralTactics (goal : String) : List String :=
  let f := goalFeatures goal
  let universalTactics : List String := if f.hasAnd then universalConjunctionSolverTactics goal else []
  let splitTactics : List String := if f.hasAnd then ["constructor", "apply And.intro"] else []
  let quantTactics : List String :=
    if f.hasForall || f.hasExists then
      let ringTactics : List String :=
        if f.hasEq && (f.hasMul || f.hasPlus) then ["intros; ring", "intro; ring"] else []
      let arithTactics : List String :=
        if hasArithmeticSignal f then ["intros; omega", "intro; omega", "intros; linarith", "intros; nlinarith"] else []
      let logicTactics : List String :=
        if hasLogicSignal f then ["intros; tauto", "intro; tauto"] else []
      ringTactics ++ arithTactics ++ logicTactics
    else
      []
  let natStructTactics : List String :=
    if f.hasForall && f.hasNat then
      [ "intro n; cases n with | zero => simp | succ k => simp_all"
      , "intro n; induction n with | zero => simp | succ k ih => simp_all"
      , "intro n; induction n with | zero => simp | succ k ih => simp_all; omega"
      ]
    else
      []
  let listStructTactics : List String :=
    if f.hasForall && f.hasList then
      [ "intro l; cases l with | nil => simp | cons h t => simp"
      , "intro l; induction l with | nil => simp | cons h t ih => simp_all"
      , "intro l; induction l with | nil => simp | cons h t ih => simp_all; omega"
      ]
    else
      []
  (splitTactics ++ universalTactics ++ quantTactics ++ natStructTactics ++ listStructTactics).eraseDups

private def enforceBranchCoverage
    (goal : String)
    (rows : List DecodedCandidate)
    (branchBudget : Nat) : List DecodedCandidate :=
  let mustTry := preferredStructuralTactics goal
  if mustTry.isEmpty then
    rows.take (max 1 branchBudget)
  else
    let promoted :=
      mustTry.map (fun tactic =>
        match rows.find? (fun row => row.tactic = tactic) with
        | some row => row
        | none => mkInjectedCandidate tactic "search_priority")
    (dedupDecodedByTactic (promoted ++ rows)).take (max 1 branchBudget)

private def subgoalPreferredTactic (subgoal : String) : Option String :=
  let f := goalFeatures subgoal
  if f.hasAnd then
    some "constructor"
  else if f.hasForall && f.hasNat && f.hasOr &&
      (hasSubstr subgoal "∃ m, n = 1 + m" || hasSubstr subgoal "∃ m : Nat, n = m + 1"
        || hasSubstr subgoal "+ 1" || hasSubstr subgoal "1 +") then
    some "intro n; cases n with | zero => left; simp | succ k => right; refine ⟨k, ?_⟩; omega"
  else if f.hasForall && f.hasNat && f.hasOr &&
      (hasSubstr subgoal "Nat.pred" || hasSubstr subgoal ".pred.succ") then
    some "intro n; cases n with | zero => left; simp | succ k => right; simp"
  else if (f.hasForall || f.hasExists) && f.hasEq && (f.hasMul || f.hasPlus) then
    some "intros; ring"
  else if hasArithmeticSignal f && !hasLogicSignal f then
    if f.hasEq && f.hasMul then some "ring"
    else if f.hasEq && f.tokenCount <= 12 then some "norm_num"
    else if f.hasForall || f.hasExists then some "intros; omega"
    else some "omega"
  else if hasLogicSignal f && !hasArithmeticSignal f then
    if f.hasForall || f.hasExists then some "intros; tauto"
    else some "tauto"
  else if f.hasList && f.hasForall then
    if hasSubstr subgoal "foldl" || hasSubstr subgoal "length" then
      some "intro l; induction l with | nil => simp | cons h t ih => simp_all; omega"
    else
      some "intro l; induction l with | nil => simp | cons h t ih => simp_all"
  else
    none

private def solvedSubgoalScript?
    (group : SubgoalGroup)
    (idx : Nat) : Option (List (String × String)) :=
  match group.solved.find? (fun row => row.1 = idx) with
  | some row => some row.2
  | none => none

private def parentPrefixLenByTactic
    (parent child : List (String × String)) : Nat :=
  let rec go (rowsA rowsB : List (String × String)) (k : Nat) : Nat :=
    match rowsA, rowsB with
    | (_, ta) :: as, (_, tb) :: bs =>
        if ta = tb then go as bs (k + 1) else k
    | _, _ => k
  go parent child 0

private def composeGroupProof? (group : SubgoalGroup) : Option (List (String × String)) := do
  if group.subgoals.isEmpty then
    none
  let indexedSubgoals := List.zip (List.range group.subgoals.length) group.subgoals
  let solvedRows ← (indexedSubgoals.mapM fun entry => do
    let idx := entry.1
    solvedSubgoalScript? group idx)
  let prefixLen :=
    solvedRows.foldl (fun acc script => min acc (parentPrefixLenByTactic group.parentScript script)) group.parentScript.length
  let suffixes := solvedRows.map (fun script => script.drop prefixLen)
  let suffixJoined := suffixes.foldr (fun rows acc => rows ++ acc) []
  pure (group.parentScript.take prefixLen ++ suffixJoined)

private def updateGroupSolved
    (groups : List SubgoalGroup)
    (groupId subgoalIdx : Nat)
    (script : List (String × String)) : List SubgoalGroup :=
  groups.map (fun g =>
    if g.groupId = groupId then
      let filtered := g.solved.filter (fun row => row.1 ≠ subgoalIdx)
      { g with solved := (subgoalIdx, script) :: filtered }
    else
      g)

private def findGroup? (groups : List SubgoalGroup) (groupId : Nat) : Option SubgoalGroup :=
  groups.find? (fun g => g.groupId = groupId)

private def sameEnrichedSampleKey (a b : EnrichedTrainingSample) : Bool :=
  a.goal = b.goal &&
  a.expectedTactic = b.expectedTactic &&
  a.subgoalsSolved = b.subgoalsSolved &&
  a.totalSubgoals = b.totalSubgoals

private def pushUniqueEnriched
    (samplesRev : List EnrichedTrainingSample)
    (sample : EnrichedTrainingSample) : List EnrichedTrainingSample :=
  if samplesRev.any (fun row => sameEnrichedSampleKey row sample) then
    samplesRev
  else
    sample :: samplesRev

private def addObserverFailureSamples
    (samplesRev : List EnrichedTrainingSample)
    (rejectionsRev : List CandidateRejection) : List EnrichedTrainingSample :=
  rejectionsRev.foldl
    (fun acc rej =>
      if rej.reason = "observer_failed" then
        pushUniqueEnriched acc
          { goal := rej.nodeGoal
            expectedTactic := rej.tactic
            subgoalsSolved := 0
            totalSubgoals := 1
            compositionBonus := 0 }
      else
        acc)
    samplesRev

private def reprioritizeQueue (queue : List SearchNode) : List SearchNode :=
  queue.foldl (fun acc node => pushQueue node acc) []

private def boostGroupNodes (queue : List SearchNode) (groups : List SubgoalGroup) (groupId : Nat) : List SearchNode :=
  let reward :=
    match findGroup? groups groupId with
    | some g => hierarchicalSubgoalReward g.solved.length g.subgoals.length ((1 : Rat) / 2)
    | none => 0
  let priorityDelta := reward / 4
  let boosted := queue.map (fun node =>
    if node.groupId = some groupId then
      { node with priorityScore := clamp01 (node.priorityScore - priorityDelta) }
    else
      node)
  reprioritizeQueue boosted

partial def search
    (goal : String)
    (searchCfg : SearchConfig)
    (baseCfg : OrchestratorConfig := {})
    (contextHints : List String := [])
    (kanSelector : Option KANTacticSelector := none) : IO SearchResult := do
  let startMs ← IO.monoMsNow
  let laneCfg := laneConfigForSearch searchCfg baseCfg
  let root : SearchNode :=
    { goal := goal
      depth := 0
      parentTactic := none
      preferredTactic := none
      groupId := none
      groupSubgoalIndex := none
      priorityScore := 0
      proofScriptRev := []
      carry := none }

  let rec loop
      (queue : List SearchNode)
      (seen : List String)
      (seenShapes : List (Nat × String))
      (explored : Nat)
      (maxDepthSeen : Nat)
      (attempts : Nat)
      (backtracks : Nat)
      (treeRev : List SearchNode)
      (rejectionsRev : List CandidateRejection)
      (trainingSamplesRev : List (String × String))
      (enrichedSamplesRev : List EnrichedTrainingSample)
      (groups : List SubgoalGroup)
      (nextGroupId : Nat) : IO SearchResult := do
    let timeoutTriggered : Bool ←
      if searchCfg.searchTimeoutSeconds > 0 then do
        let now ← IO.monoMsNow
        let elapsedSec : Nat := (now - startMs) / 1000
        pure (decide (elapsedSec >= searchCfg.searchTimeoutSeconds))
      else
        pure false
    if timeoutTriggered then
      pure <|
        mkFailure "internal_timeout" explored maxDepthSeen attempts backtracks treeRev rejectionsRev
          trainingSamplesRev (addObserverFailureSamples enrichedSamplesRev rejectionsRev)
    else
      match queue with
      | [] =>
          pure <|
            mkFailure "queue_exhausted" explored maxDepthSeen attempts backtracks treeRev rejectionsRev
              trainingSamplesRev (addObserverFailureSamples enrichedSamplesRev rejectionsRev)
      | node :: rest =>
        let maxDepthSeen := max maxDepthSeen node.depth
        if attempts >= searchCfg.maxTotalAttempts then
          pure <|
            mkFailure "attempt_budget_exhausted" explored maxDepthSeen attempts backtracks treeRev rejectionsRev
              trainingSamplesRev (addObserverFailureSamples enrichedSamplesRev rejectionsRev)
        else if node.depth > searchCfg.maxDepth then
          loop rest seen seenShapes explored maxDepthSeen attempts backtracks treeRev rejectionsRev
            trainingSamplesRev enrichedSamplesRev groups nextGroupId
        else
          let shapeKey := goalShapeKey node.goal
          let seenByShape := seenShapes.any (fun row => row.1 = node.depth && row.2 = shapeKey)
          let skipBySeen := (seen.any (fun g => g = node.goal) || seenByShape) && node.groupId.isNone
          if skipBySeen then
            loop rest seen seenShapes explored maxDepthSeen attempts backtracks treeRev rejectionsRev
              trainingSamplesRev enrichedSamplesRev groups nextGroupId
          else
            let f := goalFeatures node.goal
            let branchBudget :=
              if f.hasAnd then max searchCfg.maxBranches searchCfg.conjunctionBranchBudget
              else searchCfg.maxBranches
            let useKANRouting := kanSelector.isSome
            let nodePreferred :=
              if useKANRouting then
                none
              else
                node.preferredTactic
            let closerOnly := node.preferredTactic.isSome && node.depth > 0 && !useKANRouting
            let runResult? :=
              if closerOnly then
                none
              else
                let nodeCfg := { laneCfg with preferredTactic := nodePreferred }
                some (run node.goal nodeCfg contextHints node.carry)
            let basePriority :=
              match runResult? with
              | some runResult => computePriority runResult.progressScore runResult.psrLoss
              | none => (1 : Rat) / 2
            let baseCandidatesRaw :=
              match runResult? with
              | some runResult =>
                  runResult.bestCandidates.take (max 1 branchBudget)
              | none =>
                  let preferred := match node.preferredTactic with | some t => [t] | none => []
                  let allTactics :=
                    (preferred ++ closerInjectionTactics node.goal
                      ++ compoundCloserInjectionTactics node.goal
                      ++ universalConjunctionSolverTactics node.goal).eraseDups
                  (allTactics.take (max 1 branchBudget)).map
                    (fun tactic => mkInjectedCandidate tactic "closer_fastpath")
            let kanCandidatesRaw :=
              match kanSelector with
              | some selector =>
                  let stateForKAN :=
                    match runResult? with
                    | some runResult => runResult.bestWeights
                    | none => (encodeGoal node.goal laneCfg.currentLens contextHints none).initial
                  decodeFromKANWeightsWithGoalAndCompositions
                    stateForKAN
                    node.goal
                    (max 1 branchBudget)
                    6
                    selector
              | none => []
            let candidatesRaw :=
              if kanCandidatesRaw.isEmpty then
                baseCandidatesRaw
              else
                dedupDecodedByTactic (kanCandidatesRaw ++ baseCandidatesRaw)
            let candidates :=
              if closerOnly then
                candidatesRaw.take 1
              else
                enforceBranchCoverage node.goal candidatesRaw branchBudget
            let pairs := candidates.map (fun cand => (node.goal, cand.tactic))
            let observations ←
              observeBatch pairs searchCfg.observerTimeoutSeconds (max 1 searchCfg.parallelSubgoalWorkers)
            let normalizedObs :=
              if observations.length = candidates.length then
                observations
              else
                observations ++
                  (candidates.drop observations.length).map (fun cand =>
                    { ok := false
                      remainingGoals := []
                      originalGoal := node.goal
                      appliedTactic := cand.tactic
                      stderr := "observe_batch_length_mismatch"
                      timedOut := false })
            let candidateObs := List.zip candidates normalizedObs
            let mut nextQueue := rest
            let mut attemptsNow := attempts
            let mut backtracksNow := backtracks
            let mut rejectionsNow := rejectionsRev
            let mut trainingSamplesNow := trainingSamplesRev
            let mut enrichedSamplesNow := enrichedSamplesRev
            let mut groupsNow := groups
            let mut nextGroupIdNow := nextGroupId
            let mut solved : Option SearchResult := none

            for entry in candidateObs do
              let cand := entry.1
              let obs := entry.2
              if solved.isSome then
                pure ()
              else if attemptsNow >= searchCfg.maxTotalAttempts then
                pure ()
              else
                attemptsNow := attemptsNow + 1
                if obs.ok then
                  let scriptRev := (node.goal, cand.tactic) :: node.proofScriptRev
                  if obs.remainingGoals.isEmpty then
                    let script := scriptRev.reverse
                    let directSample := (node.goal, cand.tactic)
                    let directEnriched : EnrichedTrainingSample :=
                      { goal := node.goal
                        expectedTactic := cand.tactic
                        subgoalsSolved := 1
                        totalSubgoals := 1
                        compositionBonus := 0 }
                    match node.groupId, node.groupSubgoalIndex with
                    | some gid, some subIdx =>
                        trainingSamplesNow := directSample :: trainingSamplesNow
                        enrichedSamplesNow := pushUniqueEnriched enrichedSamplesNow directEnriched
                        groupsNow := updateGroupSolved groupsNow gid subIdx script
                        match findGroup? groupsNow gid with
                        | some groupState =>
                            let solvedCount := groupState.solved.length
                            let totalCount := groupState.subgoals.length
                            if solvedCount > 0 && solvedCount < totalCount then
                              let partialProgressSample : EnrichedTrainingSample :=
                                { goal := groupState.parentGoal
                                  expectedTactic := groupState.parentTactic
                                  subgoalsSolved := solvedCount
                                  totalSubgoals := totalCount
                                  compositionBonus := (1 : Rat) / 2 }
                              enrichedSamplesNow := pushUniqueEnriched enrichedSamplesNow partialProgressSample
                            else
                              pure ()
                            match composeGroupProof? groupState with
                            | some composedScript =>
                                let scriptOk ← recheckProofScript goal composedScript (max 30 (searchCfg.observerTimeoutSeconds * 2))
                                if scriptOk then
                                  let parentSample := (groupState.parentGoal, groupState.parentTactic)
                                  let parentEnriched : EnrichedTrainingSample :=
                                    { goal := groupState.parentGoal
                                      expectedTactic := groupState.parentTactic
                                      subgoalsSolved := groupState.solved.length
                                      totalSubgoals := groupState.subgoals.length
                                      compositionBonus := (1 : Rat) / 2 }
                                  let trainingFinal := parentSample :: trainingSamplesNow
                                  let enrichedFinal :=
                                    addObserverFailureSamples
                                      (pushUniqueEnriched enrichedSamplesNow parentEnriched)
                                      rejectionsNow
                                  let tree := (node :: treeRev).reverse
                                  solved := some
                                    { proved := true
                                      proofScript := composedScript
                                      trainingSamples := trainingFinal.reverse
                                      enrichedTrainingSamples := enrichedFinal.reverse
                                      nodesExplored := explored + 1
                                      maxDepthReached := maxDepthSeen
                                      totalAttempts := attemptsNow
                                      backtrackCount := backtracksNow
                                      searchTree := tree
                                      candidateRejections := rejectionsNow.reverse
                                      reason := "proved" }
                                else
                                  backtracksNow := backtracksNow + 1
                                  rejectionsNow := mkRejection node cand.tactic "group_proof_recheck_failed" [] obs.stderr :: rejectionsNow
                            | none =>
                                nextQueue := boostGroupNodes nextQueue groupsNow gid
                        | none =>
                            backtracksNow := backtracksNow + 1
                            rejectionsNow := mkRejection node cand.tactic "group_state_missing" [] obs.stderr :: rejectionsNow
                    | _, _ =>
                        let scriptOk ← recheckProofScript goal script (max 30 (searchCfg.observerTimeoutSeconds * 2))
                        if scriptOk then
                          trainingSamplesNow := directSample :: trainingSamplesNow
                          enrichedSamplesNow := pushUniqueEnriched enrichedSamplesNow directEnriched
                          let enrichedFinal :=
                            addObserverFailureSamples enrichedSamplesNow rejectionsNow
                          let tree := (node :: treeRev).reverse
                          solved := some
                            { proved := true
                              proofScript := script
                              trainingSamples := trainingSamplesNow.reverse
                              enrichedTrainingSamples := enrichedFinal.reverse
                              nodesExplored := explored + 1
                              maxDepthReached := maxDepthSeen
                              totalAttempts := attemptsNow
                              backtrackCount := backtracksNow
                              searchTree := tree
                              candidateRejections := rejectionsNow.reverse
                              reason := "proved" }
                        else
                          backtracksNow := backtracksNow + 1
                          rejectionsNow := mkRejection node cand.tactic "proof_recheck_failed" [] obs.stderr :: rejectionsNow
                  else
                    let remaining := (obs.remainingGoals.map String.trim).filter (fun g => !g.isEmpty)
                    if remaining.all isObserverSentinel then
                      backtracksNow := backtracksNow + 1
                      rejectionsNow := mkRejection node cand.tactic "observer_unresolved" remaining obs.stderr :: rejectionsNow
                    else
                      let carryNext :=
                        if searchCfg.warmStart then
                          match runResult? with
                          | some runResult => some runResult.bestWeights
                          | none => none
                        else
                          none
                      let validRemaining :=
                        remaining.filter (fun sg => !isObserverSentinel sg && !sg.isEmpty)
                      let mut childGroupId : Option Nat := none
                      if validRemaining.length > 1 then
                        let gid := nextGroupIdNow
                        nextGroupIdNow := nextGroupIdNow + 1
                        childGroupId := some gid
                        let parentScript := scriptRev.reverse
                        groupsNow :=
                          { groupId := gid
                            parentGoal := node.goal
                            parentTactic := cand.tactic
                            parentScript := parentScript
                            subgoals := validRemaining
                            solved := [] } :: groupsNow
                      let children :=
                        match childGroupId with
                        | some gid =>
                            let indexedRemaining := List.zip (List.range validRemaining.length) validRemaining
                            indexedRemaining.filterMap (fun entry =>
                              let subIdx := entry.1
                              let sg := entry.2
                              let dPenalty := (Int.ofNat (node.depth + 1) : Rat) / 100
                              some
                                { goal := sg
                                  depth := node.depth + 1
                                  parentTactic := some cand.tactic
                                  preferredTactic := if useKANRouting then none else subgoalPreferredTactic sg
                                  groupId := some gid
                                  groupSubgoalIndex := some subIdx
                                  priorityScore := clamp01 (basePriority + dPenalty)
                                  proofScriptRev := scriptRev
                                  carry := carryNext })
                        | none =>
                            validRemaining.filterMap (fun sg =>
                              let dPenalty := (Int.ofNat (node.depth + 1) : Rat) / 100
                              some
                                { goal := sg
                                  depth := node.depth + 1
                                  parentTactic := some cand.tactic
                                  preferredTactic := if useKANRouting then none else subgoalPreferredTactic sg
                                  groupId := none
                                  groupSubgoalIndex := none
                                  priorityScore := clamp01 (basePriority + dPenalty)
                                  proofScriptRev := scriptRev
                                  carry := carryNext })
                      if children.isEmpty then
                        backtracksNow := backtracksNow + 1
                        rejectionsNow := mkRejection node cand.tactic "no_children_after_filter" remaining obs.stderr :: rejectionsNow
                      else
                        nextQueue := pushMany children nextQueue
                else
                  backtracksNow := backtracksNow + 1
                  let reason :=
                    if obs.timedOut then
                      "observer_timeout"
                    else
                      "observer_failed"
                  rejectionsNow := mkRejection node cand.tactic reason [] obs.stderr :: rejectionsNow

            let goalPreviewRaw := if node.goal.length > 90 then node.goal.take 90 else node.goal
            let goalPreview := oneLine goalPreviewRaw
            IO.eprintln s!"[SEARCH_PROGRESS] explored={explored + 1} depth={node.depth} goal=\"{goalPreview}\" goal_len={node.goal.length} candidates={candidates.length} solved={solved.isSome} backtracks={backtracksNow}"
            match solved with
            | some done => pure done
            | none =>
                if attemptsNow >= searchCfg.maxTotalAttempts then
                  pure <|
                    mkFailure "attempt_budget_exhausted" (explored + 1) maxDepthSeen attemptsNow backtracksNow
                      (node :: treeRev) rejectionsNow trainingSamplesNow
                      (addObserverFailureSamples enrichedSamplesNow rejectionsNow)
                else
                  loop
                    nextQueue
                    (node.goal :: seen)
                    ((node.depth, shapeKey) :: seenShapes)
                    (explored + 1)
                    maxDepthSeen
                    attemptsNow
                    backtracksNow
                    (node :: treeRev)
                    rejectionsNow
                    trainingSamplesNow
                    enrichedSamplesNow
                    groupsNow
                    nextGroupIdNow
  loop [root] [] [] 0 0 0 0 [] [] [] [] [] 0

end DifferentiableATP
end ATP
end HeytingLean
