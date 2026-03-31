import HeytingLean.ATP.LensTransport.LensMove
import HeytingLean.ATP.DifferentiableATP.SearchTree

/-
- source_type: ATP infrastructure (search extension)
- attribution_status: n/a
- claim_status: n/a
- proof_status: proved
-/

namespace HeytingLean
namespace ATP
namespace LensTransport

open HeytingLean.Embeddings
open HeytingLean.LoF.Combinators.Differential.Compute

/-- Extracted proof script emitted by `SearchTree.search`. -/
abbrev ProofScript := List (String × String)

/-- Result of a lens-transported search attempt. -/
structure LensSearchResult where
  /-- Whether a proof was found. -/
  proved : Bool
  /-- The lens in which the proof was found (if any). -/
  proofLens : Option LensID
  /-- Concrete script returned by `SearchTree.search` (if solved). -/
  proofScript : Option ProofScript
  /-- Whether back-transport to the origin lens is certified non-lossy. -/
  backTransportCertified : Bool
  /-- Total nodes explored across all lenses. -/
  nodesExplored : Nat
  /-- Per-lens node counts. -/
  nodesPerLens : List (LensID × Nat)
  /-- Lens transitions taken in the successful path (if any). -/
  transitionPath : List LensID
  /-- Total wall time in milliseconds. -/
  wallMs : Nat
  deriving Repr

/-- Configuration for lens-transported search. -/
structure LensSearchConfig where
  /-- The starting lens. -/
  startLens : LensID := .omega
  /-- Maximum search depth per lens (tactic steps, not counting transitions). -/
  maxDepthPerLens : Nat := 50
  /-- Maximum total nodes to explore across all lenses. -/
  maxTotalNodes : Nat := 10000
  /-- Whether to try lens transitions when tactic search is stuck. -/
  enableLensTransitions : Bool := true
  /-- Node budget to spend in a lens before trying a transition. -/
  nodesBeforeTransition : Nat := 100
  /-- Whether to try the proof in the original lens first (before any transition). -/
  tryOriginalFirst : Bool := true
  deriving Repr

private def fallbackGoalExprOfFSum (goal : FSum) : String :=
  -- Non-silent fallback for legacy callers that only provide an FSum seed.
  -- This avoids the previous `⊢ True` stub behavior.
  s!"⊢ fsum_seed_len_{goal.length}"

private def searchBudget (total spent chunk : Nat) : Nat :=
  if spent >= total then 0
  else min chunk (total - spent)

/-- Run a standard tactic search in a single lens via `SearchTree.search`. -/
def searchInLensWithGoalExpr
    (lens : LensID)
    (goalExpr : String)
    (goal : FSum)
    (searchCfg : DifferentiableATP.SearchConfig)
    (baseCfg : DifferentiableATP.OrchestratorConfig) :
    IO (Bool × Option ProofScript × Nat) := do
  let _projGoal := DifferentiableATP.lensProjection lens goal
  let runSearchCfg : DifferentiableATP.SearchConfig :=
    { searchCfg with
      maxDepth := max 1 searchCfg.maxDepth
      maxTotalAttempts := max 1 searchCfg.maxTotalAttempts
      maxBranches := max 1 searchCfg.maxBranches
      conjunctionBranchBudget := max 1 searchCfg.conjunctionBranchBudget
      parallelSubgoalWorkers := max 1 searchCfg.parallelSubgoalWorkers
      gdBudget := max 1 searchCfg.gdBudget
      macroSteps := max 1 searchCfg.macroSteps
      subgoalLensBudget := max 1 searchCfg.subgoalLensBudget
      observerTimeoutSeconds := max 1 searchCfg.observerTimeoutSeconds }
  let runBaseCfg : DifferentiableATP.OrchestratorConfig :=
    { baseCfg with
      currentLens := lens
      maxLaneChanges := baseCfg.maxLaneChanges
      lensBudget := max 1 baseCfg.lensBudget
      decodeTopK := max 1 baseCfg.decodeTopK
      useStructuralInjection := baseCfg.useStructuralInjection
      useMultiwayGD := baseCfg.useMultiwayGD
      maxMacroSteps := max 1 baseCfg.maxMacroSteps
      enableTacticDiversification := baseCfg.enableTacticDiversification
      diversityTopK := max 1 baseCfg.diversityTopK
      oracleExamples := baseCfg.oracleExamples }
  let res ← DifferentiableATP.search goalExpr runSearchCfg runBaseCfg [] none
  let script := if res.proved then some res.proofScript else none
  pure (res.proved, script, res.nodesExplored)

/-- Run a standard tactic search in a single lens via `SearchTree.search`. -/
def searchInLens
    (lens : LensID)
    (goal : FSum)
    (maxNodes : Nat)
    (maxDepth : Nat) :
    IO (Bool × Option ProofScript × Nat) := do
  let basis := DifferentiableATP.basisForLens lens
  let searchCfg : DifferentiableATP.SearchConfig :=
    { maxDepth := max 1 maxDepth
      maxTotalAttempts := max 1 maxNodes
      maxBranches := max 1 basis.length }
  let baseCfg : DifferentiableATP.OrchestratorConfig :=
    { currentLens := lens
      maxLaneChanges := 0
      lensBudget := 1
      decodeTopK := max 1 basis.length
      useStructuralInjection := true }
  searchInLensWithGoalExpr lens (fallbackGoalExprOfFSum goal) goal searchCfg baseCfg

private def withWallMs (startedMs : Nat) (r : LensSearchResult) : IO LensSearchResult := do
  let doneMs ← IO.monoMsNow
  pure { r with wallMs := doneMs - startedMs }

/-- Main lens-transported search algorithm (original lens, 1-hop, then 2-hop). -/
def lensTransportedSearchWithGoalExpr
    (goalExpr : String)
    (goal : FSum)
    (cfg : LensSearchConfig)
    (searchCfg : DifferentiableATP.SearchConfig)
    (baseCfg : DifferentiableATP.OrchestratorConfig) :
    IO LensSearchResult := do
  let startedMs ← IO.monoMsNow
  let mut totalNodes := 0
  let mut nodesPerLens : List (LensID × Nat) := []
  let origLens := cfg.startLens

  if cfg.tryOriginalFirst then
    let budget := searchBudget cfg.maxTotalNodes totalNodes cfg.nodesBeforeTransition
    if budget > 0 then
      let perLensSearchCfg : DifferentiableATP.SearchConfig :=
        { searchCfg with
          maxDepth := max 1 cfg.maxDepthPerLens
          maxTotalAttempts := max 1 budget }
      let (proved, proof, nodes) ←
        searchInLensWithGoalExpr origLens goalExpr goal perLensSearchCfg baseCfg
      totalNodes := totalNodes + nodes
      nodesPerLens := (origLens, nodes) :: nodesPerLens
      if proved then
        return ← withWallMs startedMs {
          proved := true
          proofLens := some origLens
          proofScript := proof
          backTransportCertified := true
          nodesExplored := totalNodes
          nodesPerLens := nodesPerLens.reverse
          transitionPath := [origLens]
          wallMs := 0
        }

  if cfg.enableLensTransitions then
    let initState : LensProofState :=
      { currentLens := origLens
        state := goal
        goal := goal
        lensHistory := [origLens]
        depth := 0 }
    let targets := availableLensMoves initState

    for dst in targets do
      if totalNodes >= cfg.maxTotalNodes then
        break
      let budget := searchBudget cfg.maxTotalNodes totalNodes cfg.nodesBeforeTransition
      if budget = 0 then
        break
      let perLensSearchCfg : DifferentiableATP.SearchConfig :=
        { searchCfg with
          maxDepth := max 1 cfg.maxDepthPerLens
          maxTotalAttempts := max 1 budget }
      let (proved, proof, nodes) ←
        searchInLensWithGoalExpr dst goalExpr goal perLensSearchCfg baseCfg
      totalNodes := totalNodes + nodes
      nodesPerLens := (dst, nodes) :: nodesPerLens
      if proved then
        let backOK := (transportProofBack? { initState with currentLens := dst } origLens []).isSome
        if backOK then
          return ← withWallMs startedMs {
            proved := true
            proofLens := some dst
            proofScript := proof
            backTransportCertified := true
            nodesExplored := totalNodes
            nodesPerLens := nodesPerLens.reverse
            transitionPath := [origLens, dst]
            wallMs := 0
          }

    for mid in targets do
      if totalNodes >= cfg.maxTotalNodes then
        break
      let midGoal := DifferentiableATP.lensProjection mid goal
      let midState : LensProofState :=
        { currentLens := mid
          state := midGoal
          goal := midGoal
          lensHistory := [origLens, mid]
          depth := 1 }
      let hop2Targets := availableLensMoves midState
      for dst2 in hop2Targets do
        if totalNodes >= cfg.maxTotalNodes then
          break
        let budget := searchBudget cfg.maxTotalNodes totalNodes cfg.nodesBeforeTransition
        if budget = 0 then
          break
        let perLensSearchCfg : DifferentiableATP.SearchConfig :=
          { searchCfg with
            maxDepth := max 1 cfg.maxDepthPerLens
            maxTotalAttempts := max 1 budget }
        let (proved, proof, nodes) ←
          searchInLensWithGoalExpr dst2 goalExpr midGoal perLensSearchCfg baseCfg
        totalNodes := totalNodes + nodes
        nodesPerLens := (dst2, nodes) :: nodesPerLens
        if proved then
          let backOK := (transportProofBack? { midState with currentLens := dst2 } origLens []).isSome
          if backOK then
            return ← withWallMs startedMs {
              proved := true
              proofLens := some dst2
              proofScript := proof
              backTransportCertified := true
              nodesExplored := totalNodes
              nodesPerLens := nodesPerLens.reverse
              transitionPath := [origLens, mid, dst2]
              wallMs := 0
            }

  return ← withWallMs startedMs {
    proved := false
    proofLens := none
    proofScript := none
    backTransportCertified := false
    nodesExplored := totalNodes
    nodesPerLens := nodesPerLens.reverse
    transitionPath := []
    wallMs := 0
  }

/-- Main lens-transported search algorithm (placeholder-goal fallback). -/
def lensTransportedSearch
    (goal : FSum)
    (cfg : LensSearchConfig) :
    IO LensSearchResult := do
  let basis := DifferentiableATP.basisForLens cfg.startLens
  let searchCfg : DifferentiableATP.SearchConfig :=
    { maxDepth := max 1 cfg.maxDepthPerLens
      maxTotalAttempts := max 1 cfg.nodesBeforeTransition
      maxBranches := max 1 basis.length }
  let baseCfg : DifferentiableATP.OrchestratorConfig :=
    { currentLens := cfg.startLens
      maxLaneChanges := 0
      lensBudget := 1
      decodeTopK := max 1 basis.length
      useStructuralInjection := true }
  lensTransportedSearchWithGoalExpr (fallbackGoalExprOfFSum goal) goal cfg searchCfg baseCfg

end LensTransport
end ATP
end HeytingLean
