import HeytingLean.PathIntegral.ObstructionMonitor
import HeytingLean.PathIntegral.AnnealingTheory
import HeytingLean.ATP.LaneChanging
import HeytingLean.ATP.LensTransport.FaithfulTransportGraph

/-!
# PathIntegral.Search

Executable path-integral beam search over proof space.
-/

namespace HeytingLean
namespace PathIntegral

open HeytingLean.Embeddings
open HeytingLean.ATP
open HeytingLean.ATP.DifferentiableATP
open HeytingLean.LoF.Combinators.Differential.Compute

structure SearchConfig where
  beamWidth : Nat := 10
  expansionFactor : Nat := 5
  initialBeta : Float := 1.0
  schedule : AnnealingSchedule := .linear 0.1
  maxSteps : Nat := 100
  obstructionCheckInterval : Nat := 10
  deriving Repr

structure SearchState where
  beam : List (ProofPath × Float)
  beta : Float
  step : Nat
  completed : List ProofPath
  deriving Repr

structure SearchResult where
  path : ProofPath
  finalBeta : Float
  finalStep : Nat
  deriving Repr

private def insertByScoreDesc (x : ProofPath × Float) : List (ProofPath × Float) → List (ProofPath × Float)
  | [] => [x]
  | y :: ys =>
      if x.2 > y.2 then
        x :: y :: ys
      else
        y :: insertByScoreDesc x ys

private def sortByScoreDesc (xs : List (ProofPath × Float)) : List (ProofPath × Float) :=
  xs.foldl (fun acc x => insertByScoreDesc x acc) []

private def extendStateSameLens (s : ProofState) (goal : FSum) : ProofState :=
  { s with goal := goal, depth := s.depth + 1, history := s.lens :: s.history }

private def extendStateNewLens (s : ProofState) (dst : LensID) (goal : FSum) : ProofState :=
  {
    lens := dst
    goal := goal
    context := s.context
    depth := s.depth + 1
    history := dst :: s.history
  }

def findEquivalents (s : ProofState)
    (T : LaxCrossLensTransport SheafCarrier FSum := sheafTransport) :
    List (LensID × ProofState) :=
  ATP.LensTransport.allLenses.filterMap fun l =>
    if l ≠ s.lens then
      let transported := LaxCrossLensTransport.forward T s.lens l s.goal
      if transported = [] then
        none
      else
        some (l, extendStateNewLens s l transported)
    else
      none

def assessPaths (s : ProofState)
    (T : LaxCrossLensTransport SheafCarrier FSum := sheafTransport)
    (constructors : ProofState → List (TacticId × FSum))
    : List (ProofStep × Float) :=
  let localSteps := (constructors s).map fun (tac, result) =>
    let step : ProofStep := {
      source := s
      target := extendStateSameLens s result
      tactic := tac
      lensTransition := none
    }
    (step, stepActionFloat step)
  let laneChanges := (findEquivalents s T).map fun (l, s') =>
    let step : ProofStep := {
      source := s
      target := s'
      tactic := s!"transport:{reprStr l}"
      lensTransition := some (s.lens, l)
    }
    (step, stepActionFloat step)
  localSteps ++ laneChanges

def decideLane (β : Float) (candidates : List (ProofStep × Float))
    : List (ProofStep × Float) :=
  let weights := candidates.map fun (s, a) => (s, Float.exp (-β * a))
  let total := weights.foldl (fun acc (_, w) => acc + w) 0
  if total == 0 then
    weights
  else
    weights.map fun (s, w) => (s, w / total)

private def extendPath (p : ProofPath) (step : ProofStep) : ProofPath :=
  ProofPath.comp p (ProofPath.singleton step)

def shouldCheckObstruction (cfg : SearchConfig) (step : Nat) : Bool :=
  if cfg.obstructionCheckInterval = 0 then
    false
  else
    step % cfg.obstructionCheckInterval == 0

def pruneObstructed (cfg : SearchConfig) (step : Nat)
    (ranked : List (ProofPath × Float)) : List (ProofPath × Float) :=
  if shouldCheckObstruction cfg step then
    (partitionByObstruction ranked).1
  else
    ranked

def beamSearchStep (cfg : SearchConfig) (state : SearchState)
    (T : LaxCrossLensTransport SheafCarrier FSum := sheafTransport)
    (constructors : ProofState → List (TacticId × FSum))
    (isGoalClosed : ProofState → Bool)
    : SearchState :=
  let expansions :=
    state.beam.foldr (fun (entry : ProofPath × Float) acc =>
      let path := entry.1
      let pathScore := entry.2
      let candidates := assessPaths path.finish T constructors
      let weighted := (decideLane state.beta candidates).take cfg.expansionFactor
      let produced := weighted.map fun (step, localScore) =>
        let newPath := extendPath path step
        let combinedScore := pathScore * localScore
        (newPath, combinedScore)
      produced ++ acc) []
  let ranked := sortByScoreDesc expansions
  let completedNow := ranked.filterMap fun (path, _) =>
    if isGoalClosed path.finish then some path else none
  let filtered := pruneObstructed cfg state.step ranked
  let surviving := (filtered.filter fun (path, _) => !isGoalClosed path.finish).take cfg.beamWidth
  let nextStep := state.step + 1
  {
    beam := surviving
    beta := cfg.schedule.nextBeta cfg.initialBeta state.beta nextStep surviving
    step := nextStep
    completed := state.completed ++ completedNow
  }

private def bestCompleted? (β : Float) (completed : List ProofPath) : Option ProofPath :=
  sortByScoreDesc (completed.map fun p => (p, pathWeightFloat β p)) |>.head?.map Prod.fst

private def finalizeResult (st : SearchState) : Option SearchResult :=
  (bestCompleted? st.beta st.completed).map fun path =>
    { path := path, finalBeta := st.beta, finalStep := st.step }

def pathIntegralSearchResult (cfg : SearchConfig)
    (initialGoal : ProofState)
    (T : LaxCrossLensTransport SheafCarrier FSum := sheafTransport)
    (constructors : ProofState → List (TacticId × FSum))
    (isGoalClosed : ProofState → Bool)
    : Option SearchResult :=
  let initialPath := ProofPath.id initialGoal
  let initialState : SearchState := {
    beam := [(initialPath, 1.0)]
    beta := cfg.initialBeta
    step := 0
    completed := []
  }
  let rec go (fuel : Nat) (st : SearchState) : Option SearchResult :=
    match fuel with
    | 0 =>
        finalizeResult st
    | Nat.succ fuel' =>
        if st.completed.isEmpty then
          let next := beamSearchStep cfg st T constructors isGoalClosed
          if next.beam.isEmpty then
            none
          else
            go fuel' next
        else
          finalizeResult st
  go cfg.maxSteps initialState

def pathIntegralSearch (cfg : SearchConfig)
    (initialGoal : ProofState)
    (T : LaxCrossLensTransport SheafCarrier FSum := sheafTransport)
    (constructors : ProofState → List (TacticId × FSum))
    (isGoalClosed : ProofState → Bool)
    : Option ProofPath :=
  (pathIntegralSearchResult cfg initialGoal T constructors isGoalClosed).map SearchResult.path

end PathIntegral
end HeytingLean
