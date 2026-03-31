import HeytingLean.PathIntegral.Search
import HeytingLean.ATP.DifferentiableATP.SearchTree
import HeytingLean.ATP.DifferentiableATP.KANTacticSelector
import HeytingLean.ATP.DifferentiableATP.GoalEncoder
import HeytingLean.ATP.DifferentiableATP.TacticDecoder
import HeytingLean.ATP.DifferentiableATP.LensGDOrchestrator

/-!
# PathIntegral.Adapter

Bridge the PathIntegral proof-path search surface onto the live
`DifferentiableATP.SearchTree` goal/tactic contracts.
-/

namespace HeytingLean
namespace PathIntegral
namespace Adapter

open HeytingLean.Embeddings
open HeytingLean.ATP
open HeytingLean.ATP.DifferentiableATP
open HeytingLean.LoF.Combinators.Differential.Compute

private def fallbackGoalSeed : FSum := [(.K, 1)]

private def hasSubstr (text needle : String) : Bool :=
  if needle.isEmpty then
    false
  else
    (text.splitOn needle).length > 1

private def stateGoalText (s : ProofState) : String :=
  let txt := s.context.trim
  if txt.isEmpty then reprStr s.goal else txt

/-- Reuse the DifferentiableATP heuristic encoder instead of inventing a second
goal parser for the adapter boundary. -/
def parseGoalToFSum (goal : String) (lens : LensID := .omega) : FSum :=
  let encoded := encodeGoal goal lens
  if encoded.initial.isEmpty then fallbackGoalSeed else encoded.initial

def searchNodeToProofState (node : SearchNode) (lens : LensID := .omega) : ProofState :=
  { lens := lens
    goal := node.carry.getD (parseGoalToFSum node.goal lens)
    context := node.goal
    depth := node.depth
    history := List.replicate node.depth lens }

def proofStateToSearchNode (state : ProofState) : SearchNode :=
  { goal := stateGoalText state
    depth := state.depth
    parentTactic := none
    preferredTactic := none
    groupId := none
    groupSubgoalIndex := none
    priorityScore := 0
    proofScriptRev := []
    carry := some state.goal }

def proofPathToScript (path : ProofPath) : List (String × String) :=
  path.steps.map (fun step => (stateGoalText step.source, step.tactic))

private def structuralTactics (goal : String) : List String :=
  let f := goalFeatures goal
  let rows0 : List String :=
    if f.hasAnd || f.hasIff then ["constructor", "apply And.intro"] else []
  let rows1 : List String :=
    if f.hasForall || f.hasExists then rows0 ++ ["intro", "intros"] else rows0
  let rows2 : List String :=
    if f.hasOr then rows1 ++ ["cases"] else rows1
  if (f.hasNat || f.hasList) && f.hasForall then
    (rows2 ++
      [ "intro n; induction n with | zero => simp | succ k ih => simp_all"
      , "intro l; induction l with | nil => simp | cons h t ih => simp_all"
      ]).eraseDups
  else
    rows2.eraseDups

private def arithmeticSignal (f : GoalFeatures) : Bool :=
  f.hasNat || f.hasInt || f.hasReal || f.hasPlus || f.hasMul || f.hasLt || f.hasLe

private def logicSignal (f : GoalFeatures) : Bool :=
  f.hasArrow || f.hasIff || f.hasAnd || f.hasOr || f.hasNot || f.hasTrue || f.hasFalse

private def tacticLikelyCloses (goal : String) (tactic : String) : Bool :=
  let f := goalFeatures goal
  let lower := tactic.toLower
  (hasSubstr lower "rfl" && f.hasEq) ||
  (hasSubstr lower "exact true.intro" && f.hasTrue) ||
  (hasSubstr lower "omega" && arithmeticSignal f) ||
  (hasSubstr lower "linarith" && arithmeticSignal f) ||
  (hasSubstr lower "nlinarith" && arithmeticSignal f) ||
  (hasSubstr lower "ring" && arithmeticSignal f && f.hasEq) ||
  (hasSubstr lower "norm_num" && arithmeticSignal f) ||
  (hasSubstr lower "tauto" && logicSignal f) ||
  (hasSubstr lower "decide" && logicSignal f) ||
  (hasSubstr lower "aesop" && logicSignal f) ||
  (hasSubstr lower "simp" && (logicSignal f || f.hasEq))

private def residualGoal (state : ProofState) (tactic : String) : FSum :=
  let goal := stateGoalText state
  if tacticLikelyCloses goal tactic then
    []
  else
    let narrowed := topTermsByAbs state.goal 2
    if narrowed.isEmpty then
      fallbackGoalSeed
    else if narrowed = state.goal then
      match narrowed with
      | [] => []
      | [single] =>
          if hasSubstr tactic.toLower "intro" || hasSubstr tactic.toLower "cases" then
            []
          else
            [single]
      | head :: _ => [head]
    else
      narrowed

def standardConstructors (state : ProofState) : List (TacticId × FSum) :=
  let goal := stateGoalText state
  let decoded := decodeFromWeights state.goal 6 |>.map (fun row => row.tactic)
  let learned := decodeFromLearnedWeights state.goal 6 |>.map (fun row => row.tactic)
  let tactics :=
    (structuralTactics goal ++
      closerInjectionTactics goal ++
      compoundCloserInjectionTactics goal ++
      universalConjunctionSolverTactics goal ++
      learned ++ decoded).eraseDups
  let guaranteed := if tactics.isEmpty then ["simp", "rfl"] else tactics
  guaranteed.map (fun tactic => (tactic, residualGoal state tactic))

def standardGoalClosed (state : ProofState) : Bool :=
  state.goal = []

def runPathIntegralSearchResult
    (goal : String)
    (lens : LensID := .omega)
    (cfg : HeytingLean.PathIntegral.SearchConfig := {}) : Option SearchResult :=
  let initial := searchNodeToProofState
    { goal := goal
      depth := 0
      parentTactic := none
      preferredTactic := none
      groupId := none
      groupSubgoalIndex := none
      priorityScore := 0
      proofScriptRev := []
      carry := none }
    lens
  pathIntegralSearchResult cfg initial sheafTransport standardConstructors standardGoalClosed

def runPathIntegralSearch
    (goal : String)
    (lens : LensID := .omega)
    (cfg : HeytingLean.PathIntegral.SearchConfig := {}) : Option ProofPath :=
  (runPathIntegralSearchResult goal lens cfg).map SearchResult.path

end Adapter
end PathIntegral
end HeytingLean
