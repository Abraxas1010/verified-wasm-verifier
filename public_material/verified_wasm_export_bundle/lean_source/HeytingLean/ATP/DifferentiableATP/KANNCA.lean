import HeytingLean.ATP.DifferentiableATP.GraphNCA
import HeytingLean.ATP.DifferentiableATP.KANTacticSelector

/-!
# ATP.DifferentiableATP.KANNCA

Track C runtime surface:
- KAN-enhanced NCA updates over reduction neighborhoods,
- explicit outcome structure for ablation benchmarking,
- symbolic summaries carried from KAN edge functions.
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

private def blendFeatures (a b : Array Rat) : Array Rat :=
  let dim := max a.size b.size
  ((List.range dim).map (fun i => (a.getD i 0 + b.getD i 0) / 2)).toArray

structure KANCellUpdateRule where
  selector : KANTacticSelector := warmStartSelector
  ncaRule : NCAUpdateRule := defaultNCAUpdateRule
  maxSteps : Nat := 12
  tolerance : Rat := (1 : Rat) / 1000
  perturb : Option NCAPerturbConfig := none
  deriving Repr

structure KANNCAOutcome where
  finalState : NCAState
  converged : Bool
  stepsUsed : Nat
  stabilityScore : Rat
  candidates : List DecodedCandidate
  symbolicSummaries : List String
  deriving Repr

private def encodeCellForKAN (cell : NCACell) : FSum :=
  add (single cell.term cell.weight) (single .K cell.alive)

private def alignLogits (dim : Nat) (rows : List DecodedCandidate) : Array Rat :=
  let picked := rows.take (max 1 dim)
  ((List.range (max 1 dim)).map (fun i =>
    match picked[i]? with
    | some row => row.confidence
      | none => 0)).toArray

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

private def kanDrivenApply (rule : KANCellUpdateRule) (state : NCAState) (cell : NCACell) : NCACell :=
  let perception := perceiveNeighbors rule.ncaRule state cell
  let ranked :=
    decodeFromKANWeightsWithGoalFeatures
      (encodeCellForKAN cell)
      state.goalFeatures
      (max 1 rule.ncaRule.tacticDim)
      rule.selector
  let confidence :=
    if ranked.isEmpty then 0 else absRat ((ranked.headD (decodeComb .K)).confidence)
  let meanW := arrayGetRat perception 0
  let meanAlive := arrayGetRat perception 1
  let goalW := arrayGetRat state.goalFeatures 0
  let goalAlive := arrayGetRat state.goalFeatures 1
  let newWeight :=
    (1 - rule.ncaRule.decayRate) * cell.weight
      + rule.ncaRule.growthScale * meanW
      + (rule.ncaRule.growthScale / 2) * confidence
      + (rule.ncaRule.growthScale / 4) * goalW
  let newAlive :=
    clamp01
      ((1 - rule.ncaRule.decayRate) * cell.alive
        + (rule.ncaRule.growthScale * meanAlive)
        + confidence / 10
        + (rule.ncaRule.growthScale / 2) * goalAlive)
  let logits := alignLogits rule.ncaRule.tacticDim ranked
  let newFeatures := (blendFeatures (blendFeatures cell.features perception) state.goalFeatures)
  {
    cell with
    weight := newWeight
    features := newFeatures
    tacticLogits := logits
    alive := newAlive
    age := cell.age + 1
  }

def kanNCAStep (rule : KANCellUpdateRule) (state : NCAState) : NCAState :=
  let updated := state.cells.map (kanDrivenApply rule state)
  let grown := growCells rule.ncaRule { state with cells := updated, step := state.step + 1 }
  pruneCells grown rule.ncaRule.aliveThreshold

private def isStableKANNCA (prev curr : NCAState) (tol : Rat) : Bool :=
  DifferentiableATP.isStable prev curr tol

def runKANNCA
    (rule : KANCellUpdateRule)
    (seed : FSum)
    (goalFeatures : Array Rat := #[]) : KANNCAOutcome :=
  let init := initNCAState rule.ncaRule seed goalFeatures
  let rec go : Nat → Nat → NCAState → NCAState → Bool × Nat × NCAState
    | 0, used, _prev, curr => (true, used, curr)
    | Nat.succ fuel, used, _prev, curr =>
        let curr' :=
          match rule.perturb with
          | some p =>
              if used = p.step then perturbState curr p else curr
          | none => curr
        let next := kanNCAStep rule curr'
        if isStableKANNCA curr' next rule.tolerance then
          (true, used + 1, next)
        else
          go fuel (used + 1) curr next
  let (ok, steps, final) := go (max 1 rule.maxSteps) 0 init init
  let score := if ok then 1 else (1 : Rat) / (Int.ofNat (steps + 1) : Rat)
  {
    finalState := final
    converged := ok
    stepsUsed := steps
    stabilityScore := score
    candidates := extractTactics final 4
    symbolicSummaries := kanSymbolicSummaries rule.selector 8
  }

end DifferentiableATP
end ATP
end HeytingLean
