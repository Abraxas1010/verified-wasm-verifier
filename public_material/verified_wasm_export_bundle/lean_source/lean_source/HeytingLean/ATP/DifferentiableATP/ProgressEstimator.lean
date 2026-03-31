import HeytingLean.ATP.DifferentiableATP.TacticDecoder

/-!
# ATP.DifferentiableATP.ProgressEstimator

Cross-cutting D3 utilities:
- progress scoring for differentiable ATP trajectories,
- tactic diversification with lightweight usage tracking.
-/

namespace HeytingLean
namespace ATP
namespace DifferentiableATP

open HeytingLean.LoF
open HeytingLean.LoF.Combinators.Differential
open HeytingLean.LoF.Combinators.Differential.Compute

private def clamp01 (r : Rat) : Rat :=
  if r < 0 then 0 else if r > 1 then 1 else r

private def safeDenom (r : Rat) : Rat :=
  if r = 0 then 1 else r

structure TacticUsageTracker where
  counts : List (String × Nat) := []
  deriving Repr

private def usageOf (tracker : TacticUsageTracker) (tactic : String) : Nat :=
  match tracker.counts.find? (fun row => row.1 = tactic) with
  | some row => row.2
  | none => 0

def TacticUsageTracker.bump (tracker : TacticUsageTracker) (tactic : String) : TacticUsageTracker :=
  let rec go : List (String × Nat) → List (String × Nat)
    | [] => [(tactic, 1)]
    | (name, n) :: tl =>
        if name = tactic then
          (name, n + 1) :: tl
        else
          (name, n) :: go tl
  { tracker with counts := go tracker.counts }

private def dedupByTactic (rows : List DecodedCandidate) : List DecodedCandidate :=
  rows.foldl
    (fun acc row =>
      if acc.any (fun x => x.tactic = row.tactic) then acc else acc ++ [row])
    []

private def insertByUsage
    (tracker : TacticUsageTracker)
    (row : DecodedCandidate)
    : List DecodedCandidate → List DecodedCandidate
  | [] => [row]
  | hd :: tl =>
      let uRow := usageOf tracker row.tactic
      let uHd := usageOf tracker hd.tactic
      if uRow < uHd then
        row :: hd :: tl
      else if uRow = uHd && row.confidence > hd.confidence then
        row :: hd :: tl
      else
        hd :: insertByUsage tracker row tl

private def sortByUsage (tracker : TacticUsageTracker) (rows : List DecodedCandidate) : List DecodedCandidate :=
  rows.foldl (fun acc row => insertByUsage tracker row acc) []

private def injectCandidates (tracker : TacticUsageTracker) (existing : List DecodedCandidate) : List DecodedCandidate :=
  let present := existing.map (fun r => r.tactic)
  let injectRaw :=
    tacticTable.filterMap (fun row =>
      if present.any (fun t => t = row.tactic) then
        none
      else
        some
          {
            comb := row.pattern
            tactic := row.tactic
            source := s!"diversify::{row.family}"
            confidence := (1 : Rat) / 10
          })
  sortByUsage tracker injectRaw

/--
Diversify a ranked candidate list while preserving top-1.
- top-1 is never removed,
- remaining slots are tactic-unique,
- if needed, inject least-used tactics from the static table.
-/
def diversifyTactics
    (rows : List DecodedCandidate)
    (tracker : TacticUsageTracker := {})
    (topK : Nat := 4) : List DecodedCandidate :=
  let k := max 1 topK
  match rows with
  | [] =>
      (injectCandidates tracker []).take k
  | top1 :: tail =>
      let tailUnique := (dedupByTactic tail).filter (fun r => r.tactic ≠ top1.tactic)
      let base := (top1 :: tailUnique).take k
      if base.length >= k then
        base
      else
        let injected := injectCandidates tracker base
        (base ++ injected).take k

def tacticDiversityIndex (rows : List DecodedCandidate) : Rat :=
  if rows.isEmpty then
    0
  else
    let uniq := (rows.map (fun r => r.tactic)).eraseDups.length
    (Int.ofNat uniq : Rat) / (Int.ofNat rows.length : Rat)

/--
Progress score in [0,1]:
- movement proxy from initial to current weights,
- iteration-completion proxy.
-/
def estimateProgress
    (initial current : FSum)
    (iteration : Nat)
    (lossHistory : List Rat := [])
    (currentLoss : Rat := 0)
    (maxIterations : Nat := 24) : Rat :=
  let initMass := l2NormSq initial
  let moveMass := l2NormSq (sub current initial)
  let massScore :=
    if initMass = 0 then
      clamp01 (moveMass / safeDenom (1 + moveMass))
    else
      clamp01 (moveMass / safeDenom (initMass + moveMass))
  let iterScore :=
    clamp01 ((Int.ofNat iteration : Rat) / (Int.ofNat (max 1 maxIterations) : Rat))
  let startLoss := lossHistory.headD currentLoss
  let lossScore :=
    if startLoss = 0 then
      0
    else
      clamp01 (1 - currentLoss / safeDenom startLoss)
  let raw := clamp01 ((massScore + iterScore + lossScore) / 3)
  if raw = 0 then
    clamp01 ((clamp01 (initMass / safeDenom (1 + initMass))) / 10)
  else
    raw

end DifferentiableATP
end ATP
end HeytingLean
