import HeytingLean.ATP.DifferentiableATP.CombToExpr
import HeytingLean.ATP.DifferentiableATP.PremiseAttention
import HeytingLean.ATP.DifferentiableATP.Util

/-!
# ATP.DifferentiableATP.TacticDecoder

Decodes weighted combinator outputs into ranked tactic candidates.
-/

namespace HeytingLean
namespace ATP
namespace DifferentiableATP

open HeytingLean.LoF
open HeytingLean.LoF.Combinators.Differential
open HeytingLean.LoF.Combinators.Differential.Compute

structure DecodedCandidate where
  comb : Comb
  tactic : String
  source : String
  confidence : Rat
  deriving Repr

structure LearnedTacticEntry where
  tactic : String
  family : String
  embedding : FSum
  deriving Repr

private def fromPair (tc : Comb × Rat) : DecodedCandidate :=
  {
    comb := tc.1
    tactic := combToTactic tc.1
    source := combName tc.1
    confidence := absRat tc.2
  }

/-- Default learnable tactic embeddings seeded from the static pattern table. -/
def defaultLearnedTacticEntries : List LearnedTacticEntry :=
  tacticTable.map (fun row =>
    {
      tactic := row.tactic
      family := row.family
      embedding := single row.pattern 1
    })

private def normalizeHint (hint : String) : String :=
  hint.trim

private def hintAllowedChar (c : Char) : Bool :=
  c.isAlphanum || c = '.' || c = '_' || c = '\''

private def validPremiseHint (hint : String) : Bool :=
  let h := normalizeHint hint
  !h.isEmpty && h.data.all hintAllowedChar

private def candidateFromPremise (premise : String) (score : Rat := 1) : DecodedCandidate :=
  {
    comb := .K
    tactic := s!"exact {premise}"
    source := s!"premise::{premise}"
    confidence := absRat score
  }

private def dedupByTactic (rows : List DecodedCandidate) : List DecodedCandidate :=
  rows.foldl
    (fun acc row =>
      if acc.any (fun x => x.tactic = row.tactic) then acc else acc ++ [row])
    []

private def insertRanked
    (item : LearnedTacticEntry × Rat)
    : List (LearnedTacticEntry × Rat) → List (LearnedTacticEntry × Rat)
  | [] => [item]
  | hd :: tl =>
      if item.2 > hd.2 then
        item :: hd :: tl
      else
        hd :: insertRanked item tl

private def rankLearned
    (state : FSum)
    (depth : Nat)
    (entries : List LearnedTacticEntry) : List (LearnedTacticEntry × Rat) :=
  (entries.map (fun e => (e, softDot depth state e.embedding))).foldl
    (fun acc row => insertRanked row acc)
    []

/-- Score one learned tactic entry against the current state. -/
def scoreTactic (state : FSum) (entry : LearnedTacticEntry) (depth : Nat := 3) : Rat :=
  softDot depth state entry.embedding

/-- Rank learned tactic entries by score descending. -/
def rankTactics
    (state : FSum)
    (entries : List LearnedTacticEntry := defaultLearnedTacticEntries)
    (depth : Nat := 3) : List (LearnedTacticEntry × Rat) :=
  rankLearned state depth entries

/-- Coordinate gradient of one tactic score wrt state parameters. -/
def scoreGrad
    (params : List Comb)
    (entry : LearnedTacticEntry)
    (depth : Nat := 3) : FSum :=
  params.foldl
    (fun g t =>
      let gc := softDot depth (single t 1) entry.embedding
      add g (single t gc))
    []

/-- Auxiliary loss: maximize top-k tactic scores by minimizing negative mean score. -/
def tacticScoreLoss
    (state : FSum)
    (entries : List LearnedTacticEntry := defaultLearnedTacticEntries)
    (topK : Nat := 4)
    (depth : Nat := 3) : Rat :=
  let ranked := (rankTactics state entries depth).take (max 1 topK)
  if ranked.isEmpty then
    0
  else
    let total := ranked.foldl (fun acc row => acc - row.2) 0
    total / (Int.ofNat ranked.length : Rat)

/-- Coordinate gradient of `tacticScoreLoss` wrt state parameters. -/
def tacticScoreLossGrad
    (params : List Comb)
    (state : FSum)
    (entries : List LearnedTacticEntry := defaultLearnedTacticEntries)
    (topK : Nat := 4)
    (depth : Nat := 3) : FSum :=
  let ranked := (rankTactics state entries depth).take (max 1 topK)
  if ranked.isEmpty then
    []
  else
    let summed :=
      ranked.foldl
        (fun g row => add g (smul (-1) (scoreGrad params row.1 depth)))
        []
    smul ((1 : Rat) / (Int.ofNat ranked.length : Rat)) summed

def decodeComb (c : Comb) : DecodedCandidate :=
  {
    comb := c
    tactic := combToTactic c
    source := combName c
    confidence := 1
  }

def decodeFromWeights (w : FSum) (k : Nat := 4) : List DecodedCandidate :=
  let ranked := topTermsByAbs w k
  let decoded := ranked.map fromPair
  if decoded.isEmpty then
    [decodeComb .K, decodeComb .S]
  else
    decoded

def decodeFromWeightsWithTemperature (temperature : Rat) (w : FSum) (k : Nat := 4) : List DecodedCandidate :=
  if temperature <= 0 then
    decodeFromWeights w k
  else
    let inv := (1 : Rat) / temperature
    decodeFromWeights (w.map (fun tc => (tc.1, tc.2 * inv))) k

/-- Decode using learned tactic embeddings scored by `softDot`. -/
def decodeFromLearnedWeights
    (w : FSum)
    (k : Nat := 4)
    (depth : Nat := 3)
    (entries : List LearnedTacticEntry := defaultLearnedTacticEntries) : List DecodedCandidate :=
  let ranked := (rankLearned w depth entries).take (max 1 k)
  let decoded :=
    ranked.map (fun row =>
      {
        comb := collapseBestTerm? row.1.embedding |>.getD .K
        tactic := row.1.tactic
        source := s!"learned::{row.1.family}"
        confidence := absRat row.2
      })
  let merged := dedupByTactic decoded
  if merged.isEmpty then
    decodeFromWeights w k
  else
    merged

def decodeFromLearnedWeightsWithPremises
    (w : FSum)
    (premises : List String)
    (k : Nat := 4)
    (premiseBudget : Nat := 4)
    (depth : Nat := 3)
    (entries : List LearnedTacticEntry := defaultLearnedTacticEntries) : List DecodedCandidate :=
  let base := decodeFromLearnedWeights w k depth entries
  let normalizedPremises := premises.map normalizeHint
  let filteredPremises := normalizedPremises.filter validPremiseHint
  let uniquePremises := filteredPremises.eraseDups
  let limitedPremises := uniquePremises.take (max 1 premiseBudget)
  let premiseCandidates := limitedPremises.map (fun p => candidateFromPremise p)
  let merged := dedupByTactic (base ++ premiseCandidates)
  if merged.isEmpty then
    decodeFromLearnedWeights w k depth entries
  else
    merged

def decodeFromWeightsWithPremises
    (w : FSum)
    (premises : List String)
    (k : Nat := 4)
    (premiseBudget : Nat := 4) : List DecodedCandidate :=
  let base := decodeFromWeights w k
  let normalizedPremises := premises.map normalizeHint
  let filteredPremises := normalizedPremises.filter validPremiseHint
  let uniquePremises := filteredPremises.eraseDups
  let limitedPremises := uniquePremises.take (max 1 premiseBudget)
  let premiseCandidates := limitedPremises.map (fun p => candidateFromPremise p)
  let merged := dedupByTactic (base ++ premiseCandidates)
  if merged.isEmpty then
    [decodeComb .K, decodeComb .S]
  else
    merged

def decodeFromWeightsWithPremisesAndTemperature
    (temperature : Rat)
    (w : FSum)
    (premises : List String)
    (k : Nat := 4)
    (premiseBudget : Nat := 4) : List DecodedCandidate :=
  if temperature <= 0 then
    decodeFromWeightsWithPremises w premises k premiseBudget
  else
    let inv := (1 : Rat) / temperature
    decodeFromWeightsWithPremises (w.map (fun tc => (tc.1, tc.2 * inv))) premises k premiseBudget

end DifferentiableATP
end ATP
end HeytingLean
