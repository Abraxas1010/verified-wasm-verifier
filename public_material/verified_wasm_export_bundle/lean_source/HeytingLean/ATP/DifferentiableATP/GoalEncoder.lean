import HeytingLean.Embeddings.Adelic
import HeytingLean.LoF.Combinators.Differential.GradientDescent

/-!
# ATP.DifferentiableATP.GoalEncoder

A pragmatic goal encoder for the differentiable ATP lane.

This module intentionally stays executable-first:
- converts textual goals into `Compute.FSum` seeds,
- emits a finite combinator basis,
- emits runtime IO examples consumed by `Compute.gradientDescentLoop`.

It is additive scaffolding and does not mutate existing differential foundations.

Current mode is heuristic string-pattern encoding (`goal : String`) rather than
full structural `Expr`/`MVarId` introspection.
-/

namespace HeytingLean
namespace ATP
namespace DifferentiableATP

open HeytingLean.Embeddings
open HeytingLean.LoF
open HeytingLean.LoF.Combinators.Differential
open HeytingLean.LoF.Combinators.Differential.Compute

structure EncodedGoal where
  goal : String
  normalizedGoal : String
  lens : LensID
  initial : FSum
  examples : List IOExample
  basis : List Comb
  contextHints : List String

private def normalizeGoal (goal : String) : String :=
  goal.trim

private def hasSubstr (text needle : String) : Bool :=
  if needle.isEmpty then
    false
  else
    (text.splitOn needle).length > 1

private def hasAnySubstr (text : String) (needles : List String) : Bool :=
  needles.any (fun needle => hasSubstr text needle)

private def countToken (text token : String) : Nat :=
  if token.isEmpty then
    0
  else
    Nat.pred (text.splitOn token).length

private def sanitizeGoalForTokens (goal : String) : String :=
  let punct := ["(", ")", "[", "]", "{", "}", ",", ";", ":", "=", "→", "->", "↔", "∧", "∨", "¬"]
  punct.foldl (fun acc p => acc.replace p " ") goal

private def tokenizeGoal (goal : String) : List String :=
  (sanitizeGoalForTokens goal).splitOn " " |>.map String.trim |>.filter (fun t => !t.isEmpty)

/-- Structural hash used to diversify otherwise similar textual goals. -/
def structuralGoalHash (goal : String) : UInt64 :=
  let n := normalizeGoal goal
  hash n

structure GoalFeatures where
  hasForall : Bool := false
  hasExists : Bool := false
  hasArrow : Bool := false
  hasIff : Bool := false
  hasAnd : Bool := false
  hasOr : Bool := false
  hasNot : Bool := false
  hasEq : Bool := false
  hasNat : Bool := false
  hasInt : Bool := false
  hasReal : Bool := false
  hasList : Bool := false
  hasFinset : Bool := false
  hasSet : Bool := false
  hasPlus : Bool := false
  hasMul : Bool := false
  hasLt : Bool := false
  hasLe : Bool := false
  hasPow : Bool := false
  hasTrue : Bool := false
  hasFalse : Bool := false
  hasComposition : Bool := false
  hasInduction : Bool := false
  arrowDepth : Nat := 0
  quantifierDepth : Nat := 0
  tokenCount : Nat := 0
  uniqueTokenCount : Nat := 0
  hashBucket : Nat := 0
  deriving Repr

private def lensSeed : LensID → Comb
  | .omega => .Y
  | .region => .K
  | .graph => .S
  | .clifford => .app .S .K
  | .tensor => .app .K .S
  | .topology => .app .Y .K
  | .matula => .app (.app .S .K) .S

private def baseBasis : List Comb :=
  [.K, .S, .Y, .app .S .K, .app .K .S, .app .S .S, .app .S .Y, .app .Y .K, .app .K .K, .app (.app .S .K) .K]

private def extractFeatures (goal : String) : GoalFeatures :=
  let g := normalizeGoal goal
  let tokens := tokenizeGoal g
  let uniqueTokens := tokens.eraseDups
  let sigHash := structuralGoalHash g
  let hashBucket := sigHash.toNat % 37
  let arrowDepth := countToken g "→" + countToken g "->"
  let quantifierDepth := countToken g "∀" + countToken g "∃"
  {
    hasForall := hasSubstr g "∀"
    hasExists := hasSubstr g "∃"
    hasArrow := hasAnySubstr g ["→", "->"]
    hasIff := hasSubstr g "↔"
    hasAnd := hasAnySubstr g ["∧", "And"]
    hasOr := hasAnySubstr g ["∨", "Or"]
    hasNot := hasAnySubstr g ["¬", "Not"]
    hasEq := hasSubstr g "="
    hasNat := hasSubstr g "Nat" || hasSubstr g "ℕ"
    hasInt := hasSubstr g "Int" || hasSubstr g "ℤ"
    hasReal := hasSubstr g "Real" || hasSubstr g "ℝ"
    hasList := hasSubstr g "List"
    hasFinset := hasSubstr g "Finset"
    hasSet := hasSubstr g "Set"
    hasPlus := hasSubstr g "+"
    hasMul := hasSubstr g "*"
    hasLt := hasAnySubstr g ["<", ">"]
    hasLe := hasAnySubstr g ["≤", "≥"]
    hasPow := hasSubstr g "^"
    hasTrue := hasSubstr g "True"
    hasFalse := hasSubstr g "False"
    hasComposition := hasAnySubstr g ["∘", "Function.", "Equiv."]
    hasInduction := hasAnySubstr g ["Nat.rec", "List.rec", "induction", "cases"]
    arrowDepth := arrowDepth
    quantifierDepth := quantifierDepth
    tokenCount := tokens.length
    uniqueTokenCount := uniqueTokens.length
    hashBucket := hashBucket
  }

private def addWeightIf (cond : Bool) (w : FSum) (c : Comb) (weight : Rat) : FSum :=
  if cond then add w (single c weight) else w

private def hasArithmeticSignal (f : GoalFeatures) : Bool :=
  f.hasNat || f.hasInt || f.hasReal || f.hasPlus || f.hasMul || f.hasLt || f.hasLe

private def hasLogicSignal (f : GoalFeatures) : Bool :=
  f.hasAnd || f.hasOr || f.hasIff || f.hasNot

private def hashSeedTerm (bucket : Nat) : Comb :=
  let pool : List Comb :=
    [.K, .S, .Y, .app .S .K, .app .K .S, .app .S .S, .app .S .Y, .app .Y .K, .app .K .K, .app (.app .S .K) .K]
  pool.getD (bucket % pool.length) .K

private def hashSeedWeight (bucket offset : Nat) : Rat :=
  let n := ((bucket + offset) % 7) + 1
  (n : Rat) / 4

private def initialFromFeatures (f : GoalFeatures) (lens : LensID) : FSum :=
  let seed := lensSeed lens
  let base := add (single .S 1) (single seed 1)
  let w1 := addWeightIf f.hasTrue base .K 2
  let w2 := addWeightIf f.hasFalse w1 .Y 2
  let w3 := addWeightIf (hasArithmeticSignal f) w2 (.app .S .S) 2
  let w4 := addWeightIf (hasArithmeticSignal f) w3 (.app .S .Y) 1
  let w5 := addWeightIf (hasLogicSignal f) w4 (.app .Y .S) 2
  let w6 := addWeightIf (f.hasEq && !f.hasForall) w5 (.app .K .S) 2
  let w7 := addWeightIf (f.hasForall && f.hasArrow) w6 (.app (.app .S .K) .K) 2
  let w8 := addWeightIf f.hasExists w7 (.app (.app .S .K) .S) 1
  let w9 := addWeightIf (f.hasInduction || (f.hasNat && f.hasForall)) w8 (.app (.app .Y .K) .K) 1
  let w10 := addWeightIf f.hasComposition w9 (.app .K .K) 1
  let w11 := addWeightIf (f.tokenCount > 6) w10 (.app .Y .Y) ((f.tokenCount : Rat) / 10)
  let w12 := addWeightIf (f.uniqueTokenCount > 4) w11 (.app .K .K) ((f.uniqueTokenCount : Rat) / 12)
  let h0 := hashSeedTerm f.hashBucket
  let h1 := hashSeedTerm (f.hashBucket + 11)
  let h2 := hashSeedTerm (f.hashBucket + 23)
  normalize <|
    add
      (add (add w12 (single h0 (hashSeedWeight f.hashBucket 0))) (single h1 (hashSeedWeight f.hashBucket 1)))
      (single h2 (hashSeedWeight f.hashBucket 2))

private def basisFromFeatures (f : GoalFeatures) (contextHints : List String) : List Comb :=
  let eqBasis := if f.hasEq then [.app .K .S, .app .S .K] else []
  let arithmeticBasis := if hasArithmeticSignal f then [.app .S .S, .app .S .Y, .app .Y .K] else []
  let logicBasis := if hasLogicSignal f then [.app .Y .S, .app (.app .S .K) .S, .app .Y .Y] else []
  let quantBasis := if f.hasForall || f.hasArrow then [.app (.app .S .K) .K] else []
  let existsBasis := if f.hasExists then [.app (.app .S .K) .S] else []
  let inductionBasis := if f.hasInduction || (f.hasNat && f.hasForall) then [.app (.app .Y .K) .K] else []
  let compBasis := if f.hasComposition then [.app .K .K] else []
  let hashBasis :=
    [hashSeedTerm f.hashBucket, hashSeedTerm (f.hashBucket + 11), hashSeedTerm (f.hashBucket + 23)]
  let hintBasis := if contextHints.any (fun h => hasSubstr h "simp") then [.S] else []
  let dedup := (baseBasis ++ eqBasis ++ arithmeticBasis ++ logicBasis ++ quantBasis ++ existsBasis ++ inductionBasis ++ compBasis ++ hashBasis ++ hintBasis).eraseDups
  let capped := dedup.take 12
  if capped.isEmpty then baseBasis.take 12 else capped

private def expectedFromFeatures (f : GoalFeatures) (seed : Comb) : FSum :=
  let base := add (single (.app .S seed) 1) (single (.app .K seed) 1)
  let w1 := addWeightIf f.hasTrue base (.app .K seed) 2
  let w2 := addWeightIf f.hasFalse w1 (.app .Y seed) 2
  let w3 := addWeightIf (hasArithmeticSignal f) w2 (.app .S .S) 2
  let w4 := addWeightIf (hasArithmeticSignal f) w3 (.app .S .Y) 1
  let w5 := addWeightIf (hasLogicSignal f) w4 (.app .Y .S) 2
  let w6 := addWeightIf (f.hasEq && !f.hasForall) w5 (.app .K .S) 2
  let w7 := addWeightIf (f.hasForall && f.hasArrow) w6 (.app (.app .S .K) .K) 2
  addWeightIf f.hasExists w7 (.app (.app .S .K) .S) 1

private def examplesFromFeatures (f : GoalFeatures) (seed : Comb) : List IOExample :=
  let x : FSum := single seed 1
  let y : FSum := expectedFromFeatures f seed
  [{ input := x, expected := y }]

def encodeGoal
    (goal : String)
    (lens : LensID := .omega)
    (contextHints : List String := [])
    (oracleExamples : Option (List IOExample) := none) : EncodedGoal :=
  let normalized := normalizeGoal goal
  let features := extractFeatures normalized
  let seed := lensSeed lens
  {
    goal := goal
    normalizedGoal := normalized
    lens := lens
    initial := initialFromFeatures features lens
    examples := oracleExamples.getD (examplesFromFeatures features seed)
    basis := basisFromFeatures features contextHints
    contextHints := contextHints
  }

def goalFeatures (goal : String) : GoalFeatures :=
  extractFeatures goal

def supportsGoal (goal : String) : Bool :=
  -- Heuristic encoder currently requires only non-empty textual goal input.
  let g := normalizeGoal goal
  not g.isEmpty

end DifferentiableATP
end ATP
end HeytingLean
