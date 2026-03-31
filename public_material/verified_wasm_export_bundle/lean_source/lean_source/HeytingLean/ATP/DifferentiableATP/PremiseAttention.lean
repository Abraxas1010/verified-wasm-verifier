import HeytingLean.ATP.DifferentiableATP.CoreOps
import HeytingLean.ATP.DifferentiableATP.CombToExpr
import HeytingLean.ATP.DifferentiableATP.Util

/-!
# ATP.DifferentiableATP.PremiseAttention

Attention-style keyword extraction from differentiable ATP weight vectors.
-/

namespace HeytingLean
namespace ATP
namespace DifferentiableATP

open HeytingLean.LoF
open HeytingLean.LoF.Combinators.Differential.Compute

private def manualCombKeywords : Comb → List String
  | .K => ["const", "True", "intro", "exact", "constructor"]
  | .S => ["apply", "simp", "rewrite", "congr", "function"]
  | .Y => ["induction", "rec", "fix", "termination", "nat"]
  | .app .S .K => ["identity", "rfl", "Eq.refl", "simp"]
  | .app .K .S => ["swap", "comm", "symm", "flip"]
  | .app .Y .K => ["iterate", "repeat", "decide", "omega"]
  | .app .S .Y => ["False", "absurd", "contradiction", "False.elim"]
  | .app _ _ => []

private def tacticDerivedKeywords (c : Comb) : List String :=
  let tactic := combToTactic c
  let words := (tactic.splitOn " ").filter (fun w => !w.isEmpty)
  let lead :=
    match words with
    | [] => []
    | hd :: _ => [hd]
  let combTag :=
    match c with
    | .K => ["K"]
    | .S => ["S"]
    | .Y => ["Y"]
    | .app _ _ => ["app"]
  (combTag ++ lead ++ words).eraseDups

/--
Keyword extraction combines a small hand-tuned seed map with
auto-derived tokens from the current `combToTactic` mapping.
This keeps attention queries synchronized as tactic decoding evolves.
-/
def combKeywords : Comb → List String
  | .app f a =>
      (manualCombKeywords (.app f a) ++ tacticDerivedKeywords (.app f a) ++ combKeywords f ++ combKeywords a).eraseDups
  | c =>
      (manualCombKeywords c ++ tacticDerivedKeywords c).eraseDups

private def bumpKeyword (acc : List (String × Rat)) (kw : String) (delta : Rat) : List (String × Rat) :=
  match acc with
  | [] => [(kw, delta)]
  | (k, s) :: tl =>
      if k = kw then
        (k, s + delta) :: tl
      else
        (k, s) :: bumpKeyword tl kw delta

private def insertByScore (entry : String × Rat) : List (String × Rat) → List (String × Rat)
  | [] => [entry]
  | hd :: tl =>
      if entry.2 >= hd.2 then
        entry :: hd :: tl
      else
        hd :: insertByScore entry tl

private def sortByScoreDesc (xs : List (String × Rat)) : List (String × Rat) :=
  xs.foldl (fun acc e => insertByScore e acc) []

def attentionQuery (w : FSum) : List (String × Rat) :=
  let raw :=
    w.foldl
      (fun acc tc =>
        let score := absRat tc.2
        (combKeywords tc.1).foldl (fun acc' kw => bumpKeyword acc' kw score) acc)
      []
  sortByScoreDesc raw

def topKeywords (w : FSum) (k : Nat := 5) : List String :=
  (attentionQuery w).take (max 1 k) |>.map (fun p => p.1)

end DifferentiableATP
end ATP
end HeytingLean
