import HeytingLean.LoF.Combinators.Differential.GradientDescent
import HeytingLean.ATP.DifferentiableATP.Util

/-!
# ATP.DifferentiableATP.CombToExpr

Executable decoding helpers from combinator weights to tactic text.
-/

namespace HeytingLean
namespace ATP
namespace DifferentiableATP

open HeytingLean.LoF
open HeytingLean.LoF.Combinators.Differential
open HeytingLean.LoF.Combinators.Differential.Compute

def combName : Comb → String
  | .K => "K"
  | .S => "S"
  | .Y => "Y"
  | .app f a => s!"({combName f} {combName a})"

structure TacticEntry where
  pattern : Comb
  tactic : String
  family : String
  deriving Repr

/-- Static seed table used for backward compatibility and learned embedding initialization. -/
def tacticTable : List TacticEntry :=
  [
    { pattern := .K, tactic := "exact True.intro", family := "closing" },
    { pattern := .S, tactic := "simp", family := "simplification" },
    { pattern := .Y, tactic := "aesop", family := "automation" },
    { pattern := .app .K .K, tactic := "trivial", family := "closing" },
    { pattern := .app .K .S, tactic := "rfl", family := "equality" },
    { pattern := .app .K .Y, tactic := "decide", family := "decision" },
    { pattern := .app .S .K, tactic := "ring", family := "arithmetic" },
    { pattern := .app .S .S, tactic := "omega", family := "arithmetic" },
    { pattern := .app .S .Y, tactic := "norm_num", family := "arithmetic" },
    { pattern := .app .Y .K, tactic := "linarith", family := "arithmetic" },
    { pattern := .app .Y .S, tactic := "tauto", family := "logic" },
    { pattern := .app .Y .Y, tactic := "contradiction", family := "logic" },
    { pattern := .app (.app .S .K) .K, tactic := "intro; simp", family := "structural" },
    { pattern := .app (.app .S .K) .S, tactic := "constructor <;> simp", family := "structural" },
    { pattern := .app (.app .S .K) .Y, tactic := "simp_all", family := "structural" },
    { pattern := .app (.app .K .S) .K, tactic := "apply And.intro", family := "structural" },
    { pattern := .app (.app .K .S) .S, tactic := "simp only [*]", family := "simplification" },
    { pattern := .app (.app .Y .K) .K, tactic := "constructor", family := "structural" },
    { pattern := .app (.app .Y .K) .S, tactic := "intro", family := "structural" },
    { pattern := .app (.app .Y .S) .K, tactic := "intros", family := "structural" },
    { pattern := .app (.app .Y .S) .S, tactic := "intros; omega", family := "compound" },
    { pattern := .app (.app .Y .S) .Y, tactic := "intros; ring", family := "compound" },
    { pattern := .app (.app .Y .Y) .K, tactic := "intros; tauto", family := "compound" },
    { pattern := .app (.app .Y .Y) .S, tactic := "intros; linarith", family := "compound" },
    { pattern := .app (.app .Y .Y) .Y, tactic := "intros; nlinarith", family := "compound" },
    { pattern := .app (.app .K .K) .K, tactic := "nlinarith", family := "arithmetic" },
    { pattern := .app (.app .K .K) .S, tactic := "cases", family := "structural" },
    { pattern := .app (.app .K .K) .Y, tactic := "induction", family := "structural" },
    { pattern := .app (.app .S .S) .K, tactic := "intro n; cases n with | zero => simp | succ k => simp_all", family := "nat_structural" },
    { pattern := .app (.app .S .S) .S, tactic := "intro n; cases n with | zero => left; simp | succ k => right; simp", family := "nat_structural" },
    { pattern := .app (.app .S .S) .Y, tactic := "intro n; cases n with | zero => left; simp | succ k => right; refine ⟨k, ?_⟩; omega", family := "nat_structural" },
    { pattern := .app (.app (.app .S .K) .K) .K, tactic := "intro l; induction l with | nil => simp | cons h t ih => simp_all", family := "list_structural" },
    { pattern := .app (.app (.app .S .K) .K) .S, tactic := "intro l; induction l with | nil => simp | cons h t ih => simp_all; omega", family := "list_structural" }
  ]

private def matchPattern? (c : Comb) : Option String :=
  (tacticTable.find? (fun e => e.pattern = c)).map (fun e => e.tactic)

def combToTactic (c : Comb) : String :=
  match matchPattern? c with
  | some tactic => tactic
  | none =>
      match c with
      | .app f _ => combToTactic f
      | _ => "simp"

private def insertByAbs (tc : Comb × Rat) : List (Comb × Rat) → List (Comb × Rat)
  | [] => [tc]
  | hd :: tl =>
      if absRat tc.2 >= absRat hd.2 then
        tc :: hd :: tl
      else
        hd :: insertByAbs tc tl

private def sortByAbsDesc (w : FSum) : List (Comb × Rat) :=
  w.foldl (fun acc tc => insertByAbs tc acc) []

def topTermsByAbs (w : FSum) (k : Nat := 4) : List (Comb × Rat) :=
  (sortByAbsDesc w).take (max 1 k)

def collapseBestTerm? (w : FSum) : Option Comb :=
  Compute.bestTermByAbs? w

def collapseBestWithTemperature? (temperature : Rat) (w : FSum) : Option Comb :=
  if temperature <= 0 then
    collapseBestTerm? w
  else
    let inv := (1 : Rat) / temperature
    collapseBestTerm? (w.map (fun tc => (tc.1, tc.2 * inv)))

end DifferentiableATP
end ATP
end HeytingLean
