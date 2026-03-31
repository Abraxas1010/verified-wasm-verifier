import HeytingLean.LoF.Combinators.Birthday.Metric
import HeytingLean.LoF.Combinators.Birthday.ScopedIntegration
import HeytingLean.LoF.Combinators.SKYExec
import HeytingLean.LoF.Combinators.SKYUniversality

/-!
# SKY Birthday Decision Gate — data generation for Sub-project 3

Computes combBirthday and reduction-step count for a variety of SKY terms,
outputting CSV for the decision gate analysis.
-/

namespace HeytingLean.Tests.Numbers

open HeytingLean.LoF
open HeytingLean.LoF.Combinators
open HeytingLean.LoF.Combinators.Birthday
open HeytingLean.LoF.Combinators.SKYExec
open HeytingLean.LoF.Combinators.SKYUniversality

/-- Count reduction steps (up to fuel limit). -/
def countSteps (fuel : Nat) (t : Comb) : Nat :=
  go fuel t 0
where
  go : Nat → Comb → Nat → Nat
    | 0, _, acc => acc
    | Nat.succ n, t, acc =>
        match step? t with
        | some t' => go n t' (acc + 1)
        | none => acc

/-- Convert a Comb to a string representation. -/
def combToString : Comb → String
  | .K => "K"
  | .S => "S"
  | .Y => "Y"
  | .app f a => s!"({combToString f} {combToString a})"

def allSeeds : List (String × Comb) :=
  [ ("K", Comb.K)
  , ("S", Comb.S)
  , ("Y", Comb.Y)
  , ("I", Comb.I)
  , ("KK", Comb.app Comb.K Comb.K)
  , ("SK", Comb.app Comb.S Comb.K)
  , ("KS", Comb.app Comb.K Comb.S)
  , ("SS", Comb.app Comb.S Comb.S)
  ]

def maxDepth : Nat := 7

def main : IO Unit := do
  IO.println "seed,depth,combBirthday,reduce_steps"
  for (seedName, seed) in allSeeds do
    for depth in List.range (maxDepth + 1) do
      let program := repeatedUnfold seed depth
      let term := encode program
      let bday := combBirthday term
      let steps := countSteps 200 term
      IO.println s!"{seedName},{depth},{bday},{steps}"

end HeytingLean.Tests.Numbers
