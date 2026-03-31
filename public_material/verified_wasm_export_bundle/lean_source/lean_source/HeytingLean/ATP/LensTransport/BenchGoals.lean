import HeytingLean.ATP.LensTransport.FaithfulTransportGraph

/-!
# ATP.LensTransport.BenchGoals

Lens-discriminating benchmark goals used by `lens_transport_bench` experiments.
These are goal-string fixtures (not Lean theorem statements) so they can be fed
directly to CLI search binaries.
-/

namespace HeytingLean
namespace ATP
namespace LensTransport
namespace BenchGoals

open HeytingLean.Embeddings

structure BenchGoal where
  id : String
  goal : String
  favoredLens : LensID
  deriving Repr

/-- Tensor-oriented algebraic goals. -/
def tensorGoals : List BenchGoal :=
  [ { id := "TG1"
      goal := "⊢ ∀ n m : Nat, (n + m) * (n + m) = n * n + 2 * n * m + m * m"
      favoredLens := .tensor }
  , { id := "TG2"
      goal := "⊢ ∀ a b c : Nat, (a + b) * c = a * c + b * c"
      favoredLens := .tensor }
  , { id := "TG3"
      goal := "⊢ ∀ n : Nat, n + n = 2 * n"
      favoredLens := .tensor }
  ]

/-- Graph/list-structure oriented goals. -/
def graphGoals : List BenchGoal :=
  [ { id := "GG1"
      goal := "⊢ ∀ (l : List Nat), l = [] ∨ ∃ h : Nat, ∃ t : List Nat, l = h :: t"
      favoredLens := .graph }
  , { id := "GG2"
      goal := "⊢ ∀ (l : List Nat), l ≠ [] → ∃ h : Nat, ∃ t : List Nat, l = h :: t"
      favoredLens := .graph }
  , { id := "GG3"
      goal := "⊢ ∀ (l : List Nat), List.foldl (fun acc _ => acc + 2) 0 l = 2 * l.length"
      favoredLens := .graph }
  ]

/-- Topology/set-flavored goals. -/
def topologyGoals : List BenchGoal :=
  [ { id := "TOP1"
      goal := "⊢ ∀ U V : Set Nat, U ∩ V ⊆ U"
      favoredLens := .topology }
  , { id := "TOP2"
      goal := "⊢ ∀ U V : Set Nat, U ⊆ U ∪ V"
      favoredLens := .topology }
  ]

def allGoals : List BenchGoal :=
  tensorGoals ++ graphGoals ++ topologyGoals

end BenchGoals
end LensTransport
end ATP
end HeytingLean
