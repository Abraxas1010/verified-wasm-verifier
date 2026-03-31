import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic
import HeytingLean.CodingTheory.InsDel.Subsequence
import HeytingLean.CodingTheory.InsDel.Distance

namespace HeytingLean
namespace CodingTheory
namespace InsDel

/-!
# Insertion/deletion code predicates
-/

variable {α : Type}

def delCode (C : Set (List α)) (t : Nat) : Prop :=
  ∀ X Y Z : List α,
    X ∈ C → Y ∈ C → Z ⊴ X → Z ⊴ Y →
    X.length - Z.length ≤ t →
    Y.length - Z.length ≤ t →
    X = Y

def insCode (C : Set (List α)) (t : Nat) : Prop :=
  ∀ X Y Z : List α,
    X ∈ C → Y ∈ C → X ⊴ Z → Y ⊴ Z →
    Z.length - X.length ≤ t →
    Z.length - Y.length ≤ t →
    X = Y

def editCode (C : Set (List α)) (t : Nat) [DecidableEq α] : Prop :=
  ∀ X Y Z : List α,
    X ∈ C → Y ∈ C →
    insDelDist Z X ≤ t →
    insDelDist Z Y ≤ t →
    X = Y

end InsDel
end CodingTheory
end HeytingLean
