import HeytingLean.Embeddings.PerspectivalDescentHierarchy

/-!
# Embeddings.PDCExtensions.DerivedHigher

Family J representative:
- derived-stack style simplicial-degree perspectives
-/

namespace HeytingLean
namespace Embeddings
namespace PDCExtensions

inductive SimplicialDegree where
  | d0 | d1 | d2 | d3 | d4
  deriving DecidableEq, Repr, Inhabited

instance : Fintype SimplicialDegree where
  elems := {.d0, .d1, .d2, .d3, .d4}
  complete t := by cases t <;> simp

def degreeAsNat : SimplicialDegree → Nat
  | .d0 => 0
  | .d1 => 1
  | .d2 => 2
  | .d3 => 3
  | .d4 => 4

instance derivedStackPDC :
    PDCWithDescent SimplicialDegree (fun _ => Int) where
  integral _ := {x | x = 0}
  finiteness x := by
    exact Set.toFinite {t : SimplicialDegree | x t ≠ 0}
  truncate t k x := if degreeAsNat t ≤ k then x else 0
  Plato := Int
  toPlato _ x := x
  fromPlato _ p := p
  rt1 _ _ := rfl
  rt2 _ _ := rfl
  MatchingFamily x := ∀ t, x t = x .d0
  amalgamate x hx := ⟨x .d0, by intro t; exact (hx t).symm⟩

theorem derived_postnikov_truncate_zero_of_lt (t : SimplicialDegree) (k : Nat)
    (h : k < degreeAsNat t) (x : Int) :
    PerspectivalDescentCarrier.truncate
      (τ := SimplicialDegree) (Carrier := fun _ => Int) t k x = 0 := by
  by_cases hle : degreeAsNat t ≤ k
  · exact (False.elim (Nat.not_le_of_lt h hle))
  · simp [PerspectivalDescentCarrier.truncate, hle]

theorem derived_forward_cocycle :
    PDCWithTransport.ForwardCocycle
      (τ := SimplicialDegree) (Carrier := fun _ => Int) := by
  simpa using
    (PDCWithTransport.forward_is_cocycle
      (τ := SimplicialDegree) (Carrier := fun _ => Int))

end PDCExtensions
end Embeddings
end HeytingLean
