import Mathlib.Data.Fintype.BigOperators

namespace HeytingLean
namespace Algebra
namespace BarConstruction

universe u

/-- Degree-`n` bar simplices for a type `M`, encoded as `n`-tuples. -/
abbrev BarSimplex (M : Type u) (n : Nat) : Type u := Fin n → M

def barFiltrationDegree (n : Nat) : Nat := n

theorem barFiltrationDegree_monotone (a b : Nat) (h : a ≤ b) :
    barFiltrationDegree a ≤ barFiltrationDegree b := h

set_option linter.unnecessarySimpa false in
theorem barSimplex_card (M : Type u) [Fintype M] (n : Nat) :
    Fintype.card (BarSimplex M n) = Fintype.card M ^ n := by
  simpa [BarSimplex] using (Fintype.card_fun (α := Fin n) (β := M))

theorem barSimplex_card_zero (M : Type u) [Fintype M] :
    Fintype.card (BarSimplex M 0) = 1 := by
  simp [BarSimplex]

end BarConstruction
end Algebra
end HeytingLean
