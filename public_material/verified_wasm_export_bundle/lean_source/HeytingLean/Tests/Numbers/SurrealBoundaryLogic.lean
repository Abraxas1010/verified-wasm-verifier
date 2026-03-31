import HeytingLean.Numbers.Surreal.BoundaryLogic
import HeytingLean.Numbers.Surreal.Tactics

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Numbers.Surreal
open HeytingLean.Numbers.SurrealCore

/-! Smoke checks for Surreal boundary/co-negation operators. -/

#check BoundaryOps
#check setBoundaryOps

example (A : Set PreGame) :
    setBoundaryOps.boundary A = A ∩ Aᶜ := by
  exact set_boundary_eq_inter_compl A

example (A : Set PreGame) :
    setBoundaryOps.nonExistent A := by
  exact set_nonExistent_all A

example (A : Set PreGame) :
    ¬ setBoundaryOps.impossible A := by
  exact set_not_impossible A

example (A B : Set PreGame) (hAB : A ⊆ B) :
    setBoundaryOps.boundary B ⊆ setBoundaryOps.boundary A := by
  exact set_boundary_antitone hAB

example (A : Set PreGame) :
    setBoundaryOps.nonExistent A := by
  noneist_simp

example : fin3BoundaryOps.boundary (0 : Fin 3) = 0 := by
  exact fin3_boundary_zero

example : fin3BoundaryOps.boundary (1 : Fin 3) = 1 := by
  exact fin3_boundary_one

example : fin3BoundaryOps.impossible (1 : Fin 3) := by
  exact fin3_impossible_one

example : ∃ a : Fin 3, fin3BoundaryOps.impossible a := by
  exact fin3_exists_impossible

example : ¬ ∀ a : Fin 3, fin3BoundaryOps.nonExistent a := by
  exact fin3_not_all_nonExistent

example :
    ¬ ∃ b : Fin 3, (1 : Fin 3) ⊓ b = (0 : Fin 3) ∧ (1 : Fin 3) ⊔ b = (2 : Fin 3) := by
  exact fin3_one_has_no_complement

example : fin3ProdBoundaryOps.boundary ((0 : Fin 3), (0 : Fin 3)) = ((0 : Fin 3), (0 : Fin 3)) := by
  exact fin3Prod_boundary_zero

example : fin3ProdBoundaryOps.boundary ((1 : Fin 3), (0 : Fin 3)) = ((1 : Fin 3), (0 : Fin 3)) := by
  exact fin3Prod_boundary_mid

example : fin3ProdBoundaryOps.impossible ((1 : Fin 3), (0 : Fin 3)) := by
  exact fin3Prod_impossible_mid

example (a : Fin 3) (b : Fin 3) :
    (canonicalBoundaryOps (α := Fin 3 × Fin 3)).nonExistent (a, b) ↔
      (canonicalBoundaryOps (α := Fin 3)).nonExistent a ∧
        (canonicalBoundaryOps (α := Fin 3)).nonExistent b := by
  exact canonical_nonExistent_prod_iff (a := a) (b := b)

example :
    (canonicalBoundaryOps (α := Fin 3 × Fin 3)).impossible ((1 : Fin 3), (0 : Fin 3)) := by
  exact canonical_impossible_prod_left (a := (1 : Fin 3)) (b := (0 : Fin 3)) fin3_impossible_one

example (A : Set PreGame) :
    (canonicalBoundaryOps (α := Fin 3 × Set PreGame)).impossible ((1 : Fin 3), A) := by
  exact canonical_impossible_prod_left (a := (1 : Fin 3)) (b := A) fin3_impossible_one

example (a : Fin 3) (A : Set PreGame)
    (h : (canonicalBoundaryOps (α := Fin 3 × Set PreGame)).impossible (a, A)) :
    (canonicalBoundaryOps (α := Fin 3)).impossible a ∨
      (canonicalBoundaryOps (α := Set PreGame)).impossible A := by
  exact canonical_impossible_prod_elim (a := a) (b := A) h

example : ∃ a : Fin 3 × Fin 3, fin3ProdBoundaryOps.nonExistent a := by
  exact fin3Prod_exists_nonExistent

example : ∃ a : Fin 3 × Fin 3, fin3ProdBoundaryOps.impossible a := by
  exact fin3Prod_exists_impossible

example : ¬ ∀ a : Fin 3 × Fin 3, fin3ProdBoundaryOps.nonExistent a := by
  exact fin3Prod_not_all_nonExistent

example :
    ¬ ∃ b : Fin 3 × Fin 3,
      ((1 : Fin 3), (0 : Fin 3)) ⊓ b = ((0 : Fin 3), (0 : Fin 3)) ∧
      ((1 : Fin 3), (0 : Fin 3)) ⊔ b = ((2 : Fin 3), (2 : Fin 3)) := by
  exact fin3Prod_mid_has_no_complement

example :
    (canonicalBoundaryOps (α := Fin 3 × Fin 3)).nonExistent
      (((0 : Fin 3), (0 : Fin 3)) ⊓ ((2 : Fin 3), (2 : Fin 3))) := by
  exact canonical_nonExistent_inf
    (a := ((0 : Fin 3), (0 : Fin 3)))
    (b := ((2 : Fin 3), (2 : Fin 3)))
    fin3Prod_nonExistent_zero
    (by
      unfold BoundaryOps.nonExistent
      simpa using fin3Prod_boundary_top)

example :
    fin3ProdBoundaryOps.impossible (((1 : Fin 3), (0 : Fin 3)) ⊓ ((1 : Fin 3), (0 : Fin 3))) →
      fin3ProdBoundaryOps.impossible ((1 : Fin 3), (0 : Fin 3)) ∨
        fin3ProdBoundaryOps.impossible ((1 : Fin 3), (0 : Fin 3)) := by
  intro h
  exact fin3Prod_impossible_inf_elim ((1 : Fin 3), (0 : Fin 3)) ((1 : Fin 3), (0 : Fin 3)) h

end Numbers
end Tests
end HeytingLean
