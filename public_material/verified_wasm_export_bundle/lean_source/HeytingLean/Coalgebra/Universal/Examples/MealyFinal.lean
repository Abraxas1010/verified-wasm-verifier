import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import HeytingLean.Coalgebra.Universal.Examples.Mealy

/-!
# Universal coalgebra examples: final Mealy coalgebra

For the Mealy endofunctor

`F(X) = A → (B × X)`

we construct an explicit terminal coalgebra in `Type`.

The carrier is the **function space of behaviors on nonempty finite words**:

`A → List A → B`.

Intuition: a behavior consumes at least one input letter (the head `a : A`) and then any
finite continuation word (`List A`), producing the output emitted at the *last* step.

This provides a canonical “semantic map” from any Mealy coalgebra into behaviors, and it
upgrades the one-state Mealy bisimilarity lemma (`Examples/Mealy.lean`) to **general state
machines** via

`Bisimilar s t ↔ sem s = sem t`.
-/

namespace HeytingLean
namespace Coalgebra
namespace Universal
namespace Examples

open CategoryTheory
open CategoryTheory.Limits

universe u

variable {A B : Type u}

/-! ## Final coalgebra candidate -/

/-- Behaviors for the Mealy functor: outputs indexed by nonempty finite words.

Represent a nonempty word as a head letter `a : A` and a tail `List A`.
-/
abbrev MealyFinal (A B : Type u) : Type u :=
  A → List A → B

/-- Coalgebra structure on behaviors.

For `f : A → List A → B` and `a : A`:

- output is `f a []` (the one-letter word `[a]`),
- next behavior is the derivative `fun a' w => f a (a' :: w)`.
-/
def mealyFinalCoalgebra (A B : Type u) : Universal.Coalg (F := MealyF A B) where
  V := MealyFinal A B
  str := fun f =>
    fun a =>
      (f a [], fun a' w => f a (a' :: w))

namespace MealyFinal

variable {A B : Type u}

/-- Semantics map from any Mealy coalgebra into the final-coalgebra carrier.

Given a state `x : X.V`, the behavior `sem X x` returns the last output produced while
processing a nonempty input word.
-/
def sem (X : Universal.Coalg (F := MealyF A B)) (x : X.V) : MealyFinal A B
  | a, [] => (X.str x a).1
  | a, a' :: w => sem X ((X.str x a).2) a' w

@[simp] theorem sem_nil (X : Universal.Coalg (F := MealyF A B)) (x : X.V) (a : A) :
    sem (A := A) (B := B) X x a [] = (X.str x a).1 := by
  rfl

@[simp] theorem sem_cons (X : Universal.Coalg (F := MealyF A B)) (x : X.V) (a a' : A) (w : List A) :
    sem (A := A) (B := B) X x a (a' :: w) = sem (A := A) (B := B) X ((X.str x a).2) a' w := by
  rfl

/-- The canonical coalgebra morphism `X ⟶ mealyFinalCoalgebra`. -/
def homToFinal (X : Universal.Coalg (F := MealyF A B)) : X ⟶ mealyFinalCoalgebra A B where
  f := sem (A := A) (B := B) X
  h := by
    funext x
    funext a
    -- Unfold the Mealy functor map and the final-coalgebra structure.
    -- The output component is `sem_nil`; the transition component is `sem_cons`.
    ext
    · simp [MealyF, mealyFinalCoalgebra, sem]
    · funext a' w
      simp [MealyF, mealyFinalCoalgebra, sem]

/-- Uniqueness of coalgebra morphisms into the final coalgebra. -/
theorem homToFinal_unique (X : Universal.Coalg (F := MealyF A B))
    (g : X ⟶ mealyFinalCoalgebra A B) :
    g = homToFinal (A := A) (B := B) X := by
  ext x
  funext a w
  revert x a
  induction w with
  | nil =>
      intro x a
      -- Project the coalgebra morphism law to the output component.
      have hx := congrArg (fun h => h x) g.h
      have hxa := congrArg (fun k => k a) hx
      have hout := congrArg Prod.fst hxa
      -- `hout : (X.str x a).1 = g.f x a []`.
      simpa [homToFinal, MealyF, mealyFinalCoalgebra, sem] using hout.symm
  | cons a' w ih =>
      intro x a
      -- Project the coalgebra morphism law to the transition component, then evaluate.
      have hx := congrArg (fun h => h x) g.h
      have hxa := congrArg (fun k => k a) hx
      have hnext := congrArg Prod.snd hxa
      have hxaw : g.f x a (a' :: w) = g.f ((X.str x a).2) a' w := by
        have := congrArg (fun k => k a' w) hnext
        -- LHS is `g.f ((X.str x a).2) a' w`, RHS is `g.f x a (a'::w)`.
        simpa [MealyF, mealyFinalCoalgebra] using this.symm
      -- Reduce the word by one step and apply the IH.
      calc
        g.f x a (a' :: w) = g.f ((X.str x a).2) a' w := hxaw
        _ = sem (A := A) (B := B) X ((X.str x a).2) a' w := by
            simpa using ih (x := (X.str x a).2) (a := a')
        _ = sem (A := A) (B := B) X x a (a' :: w) := by
            rfl

end MealyFinal

/-! ## Terminality -/

variable (A B : Type u)

/-- `A → List A → B` is terminal for Mealy coalgebras `X ↦ A → (B × X)`. -/
noncomputable def mealyFinalCoalgebra_isTerminal :
    IsTerminal (mealyFinalCoalgebra A B) := by
  classical
  refine IsTerminal.ofUniqueHom (Y := mealyFinalCoalgebra A B)
    (h := fun X => MealyFinal.homToFinal (A := A) (B := B) X)
    (uniq := fun X g => ?_)
  exact MealyFinal.homToFinal_unique (A := A) (B := B) X g

/-! ## Behavioral equivalence = bisimilarity (general state machines) -/

namespace MealyFinal

open RelBisim

variable {A B : Type u}

theorem sem_eq_of_bisimilar {S T : Universal.Coalg (F := MealyF A B)} {s : S.V} {t : T.V}
    (h : Bisimilar (F := MealyF A B) S T s t) :
    sem (A := A) (B := B) S s = sem (A := A) (B := B) T t := by
  funext a w
  revert s t
  induction w generalizing a with
  | nil =>
      intro s t h
      have hstep := bisimilar_isBisimulation (F := MealyF A B) S T s t h
      exact (hstep a).1
  | cons a' w ih =>
      intro s t h
      have hstep := bisimilar_isBisimulation (F := MealyF A B) S T s t h
      have hnext : Bisimilar (F := MealyF A B) S T ((S.str s a).2) ((T.str t a).2) :=
        (hstep a).2
      -- Peel off one input symbol and apply the IH to successor states.
      simpa [sem] using ih (a := a') (s := (S.str s a).2) (t := (T.str t a).2) hnext

theorem bisimilar_of_sem_eq {S T : Universal.Coalg (F := MealyF A B)} {s : S.V} {t : T.V}
    (h : sem (A := A) (B := B) S s = sem (A := A) (B := B) T t) :
    Bisimilar (F := MealyF A B) S T s t := by
  -- Use coinduction with the relation “has equal behavior semantics”.
  let R : Rel S.V T.V := fun s t => sem (A := A) (B := B) S s = sem (A := A) (B := B) T t
  have hR : IsBisimulation (F := MealyF A B) S T R := by
    intro s t hst
    intro a
    refine ⟨?_, ?_⟩
    · -- output equality follows by evaluating the behavior on the one-letter word `[a]`.
      have := congrArg (fun f => f a []) hst
      simpa [sem] using this
    · -- successor states have equal semantics by evaluating on extended words.
      funext a' w
      have := congrArg (fun f => f a (a' :: w)) hst
      simpa [sem] using this
  have hle := coinduction (F := MealyF A B) (S := S) (T := T) (R := R) hR
  exact hle s t h

theorem bisimilar_iff_sem_eq {S T : Universal.Coalg (F := MealyF A B)} (s : S.V) (t : T.V) :
    Bisimilar (F := MealyF A B) S T s t ↔
      sem (A := A) (B := B) S s = sem (A := A) (B := B) T t := by
  constructor
  · intro h
    exact sem_eq_of_bisimilar (A := A) (B := B) (S := S) (T := T) h
  · intro h
    exact bisimilar_of_sem_eq (A := A) (B := B) (S := S) (T := T) h

end MealyFinal

end Examples
end Universal
end Coalgebra
end HeytingLean
