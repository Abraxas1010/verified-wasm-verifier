import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import HeytingLean.LoF.MRSystems.Coalgebra

/-!
# Moore coalgebras have a nontrivial terminal object (Phase E.3, refinement)

`MRSystems/ReaderTerminal.lean` shows the reader endofunctor `X ↦ (A → X)` has a **trivial**
terminal coalgebra (`PUnit`). To obtain a nontrivial “behavior semantics” terminal object, we
switch to the standard Moore-machine functor:

```
F(X) := B × (A → X)
```

This file proves that the coalgebra with carrier `List A → B` is **terminal** for `F`-coalgebras,
with structure map given by “output at `[]`” and “derivative along `a : A`”.

Objectivity boundary:
- This is a coalgebraic semantics result in `Type`.
- It does not (yet) identify the “right” functor for full Rosen admissibility/selection; it only
  demonstrates a principled nontrivial terminal-coalgebra pattern compatible with `R : B → A → B`.
-/

namespace HeytingLean
namespace LoF
namespace MRSystems

open CategoryTheory
open CategoryTheory.Limits

universe u v

/-! ## The Moore endofunctor -/

/-- The Moore-machine endofunctor `X ↦ B × (A → X)` on `Type`. -/
def MooreEndo (A : Type u) (B : Type v) : Type (max u v) ⥤ Type (max u v) where
  obj X := B × (A → X)
  map {X Y} (f : X → Y) := fun p => (p.1, fun a => f (p.2 a))
  map_id := by
    intro X
    rfl
  map_comp := by
    intro X Y Z f g
    rfl

/-! ## The final coalgebra candidate: behaviors on finite words -/

/-- Behaviors for the Moore functor: outputs indexed by finite input words. -/
abbrev MooreFinal (A : Type u) (B : Type v) : Type (max u v) :=
  List A → B

/-- The coalgebra structure on `List A → B`:
`str f = (f [], fun a => fun w => f (a :: w))`. -/
def mooreFinalCoalgebra (A : Type u) (B : Type v) :
    CategoryTheory.Endofunctor.Coalgebra (MooreEndo A B) where
  V := MooreFinal A B
  str := fun f => (f [], fun a => fun w => f (a :: w))

namespace MooreFinal

variable {A : Type u} {B : Type v}

/-- Semantics map from any Moore coalgebra into the final coalgebra carrier `List A → B`. -/
def sem (X : CategoryTheory.Endofunctor.Coalgebra (MooreEndo A B)) (x : X.V) : MooreFinal A B
  | [] => (X.str x).1
  | a :: w => sem X ((X.str x).2 a) w

@[simp] theorem sem_nil (X : CategoryTheory.Endofunctor.Coalgebra (MooreEndo A B)) (x : X.V) :
    sem (A := A) (B := B) X x [] = (X.str x).1 := by
  rfl

@[simp] theorem sem_cons (X : CategoryTheory.Endofunctor.Coalgebra (MooreEndo A B)) (x : X.V) (a : A)
    (w : List A) :
    sem (A := A) (B := B) X x (a :: w) = sem (A := A) (B := B) X ((X.str x).2 a) w := by
  rfl

/-- The canonical coalgebra morphism `X ⟶ mooreFinalCoalgebra`. -/
def homToFinal (X : CategoryTheory.Endofunctor.Coalgebra (MooreEndo A B)) :
    X ⟶ mooreFinalCoalgebra A B where
  f := sem (A := A) (B := B) X
  h := by
    funext x
    -- Unfold the Moore functor map and the final-coalgebra structure; definitional reductions close it.
    simp [MooreEndo, mooreFinalCoalgebra, sem]

/-- Uniqueness of coalgebra morphisms into the final coalgebra. -/
theorem homToFinal_unique (X : CategoryTheory.Endofunctor.Coalgebra (MooreEndo A B))
    (g : X ⟶ mooreFinalCoalgebra A B) :
    g = homToFinal (A := A) (B := B) X := by
  ext x
  funext w
  induction w generalizing x with
  | nil =>
      -- Project the coalgebra morphism law to the output component.
      have hx := congrArg Prod.fst (congrArg (fun h => h x) g.h)
      -- `hx : (X.str x).1 = g.f x []`.
      simpa [homToFinal, MooreEndo, mooreFinalCoalgebra, sem] using hx.symm
  | cons a w ih =>
      -- Project the coalgebra morphism law to the transition component, then evaluate at `a, w`.
      have hx := congrArg Prod.snd (congrArg (fun h => h x) g.h)
      have hxaw : g.f ((X.str x).2 a) w = g.f x (a :: w) := by
        have := congrArg (fun k => k a w) hx
        simpa [MooreEndo, mooreFinalCoalgebra] using this
      -- Reduce `g.f x (a :: w)` to the successor state, then apply the induction hypothesis.
      calc
        g.f x (a :: w) = g.f ((X.str x).2 a) w := by simpa using hxaw.symm
        _ = sem (A := A) (B := B) X ((X.str x).2 a) w := ih ((X.str x).2 a)
        _ = sem (A := A) (B := B) X x (a :: w) := by rfl

end MooreFinal

/-! ## Terminality -/

variable (A : Type u) (B : Type v)

/-- `List A → B` is terminal for Moore coalgebras `X ↦ B × (A → X)`. -/
noncomputable def mooreFinalCoalgebra_isTerminal :
    IsTerminal (mooreFinalCoalgebra A B) := by
  classical
  refine IsTerminal.ofUniqueHom (Y := mooreFinalCoalgebra A B)
    (h := fun X => MooreFinal.homToFinal (A := A) (B := B) X)
    (uniq := fun X g => ?_)
  exact MooreFinal.homToFinal_unique (A := A) (B := B) X g

/-! ## Minimal MR hook: transition-only core as a Moore coalgebra -/

namespace MRCore

variable (m : MRCore.{u, v})

/-- View the repair map `R : B → (A → B)` as a Moore coalgebra (state lifted to `ULift` to fit `Type (max u v)`). -/
def toMooreCoalgebra (m : MRCore.{u, v}) : CategoryTheory.Endofunctor.Coalgebra (MooreEndo m.A m.B) where
  V := ULift.{u, v} m.B
  str := fun b => (b.down, fun a => ULift.up (m.R b.down a))

/-- For the Moore coalgebra induced by an `MRCore`, one-letter semantics is exactly `R`. -/
@[simp] theorem sem_singleton (m : MRCore.{u, v}) (b : (m.toMooreCoalgebra).V) (a : m.A) :
    MooreFinal.sem (A := m.A) (B := m.B) (m.toMooreCoalgebra) b [a] = m.R b.down a := by
  rfl

/-- Moore semantics from an unlifted initial state. -/
def semFrom (m : MRCore.{u, v}) (b : m.B) : MooreFinal m.A m.B :=
  MooreFinal.sem (A := m.A) (B := m.B) (m.toMooreCoalgebra) (ULift.up b)

@[simp] theorem semFrom_nil (m : MRCore.{u, v}) (b : m.B) :
    m.semFrom b [] = b := by
  rfl

@[simp] theorem semFrom_singleton (m : MRCore.{u, v}) (b : m.B) (a : m.A) :
    m.semFrom b [a] = m.R b a := by
  rfl

/-- The deterministic “run” of an `MRCore` transition along a finite input word. -/
def run (m : MRCore.{u, v}) : m.B → List m.A → m.B
  | b, [] => b
  | b, a :: w => run m (m.R b a) w

@[simp] theorem semFrom_eq_run (m : MRCore.{u, v}) (b : m.B) (w : List m.A) :
    m.semFrom b w = run m b w := by
  induction w generalizing b with
  | nil =>
      rfl
  | cons a w ih =>
      -- Unfold both recurrences and use the IH.
      simpa [MRCore.semFrom, run] using ih (b := m.R b a)

end MRCore

end MRSystems
end LoF
end HeytingLean
