import HeytingLean.Coalgebra.Universal.Bisimulation

/-!
# Universal coalgebra examples: deterministic automata

We model deterministic automata as coalgebras for the functor

`F X = Bool × (A → X)`.

We then show that a standard “bisimulation” relation implies equality of the induced
language semantics (`List A → Bool`).

This is an executable-first sanity layer; it does not claim any final-coalgebra existence.
-/

namespace HeytingLean
namespace Coalgebra
namespace Universal
namespace Examples

open CategoryTheory

universe u

variable (A : Type u)

/-- Deterministic-automaton functor: `X ↦ Bool × (A → X)`. -/
def DFAF : Type u ⥤ Type u where
  obj X := Bool × (A → X)
  map {X Y} (f : X → Y) := fun p => (p.1, fun a => f (p.2 a))
  map_id := by
    intro X
    funext p
    rfl
  map_comp := by
    intro X Y Z f g
    funext p
    rfl

instance : Relator (DFAF (A := A)) where
  LiftR {α β} R x y := x.1 = y.1 ∧ ∀ a, R (x.2 a) (y.2 a)
  mono := by
    intro α β R S h x y hxy
    refine ⟨hxy.1, ?_⟩
    intro a
    exact h _ _ (hxy.2 a)

/-- A DFA coalgebra is just a carrier state type with output+transition. -/
abbrev DFA := Coalg (DFAF (A := A))

namespace DFA

variable {A}

/-- Output bit of a state. -/
def out (M : DFA (A := A)) (s : M.V) : Bool :=
  (M.str s).1

/-- Next-state transition. -/
def step (M : DFA (A := A)) (s : M.V) (a : A) : M.V :=
  (M.str s).2 a

/-- Language semantics of a state: run on a word and return the final output bit.

This is a *Mealy/Moore-style* semantics (output observed at the final state).
-/
def lang (M : DFA (A := A)) (s : M.V) : List A → Bool
  | [] => out M s
  | a :: w => lang M (step M s a) w

end DFA

open DFA

/-- A relation `R` is a bisimulation on a DFA if it matches output and steps. -/
def IsDFABisim (M : DFA (A := A)) (R : M.V → M.V → Prop) : Prop :=
  ∀ ⦃s t⦄, R s t → out M s = out M t ∧ ∀ a, R (step M s a) (step M t a)

theorem isDFABisim_of_isBisimulation (M : DFA (A := A)) (R : M.V → M.V → Prop)
    (h : RelBisim.IsBisimulation (F := DFAF (A := A)) M M R) :
    IsDFABisim (A := A) M R := by
  intro s t hst
  have hstep : RelBisim.Step (F := DFAF (A := A)) M M R s t := h s t hst
  exact hstep

/-- If `R` is a DFA bisimulation, then related states have the same language. -/
theorem lang_eq_of_bisim (M : DFA (A := A)) (R : M.V → M.V → Prop)
    (hR : IsDFABisim (A := A) M R) :
    ∀ {s t : M.V}, R s t → DFA.lang (A := A) M s = DFA.lang (A := A) M t := by
  intro s t hst
  funext w
  induction w generalizing s t with
  | nil =>
      simpa [DFA.lang, DFA.out] using (hR hst).1
  | cons a w ih =>
      have hstep := (hR hst).2 a
      simpa [DFA.lang, DFA.step] using ih hstep

end Examples
end Universal
end Coalgebra
end HeytingLean

