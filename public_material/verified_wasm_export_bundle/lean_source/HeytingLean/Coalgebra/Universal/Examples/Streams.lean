import HeytingLean.Coalgebra.Universal.Bisimulation
import Mathlib.Data.Stream.Init

/-!
# Universal coalgebra examples: streams

We model streams as the final coalgebra of the functor `F X = A × X`.

This file focuses on a minimal, executable-friendly bisimulation principle:
any relation `R` that is closed under observing head/tail implies equality.

Mathlib already provides this as `Stream'.eq_of_bisim`, and we show how it matches
the `RelBisim.IsBisimulation` interface from `HeytingLean.Coalgebra.Universal`.
-/

namespace HeytingLean
namespace Coalgebra
namespace Universal
namespace Examples

open CategoryTheory

universe u

variable (A : Type u)

/-- Stream endofunctor: `X ↦ A × X`. -/
def StreamF : Type u ⥤ Type u where
  obj X := A × X
  map {X Y} (f : X → Y) := fun p => (p.1, f p.2)
  map_id := by
    intro X
    funext p
    rfl
  map_comp := by
    intro X Y Z f g
    funext p
    rfl

instance : Relator (StreamF (A := A)) where
  LiftR {α β} R x y := x.1 = y.1 ∧ R x.2 y.2
  mono := by
    intro α β R S h x y hxy
    exact ⟨hxy.1, h _ _ hxy.2⟩

/-- The canonical stream coalgebra `Stream' A → A × Stream' A`. -/
def streamCoalg : Coalg (StreamF (A := A)) :=
  Coalg.mk (F := StreamF (A := A)) (Stream' A) (fun s => (Stream'.head s, Stream'.tail s))

namespace StreamBisim

open RelBisim

/-- A relation `R` on streams is a bisimulation in the `Stream'` sense if heads match and tails relate. -/
def IsStreamBisim (R : Stream' A → Stream' A → Prop) : Prop :=
  ∀ ⦃s t⦄, R s t → Stream'.head s = Stream'.head t ∧ R (Stream'.tail s) (Stream'.tail t)

theorem isStreamBisim_of_isBisimulation (R : Stream' A → Stream' A → Prop)
    (h : IsBisimulation (F := StreamF (A := A)) (streamCoalg (A := A)) (streamCoalg (A := A)) R) :
    IsStreamBisim (A := A) R := by
  intro s t hst
  -- unfold the bisimulation step for `StreamF`
  have hstep : Step (F := StreamF (A := A)) (streamCoalg (A := A)) (streamCoalg (A := A)) R s t :=
    h s t hst
  -- `Step` is `LiftR` applied to `str`.
  exact hstep

theorem eq_of_isBisimulation (R : Stream' A → Stream' A → Prop)
    (h : IsBisimulation (F := StreamF (A := A)) (streamCoalg (A := A)) (streamCoalg (A := A)) R) :
    ∀ {s t : Stream' A}, R s t → s = t := by
  intro s t hst
  have hb : Stream'.IsBisimulation R := isStreamBisim_of_isBisimulation (A := A) R h
  exact Stream'.eq_of_bisim (R := R) hb hst

end StreamBisim

/-- A simple “zip” on streams (pointwise pairing). -/
def zip {α β : Type u} (s : Stream' α) (t : Stream' β) : Stream' (α × β) :=
  fun n => (s n, t n)

@[simp] theorem head_zip {α β : Type u} (s : Stream' α) (t : Stream' β) :
    Stream'.head (zip s t) = (Stream'.head s, Stream'.head t) :=
  rfl

@[simp] theorem tail_zip {α β : Type u} (s : Stream' α) (t : Stream' β) :
    Stream'.tail (zip s t) = zip (Stream'.tail s) (Stream'.tail t) := by
  rfl

end Examples
end Universal
end Coalgebra
end HeytingLean

