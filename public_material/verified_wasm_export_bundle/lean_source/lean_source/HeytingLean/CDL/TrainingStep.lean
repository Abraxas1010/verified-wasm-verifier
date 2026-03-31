import HeytingLean.CDL.Para.Type

/-!
# CDL: minimal training-step semantics in `Para(Type)`

This file introduces a compact, executable-first interface for one optimization step:

- a parametric forward map (`ParaHom`),
- a typed parameter update map driven by `(parameter, input, output)`.

The interface is intentionally small so later phases can attach invariants/proofs over a stable API.
-/

namespace HeytingLean
namespace CDL

open HeytingLean.CDL.Para

universe u

/-- Minimal categorical training-step semantics on `Type`:
`model` is the parametric forward map, `update` advances parameters after one observation. -/
structure TrainingStep (X Y : Type u) : Type (u + 1) where
  model : ParaHom X Y
  update : model.P × X × Y → model.P

namespace TrainingStep

variable {X Y Z : Type u}

/-- Forward output for a single parameter/input pair. -/
def output (t : TrainingStep X Y) (p : t.model.P) (x : X) : Y :=
  t.model.f (p, x)

/-- Execute one training step: return updated parameters and produced output. -/
def step (t : TrainingStep X Y) (p : t.model.P) (x : X) : t.model.P × Y :=
  (t.update (p, x, t.output p x), t.output p x)

@[simp] theorem step_fst (t : TrainingStep X Y) (p : t.model.P) (x : X) :
    (t.step p x).1 = t.update (p, x, t.output p x) := rfl

@[simp] theorem step_snd (t : TrainingStep X Y) (p : t.model.P) (x : X) :
    (t.step p x).2 = t.output p x := rfl

/-- Identity training-step: identity model with no-op parameter update on `PUnit`. -/
def id (X : Type u) : TrainingStep X X where
  model := ParaHom.id X
  update := fun
    | (⟨⟩, _, _) => PUnit.unit

@[simp] theorem id_P (X : Type u) : (id X).model.P = PUnit := rfl

@[simp] theorem id_step (x : X) :
    (id X).step PUnit.unit x = (PUnit.unit, x) := rfl

/-- Compose training semantics by composing forward maps and stacking parameters. -/
def comp (g : TrainingStep Y Z) (f : TrainingStep X Y) : TrainingStep X Z where
  model := ParaHom.comp g.model f.model
  update := fun
    | ((pg, pf), x, z) =>
        let y := f.output pf x
        let pf' := f.update (pf, x, y)
        let pg' := g.update (pg, y, z)
        (pg', pf')

@[simp] theorem comp_P (g : TrainingStep Y Z) (f : TrainingStep X Y) :
    (comp g f).model.P = (g.model.P × f.model.P) := rfl

@[simp] theorem comp_output (g : TrainingStep Y Z) (f : TrainingStep X Y)
    (pg : g.model.P) (pf : f.model.P) (x : X) :
    (comp g f).output (pg, pf) x = g.output pg (f.output pf x) := rfl

@[simp] theorem comp_step (g : TrainingStep Y Z) (f : TrainingStep X Y)
    (pg : g.model.P) (pf : f.model.P) (x : X) :
    (comp g f).step (pg, pf) x =
      ((g.update (pg, f.output pf x, g.output pg (f.output pf x)),
        f.update (pf, x, f.output pf x)),
       g.output pg (f.output pf x)) := rfl

/-- Constrained invariant preservation for one step:
if `update` preserves `Inv`, then `step` preserves `Inv` on the parameter component. -/
theorem step_preserves (t : TrainingStep X Y) (Inv : t.model.P → Prop)
    (hupdate : ∀ p x, Inv p → Inv (t.update (p, x, t.output p x)))
    {p : t.model.P} (hp : Inv p) (x : X) :
    Inv (t.step p x).1 := by
  simpa [step] using hupdate p x hp

end TrainingStep

end CDL
end HeytingLean
