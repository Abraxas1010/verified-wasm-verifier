import HeytingLean.IteratedVirtual.Basic

/-!
# IteratedVirtual.Pasting

Coherence laws / composition laws for *virtual cells* are subtle when we do not want to
commit to any concrete “evaluation” semantics.

This module provides a **free pasting syntax** for *globular* virtual cells (identity-framed
cells), together with a substitution operation whose laws give a clean form of “pasting
coherence” (associativity + units) without requiring any extra structure on the underlying
`VirtualDoubleCategory`.

Interpretation:
- `Pasting V f` is a formal pasting diagram that *targets* the proarrow `f`;
- the leaves are just proarrows (`pure`);
- internal nodes apply an existing multi-cell of `V` whose vertical frame is all identities.

The only coherence we assert here is for *pasting by substitution*: replacing leaves by
diagrams is associative and has `pure` as a unit.
-/

namespace HeytingLean
namespace IteratedVirtual

open CategoryTheory

universe u v w

variable (V : VirtualDoubleCategory.{u, v, w})

/-- A “globular” multi-cell: the vertical frame is all identities and we take `A = B`. -/
abbrev GlobularCell {n : ℕ}
    (A : Fin (n + 1) → V.Obj)
    (h : ∀ i : Fin n, V.Horiz (A i.castSucc) (A i.succ))
    (tgt : V.Horiz (A 0) (A (Fin.last n))) : Type w :=
  V.Cell (n := n) (A := A) (B := A) (v := fun i => 𝟙 (A i)) (h := h) (tgt := tgt)

/--
Formal pasting diagrams targeting a fixed proarrow `f`.

Leaves are proarrows (`pure`). Internal nodes apply an existing identity-framed multi-cell,
whose horizontal inputs are themselves provided by subdiagrams.
-/
inductive Pasting : ∀ {a b : V.Obj}, V.Horiz a b → Type (max u v w)
  | pure {a b : V.Obj} (f : V.Horiz a b) : Pasting f
  | cell {n : ℕ}
      {A : Fin (n + 1) → V.Obj}
      {h : ∀ i : Fin n, V.Horiz (A i.castSucc) (A i.succ)}
      {tgt : V.Horiz (A 0) (A (Fin.last n))}
      (c : GlobularCell (V := V) A h tgt)
      (args : ∀ i : Fin n, Pasting (h i)) : Pasting tgt

namespace Pasting

/-- “Substitution” / pasting-by-replacement of leaves. -/
def bind {a b : V.Obj} {f : V.Horiz a b} :
    Pasting (V := V) f →
      (∀ {x y : V.Obj}, (g : V.Horiz x y) → Pasting (V := V) g) →
        Pasting (V := V) f
  | pure f, σ => σ f
  | cell c args, σ => cell c (fun i => bind (args i) σ)

@[simp] theorem bind_pure {a b : V.Obj} (f : V.Horiz a b)
    (σ : ∀ {x y : V.Obj}, (g : V.Horiz x y) → Pasting (V := V) g) :
    bind (V := V) (pure (V := V) f) σ = σ f := by
  rfl

@[simp] theorem bind_cell {n : ℕ}
    {A : Fin (n + 1) → V.Obj}
    {h : ∀ i : Fin n, V.Horiz (A i.castSucc) (A i.succ)}
    {tgt : V.Horiz (A 0) (A (Fin.last n))}
    (c : GlobularCell (V := V) A h tgt)
    (args : ∀ i : Fin n, Pasting (V := V) (h i))
    (σ : ∀ {x y : V.Obj}, (g : V.Horiz x y) → Pasting (V := V) g) :
    bind (V := V) (cell (V := V) c args) σ = cell (V := V) c (fun i => bind (V := V) (args i) σ) := by
  rfl

/-- Right unit: substituting each leaf by itself does nothing. -/
@[simp] theorem bind_pure_right {a b : V.Obj} {f : V.Horiz a b} (p : Pasting (V := V) f) :
    bind (V := V) p (fun g => pure (V := V) g) = p := by
  induction p with
  | pure f =>
      rfl
  | cell c args ih =>
      simp [bind, ih]

/-- Associativity of substitution (pasting coherence). -/
theorem bind_assoc {a b : V.Obj} {f : V.Horiz a b} (p : Pasting (V := V) f)
    (σ : ∀ {x y : V.Obj}, (g : V.Horiz x y) → Pasting (V := V) g)
    (τ : ∀ {x y : V.Obj}, (g : V.Horiz x y) → Pasting (V := V) g) :
    bind (V := V) (bind (V := V) p σ) τ =
      bind (V := V) p (fun g => bind (V := V) (σ g) τ) := by
  induction p with
  | pure f =>
      rfl
  | cell c args ih =>
      simp [bind, ih]

end Pasting

end IteratedVirtual
end HeytingLean
