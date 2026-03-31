import HeytingLean.IteratedVirtual.Basic

/-!
# IteratedVirtual.PastingFramed

Phase‑8 (research-scale) extension of `IteratedVirtual.Pasting`:

`Pasting.lean` provided free pasting syntax only for **identity-framed** (“globular”) cells.
Here we generalize the syntax to allow *arbitrary* vertical frames, i.e. internal nodes may use any
multi-cell of the underlying `VirtualDoubleCategory`.

We still do **not** provide evaluation semantics or a concrete composition law for `V.Cell`. The
only coherence asserted is for substitution/pasting-by-replacement of horizontal leaves:

- associativity of substitution (`bind_assoc`)
- left/right unit laws (`pure` is a unit)

This gives a strict-only, syntax-level notion of “virtual cells are virtual compositions of
cobordisms”, now without forcing the vertical boundary to be all identities.
-/

namespace HeytingLean
namespace IteratedVirtual

open CategoryTheory

universe u v w

/--
Formal pasting diagrams targeting a fixed proarrow `f`.

Leaves are proarrows (`pure`). Internal nodes apply an existing multi-cell of `V`
with *arbitrary* vertical frame; the horizontal inputs are themselves provided by subdiagrams.
-/
inductive PastingFramed (V : VirtualDoubleCategory.{u, v, w}) :
    ∀ {a b : V.Obj}, V.Horiz a b → Type (max u v w)
  | pure {a b : V.Obj} (f : V.Horiz a b) : PastingFramed V f
  | cell {n : ℕ}
      {A B : Fin (n + 1) → V.Obj}
      {v : ∀ i : Fin (n + 1), A i ⟶ B i}
      {h : ∀ i : Fin n, V.Horiz (A i.castSucc) (A i.succ)}
      {tgt : V.Horiz (B 0) (B (Fin.last n))}
      (c : V.Cell (n := n) (A := A) (B := B) (v := v) (h := h) (tgt := tgt))
      (args : ∀ i : Fin n, PastingFramed V (h i)) : PastingFramed V tgt

namespace PastingFramed

/-- “Substitution” / pasting-by-replacement of leaves. -/
def bind {V : VirtualDoubleCategory.{u, v, w}} {a b : V.Obj} {f : V.Horiz a b} :
    PastingFramed V f →
      (∀ {x y : V.Obj}, (g : V.Horiz x y) → PastingFramed V g) →
        PastingFramed V f
  | pure f, σ => σ f
  | PastingFramed.cell (V := V) (n := n) (A := A) (B := B) (v := v) (h := h) (tgt := tgt) c args, σ =>
      PastingFramed.cell (V := V) (n := n) (A := A) (B := B) (v := v) (h := h) (tgt := tgt) c
        (fun i => bind (V := V) (args i) σ)

@[simp] theorem bind_pure {a b : V.Obj} (f : V.Horiz a b)
    (σ : ∀ {x y : V.Obj}, (g : V.Horiz x y) → PastingFramed V g) :
    bind (V := V) (pure (V := V) f) σ = σ f := by
  rfl

@[simp] theorem bind_cell {n : ℕ}
    {A B : Fin (n + 1) → V.Obj}
    {v : ∀ i : Fin (n + 1), A i ⟶ B i}
    {h : ∀ i : Fin n, V.Horiz (A i.castSucc) (A i.succ)}
    {tgt : V.Horiz (B 0) (B (Fin.last n))}
    (c : V.Cell (n := n) (A := A) (B := B) (v := v) (h := h) (tgt := tgt))
    (args : ∀ i : Fin n, PastingFramed V (h i))
    (σ : ∀ {x y : V.Obj}, (g : V.Horiz x y) → PastingFramed V g) :
    bind (V := V) (PastingFramed.cell (V := V) (n := n) (A := A) (B := B) (v := v) (h := h) (tgt := tgt) c args) σ =
      PastingFramed.cell (V := V) (n := n) (A := A) (B := B) (v := v) (h := h) (tgt := tgt) c
        (fun i => bind (V := V) (args i) σ) := by
  rfl

/-- Right unit: substituting each leaf by itself does nothing. -/
@[simp] theorem bind_pure_right {a b : V.Obj} {f : V.Horiz a b} (p : PastingFramed V f) :
    bind (V := V) p (fun g => pure (V := V) g) = p := by
  induction p with
  | pure f =>
      rfl
  | cell c args ih =>
      simp [bind, ih]

/-- Associativity of substitution (pasting coherence). -/
theorem bind_assoc {a b : V.Obj} {f : V.Horiz a b} (p : PastingFramed V f)
    (σ : ∀ {x y : V.Obj}, (g : V.Horiz x y) → PastingFramed V g)
    (τ : ∀ {x y : V.Obj}, (g : V.Horiz x y) → PastingFramed V g) :
    bind (V := V) (bind (V := V) p σ) τ =
      bind (V := V) p (fun g => bind (V := V) (σ g) τ) := by
  induction p with
  | pure f =>
      rfl
  | cell c args ih =>
      simp [bind, ih]

end PastingFramed

end IteratedVirtual
end HeytingLean
