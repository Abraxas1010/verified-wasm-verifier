import Mathlib.CategoryTheory.Category.Basic

/-!
# IteratedVirtual.Basic

Minimal, data-only scaffolding for “virtual double categories” in the sense of
Cruttwell–Shulman (generalized multicategories). This is intentionally light:
we record objects, a vertical category, proarrows, and *multi-cells* whose
horizontal source is a `Fin`-indexed string of proarrows.

Coherence laws and compositions are deferred to later iterations.
-/

namespace HeytingLean
namespace IteratedVirtual

universe u v w

open CategoryTheory

/-- Helper: a `Fin 2 → α` picking `x` at `0` and `y` at `1`. -/
def fin2 {α : Sort u} (x y : α) : Fin 2 → α :=
  Fin.cases x (fun _ => y)

/-- A data-only virtual double category:
* objects with a vertical category structure,
* proarrows (`Horiz`),
* multi-cells with a `Fin`-indexed horizontal source and `Fin`-indexed vertical frame.

This matches the “string-of-proarrows → single-proarrow” shape used for virtual double categories.
-/
structure VirtualDoubleCategory where
  Obj : Type u
  vertCat : CategoryTheory.Category.{v} Obj
  Horiz : Obj → Obj → Type v
  /-- A multi-cell whose horizontal source is a length-`n` string of proarrows
  over objects `A`, with a vertical frame `v : A i ⟶ B i`, targeting a single proarrow
  from `B 0` to `B (Fin.last n)`. -/
  Cell :
      ∀ {n : ℕ},
        (A B : Fin (n + 1) → Obj) →
          (v : ∀ i : Fin (n + 1), A i ⟶ B i) →
            (h : ∀ i : Fin n, Horiz (A i.castSucc) (A i.succ)) →
              (tgt : Horiz (B 0) (B (Fin.last n))) → Type w
  /-- Horizontal identity proarrow. -/
  horizId : ∀ a : Obj, Horiz a a

attribute [instance] VirtualDoubleCategory.vertCat

end IteratedVirtual
end HeytingLean
