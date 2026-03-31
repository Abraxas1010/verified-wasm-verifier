import HeytingLean.IteratedVirtual.PastingFramedEval
import HeytingLean.Rel.Basic

/-!
# VETT.Rel.PastingEval

A small, universe-safe “evaluation target” showing that Phase‑8 `PastingFramed` diagrams can be
folded into concrete relation semantics.

Key design choice:
- We evaluate **only over small types** (`Obj := Type`), avoiding universe-cumulativity issues that
  arise with `Obj := Type u`.

This module is intentionally minimal: it provides a `VirtualDoubleCategory` whose horizontal arrows
are `Prop`-valued relations, and whose multi-cells carry an explicit evaluator plus a “tag soundness”
equation (`eval h = tgt`).
-/

namespace HeytingLean
namespace VETT
namespace Rel
namespace PastingEval

open HeytingLean.IteratedVirtual
open HeytingLean.Rel

/-- Horizontal proarrows: `Prop`-valued relations, bundled for convenient projection. -/
structure Horiz (A B : Type) where
  rel : HRel A B

@[simp] theorem Horiz.rel_mk {A B : Type} (r : HRel A B) : (Horiz.mk r).rel = r := rfl

/-- Smart constructor for `Horiz`. -/
def upHoriz {A B : Type} (r : HRel A B) : Horiz A B :=
  ⟨r⟩

@[simp] theorem upHoriz_rel {A B : Type} (r : HRel A B) : (upHoriz r).rel = r := rfl

/-- A tagged multi-cell that carries an evaluator for the target relation. -/
structure CellData {n : ℕ}
    {A B : Fin (n + 1) → Type}
    (v : ∀ i : Fin (n + 1), A i ⟶ B i)
    (h : ∀ i : Fin n, Horiz (A i.castSucc) (A i.succ))
    (tgt : Horiz (B 0) (B (Fin.last n))) where
  eval :
      (∀ i : Fin n, Horiz (A i.castSucc) (A i.succ)) →
        Horiz (B 0) (B (Fin.last n))
  /-- The evaluator agrees with the tagged target when fed the tag’s horizontal source. -/
  sound : eval h = tgt

/-- The small-types virtual double category with relations as proarrows. -/
def V : VirtualDoubleCategory.{1, 0, 0} where
  Obj := Type
  vertCat := inferInstance
  Horiz := Horiz
  Cell := fun {n} A B v h tgt => CellData (n := n) (A := A) (B := B) v h tgt
  horizId := fun A => upHoriz (RelOps.unit A)

/-! ## A canonical evaluation algebra -/

namespace Algebra

open HeytingLean.IteratedVirtual.PastingFramed

/--
An algebra whose carrier remembers a computed relation plus a proof it equals the proarrow it’s
typed by.

This lets the cell step compute using the evaluated subdiagrams, then discharge equality to `tgt`
using `CellData.sound` and the subdiagram equalities.
-/
def relAlgebra : PastingFramed.Algebra V where
  Carrier := fun {a b} (f : (V).Horiz a b) => ULift.{1} {r : (V).Horiz a b // r = f}
  pure := fun f => ⟨⟨f, rfl⟩⟩
  cell := by
    intro n A B v h tgt c args
    cases c with
    | mk eval sound =>
        refine ⟨⟨eval (fun i => (args i).down.1), ?_⟩⟩
        have hh : (fun i => (args i).down.1) = h := by
          funext i
          exact (args i).down.2
        have heq : eval (fun i => (args i).down.1) = eval h :=
          congrArg eval hh
        exact heq.trans sound

end Algebra

/-- Evaluate a diagram to its underlying relation. -/
def evalRel {A B : Type} (f : (V).Horiz A B) (p : PastingFramed V f) : (V).Horiz A B :=
  (PastingFramed.eval (V := V) Algebra.relAlgebra p).down.1

/-- Soundness: evaluation computes the tagged target relation. -/
theorem evalRel_eq {A B : Type} (f : (V).Horiz A B) (p : PastingFramed V f) :
    evalRel (A := A) (B := B) f p = f :=
  (PastingFramed.eval (V := V) Algebra.relAlgebra p).down.2

end PastingEval
end Rel
end VETT
end HeytingLean
