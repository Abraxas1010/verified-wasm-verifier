import HeytingLean.IteratedVirtual.PastingFramed

/-!
# IteratedVirtual.PastingFramedEval

Evaluation semantics for `PastingFramed` are intentionally **parametric**:
`VirtualDoubleCategory` is data-only and does not provide a composition law for multi-cells.

Instead, we define the notion of an **algebra** for the `PastingFramed` syntax (a fold target),
and show that evaluation respects `bind` (substitution).

This closes the Phase‑8 “evaluation semantics interface” item without asserting any particular
interchange law or concrete virtual double category composition semantics.
-/

namespace HeytingLean
namespace IteratedVirtual

universe u v w

variable {V : VirtualDoubleCategory.{u, v, w}}

namespace PastingFramed

/-! ## Algebras and evaluation -/

structure Algebra (V : VirtualDoubleCategory.{u, v, w}) where
  Carrier : ∀ {a b : V.Obj}, V.Horiz a b → Type (max u v w)
  pure : ∀ {a b : V.Obj} (f : V.Horiz a b), Carrier f
  cell :
    ∀ {n : ℕ}
      {A B : Fin (n + 1) → V.Obj}
      {v : ∀ i : Fin (n + 1), A i ⟶ B i}
      {h : ∀ i : Fin n, V.Horiz (A i.castSucc) (A i.succ)}
      {tgt : V.Horiz (B 0) (B (Fin.last n))},
      V.Cell (n := n) (A := A) (B := B) (v := v) (h := h) (tgt := tgt) →
        (∀ i : Fin n, Carrier (h i)) →
          Carrier tgt

/-- Fold a `PastingFramed` diagram into an algebra. -/
def eval (A : Algebra V) :
    ∀ {a b : V.Obj} {f : V.Horiz a b}, PastingFramed V f → A.Carrier f
  | _, _, _, PastingFramed.pure f => A.pure f
  | _, _, _, PastingFramed.cell (V := V) (n := n) (A := A₀) (B := B₀) (v := v₀) (h := h₀) (tgt := tgt₀) c args =>
      A.cell (n := n) (A := A₀) (B := B₀) (v := v₀) (h := h₀) (tgt := tgt₀) c (fun i => eval A (args i))

/-- Rebase an algebra along a leaf-substitution `σ : Horiz → PastingFramed`. -/
def algebraOfSubst (A : Algebra V)
    (σ : ∀ {x y : V.Obj}, (g : V.Horiz x y) → PastingFramed V g) : Algebra V where
  Carrier := A.Carrier
  pure := fun f => eval A (σ f)
  cell := fun c args => A.cell c args

/-! ## Substitution soundness -/

theorem eval_bind (A : Algebra V) {a b : V.Obj} {f : V.Horiz a b} (p : PastingFramed V f)
    (σ : ∀ {x y : V.Obj}, (g : V.Horiz x y) → PastingFramed V g) :
    eval A (bind (V := V) p σ) = eval (algebraOfSubst (V := V) A σ) p := by
  induction p with
  | pure f =>
      rfl
  | cell c args ih =>
      simp [PastingFramed.bind, eval, algebraOfSubst, ih]

end PastingFramed

end IteratedVirtual
end HeytingLean

