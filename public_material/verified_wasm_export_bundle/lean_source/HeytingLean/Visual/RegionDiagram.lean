import HeytingLean.LoF.Nucleus
import HeytingLean.LoF.HeytingCore

/-
# Visual.RegionDiagram

A small, fully total syntax for region-style Heyting expressions over the
fixed-point algebra `Ω_R` of a reentry nucleus `R`, together with an
evaluation function back into `Ω_R`.

The intent is to provide a lightweight, diagram-friendly representation of:

* intersections and unions of regions;
* Heyting implication;
* negation modelled as implication into bottom.

This module does not introduce any I/O or UI dependencies; it is purely
semantic and suitable as a backend for future visualization/export layers.
-/

namespace HeytingLean
namespace Visual
namespace Region

open HeytingLean.LoF

universe u

variable {α : Type u} [PrimaryAlgebra α]

/-- Syntax of region diagrams over the Heyting core `Ω_R`.

The constructors mirror the basic Heyting operations on `R.Omega`:

* `atom a` is a primitive region corresponding to `a : Ω_R`;
* `inf x y` represents intersection;
* `sup x y` represents union;
* `himp x y` represents implication;
* `neg x` is the negation of a region, defined semantically as implication to
  bottom in `Ω_R`.
-/
inductive Expr (R : Reentry α) : Type u where
  | atom (a : R.Omega) : Expr R
  | inf (x y : Expr R) : Expr R
  | sup (x y : Expr R) : Expr R
  | himp (x y : Expr R) : Expr R
  | neg (x : Expr R) : Expr R

namespace Expr

variable {R : Reentry α}

/-- Evaluate a region expression into `Ω_R`. -/
def eval : Expr R → R.Omega
  | atom a => a
  | inf x y => eval x ⊓ eval y
  | sup x y => eval x ⊔ eval y
  | himp x y => eval x ⇨ eval y
  | neg x => eval x ⇨ (⊥ : R.Omega)

@[simp] lemma eval_atom (a : R.Omega) :
    eval (Expr.atom (R := R) a) = a :=
  rfl

@[simp] lemma eval_inf (x y : Expr R) :
    eval (Expr.inf (R := R) x y) = eval x ⊓ eval y :=
  rfl

@[simp] lemma eval_sup (x y : Expr R) :
    eval (Expr.sup (R := R) x y) = eval x ⊔ eval y :=
  rfl

@[simp] lemma eval_himp (x y : Expr R) :
    eval (Expr.himp (R := R) x y) = eval x ⇨ eval y :=
  rfl

@[simp] lemma eval_neg (x : Expr R) :
    eval (Expr.neg (R := R) x) = eval x ⇨ (⊥ : R.Omega) :=
  rfl

end Expr

end Region
end Visual
end HeytingLean
