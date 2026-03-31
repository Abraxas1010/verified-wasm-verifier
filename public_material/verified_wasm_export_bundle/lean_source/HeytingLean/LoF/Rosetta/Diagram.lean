import HeytingLean.LoF.Nucleus
import HeytingLean.LoF.OmegaCategory
import HeytingLean.LoF.Rosetta.Core
import Mathlib.CategoryTheory.Category.Preorder

/-
# Rosetta.Diagram: a tiny Ω_R string-diagram DSL

This module defines a small, purely syntactic diagram language over the
fixed-point lattice `Ω_R` of a reentry nucleus `R`, together with a semantics
function into the preorder on `R.Omega` and hence the thin category on `Ω_R`.

The goal is to provide a minimal Lean-side analogue of Baez–Stay string
diagrams that can be safely evaluated inside the existing Ω_R category:

* objects: elements of `R.Omega`;
* morphisms: inequalities `A ≤ B` or, categorically, morphisms `A ⟶ B` in the
  preorder category on Ω_R;
* constructors: identity, composition, tensor (meet), and a primitive
  constructor for morphisms coming from known inequalities.

This DSL is intentionally small and fully total, serving as a foundation for
future visualization/export layers without imposing any UI or I/O dependencies.
-/

namespace HeytingLean
namespace LoF
namespace Rosetta

open CategoryTheory

universe u

variable {α : Type u} [PrimaryAlgebra α]

/-- A tiny diagram language over `Ω_R`, with objects `A B : R.Omega`.

Morphisms are built from:

* identities;
* composition;
* tensor (using the cartesian monoidal structure on Ω_R, i.e., meet);
* a primitive constructor for morphisms coming from known inequalities
  `A ≤ B`.
-/
inductive Diagram (R : Reentry α) : R.Omega → R.Omega → Type u where
  | id (A : R.Omega) :
      Diagram R A A
  | comp {A B C : R.Omega} :
      Diagram R A B → Diagram R B C → Diagram R A C
  | tensor {A₁ A₂ B₁ B₂ : R.Omega} :
      Diagram R A₁ B₁ → Diagram R A₂ B₂ →
      Diagram R (A₁ ⊓ A₂) (B₁ ⊓ B₂)
  | ofLe {A B : R.Omega} (h : A ≤ B) :
      Diagram R A B

namespace Diagram

variable {R : Reentry α}

/-- Interpret a diagram as an inequality `A ≤ B` in the preorder on `Ω_R`. -/
def eval {A B : R.Omega} : Diagram R A B → A ≤ B
  | id _ => le_rfl
  | comp f g => le_trans (eval f) (eval g)
  | tensor f g => inf_le_inf (eval f) (eval g)
  | ofLe h => h

/-- Interpret a diagram as a morphism in the preorder category on `Ω_R`. -/
def toHom {A B : R.Omega} (d : Diagram R A B) : A ⟶ B :=
  CategoryTheory.homOfLE (eval d)

@[simp] lemma eval_id (A : R.Omega) :
    eval (Diagram.id (R := R) A) = (le_rfl : A ≤ A) :=
  rfl

@[simp] lemma toHom_id (A : R.Omega) :
    toHom (Diagram.id (R := R) A) = 𝟙 A :=
  rfl

@[simp] lemma eval_ofLe {A B : R.Omega} (h : A ≤ B) :
    eval (Diagram.ofLe (R := R) h) = h :=
  rfl

@[simp] lemma toHom_ofLe {A B : R.Omega} (h : A ≤ B) :
    toHom (Diagram.ofLe (R := R) h) = CategoryTheory.homOfLE h :=
  rfl

end Diagram

end Rosetta
end LoF
end HeytingLean

