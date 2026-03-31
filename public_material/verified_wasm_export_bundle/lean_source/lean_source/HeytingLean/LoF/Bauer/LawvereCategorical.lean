import Mathlib.CategoryTheory.Closed.Cartesian

/-!
# Lawvere fixed-point theorem (categorical, CCC form)

This file upgrades the `Type`/`Set`-level Lawvere diagonal argument
(`HeytingLean.LoF.Bauer.LawvereFixedPoint`) to Mathlib’s cartesian-closed API
(`CategoryTheory.CartesianClosed` over a `CartesianMonoidalCategory`).

We use a *weak* (global-point) notion of point-surjectivity:

`φ : A ⟶ A ⟹ B` is weakly point-surjective if every global element of `A ⟹ B`
factors through `φ`.

Then every endomorphism `f : B ⟶ B` has a global fixed point `b : 𝟙 ⟶ B`.
-/

namespace HeytingLean
namespace LoF
namespace Bauer

namespace LawvereCategorical

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable {A B : C} [CategoryTheory.Exponentiable A]

/-- Weak (global-point) point-surjectivity for `φ : A ⟶ A ⟹ B`. -/
def WeaklyPointSurjective (φ : A ⟶ A ⟹ B) : Prop :=
  ∀ g : 𝟙_ C ⟶ A ⟹ B, ∃ a : 𝟙_ C ⟶ A, a ≫ φ = g

private def diag (A : C) : A ⟶ A ⊗ A :=
  lift (𝟙 A) (𝟙 A)

private def eval (A B : C) [CategoryTheory.Exponentiable A] : A ⊗ (A ⟹ B) ⟶ B :=
  (CategoryTheory.exp.ev A).app B

/-- The “self-application” map `a ↦ (φ a) a`, expressed using the cartesian closed evaluator. -/
private def selfApply (φ : A ⟶ A ⟹ B) : A ⟶ B :=
  diag A ≫ (A ◁ φ) ≫ eval A B

omit [CategoryTheory.Exponentiable A] in
private lemma point_diag (a : 𝟙_ C ⟶ A) :
    a ≫ diag A = lift a a := by
  ext <;> simp [diag]

private lemma point_selfApply (φ : A ⟶ A ⟹ B) (a : 𝟙_ C ⟶ A) :
    a ≫ selfApply (A := A) (B := B) φ = lift a (a ≫ φ) ≫ eval A B := by
  unfold selfApply
  have hdiag : a ≫ diag A = lift a a := point_diag (A := A) a
  have hpair' : (lift a a) ≫ (A ◁ φ) ≫ eval A B = lift a (a ≫ φ) ≫ eval A B := by
    simp
  calc
    a ≫ diag A ≫ (A ◁ φ) ≫ eval A B
        = (a ≫ diag A) ≫ (A ◁ φ) ≫ eval A B := by
            simp [Category.assoc]
    _ = (lift a a) ≫ (A ◁ φ) ≫ eval A B := by
            simp [hdiag]
    _ = lift a (a ≫ φ) ≫ eval A B := hpair'

omit [CategoryTheory.Exponentiable A] in
private lemma lift_id_comp_rightUnitor_hom (x : 𝟙_ C ⟶ A) :
    lift x (𝟙 (𝟙_ C)) ≫ (ρ_ A).hom = x := by
  -- In a Cartesian monoidal category, `ρ_ A` agrees with `fst A 𝟙`.
  have hρ : (ρ_ A).hom = fst A (𝟙_ C) := by
    -- `A ◁ toUnit 𝟙` is the identity, so the lemma reduces to `ρ = fst`.
    simpa using
      (whiskerLeft_toUnit_comp_rightUnitor_hom (C := C) (X := A) (Y := (𝟙_ C)))
  simp [hρ]

private lemma eval_at_point_of_curry
    (h : A ⟶ B) (a : 𝟙_ C ⟶ A) :
    lift a
        (CategoryTheory.CartesianClosed.curry (A := A) (Y := (𝟙_ C)) (X := B) ((ρ_ A).hom ≫ h))
        ≫ eval A B
      =
      (a ≫ h) := by
  let g : 𝟙_ C ⟶ A ⟹ B :=
    CategoryTheory.CartesianClosed.curry (A := A) (Y := (𝟙_ C)) (X := B) ((ρ_ A).hom ≫ h)
  -- Rewrite `lift a g` as a composite through `A ⊗ 𝟙`, then use `uncurry` and simplify.
  have hlift : lift a g = lift a (𝟙 (𝟙_ C)) ≫ (A ◁ g) := by
    -- Both sides are maps `𝟙 ⟶ A ⊗ (A ⟹ B)` with the same projections.
    ext <;> simp
  have h1 : lift a g ≫ eval A B = lift a (𝟙 (𝟙_ C)) ≫ (A ◁ g) ≫ eval A B := by
    rw [hlift]
    simp
  calc
    lift a g ≫ eval A B
        = lift a (𝟙 (𝟙_ C)) ≫ (A ◁ g) ≫ eval A B := h1
    _ = lift a (𝟙 (𝟙_ C)) ≫ CategoryTheory.CartesianClosed.uncurry (A := A) (Y := (𝟙_ C)) g := by
        simp [CategoryTheory.CartesianClosed.uncurry_eq, eval]
    _ = lift a (𝟙 (𝟙_ C)) ≫ ((ρ_ A).hom ≫ h) := by
        simp [g]
    _ = a ≫ h := by
        simp

/-- **Lawvere fixed-point theorem (categorical):**
if `φ : A ⟶ A ⟹ B` is weakly point-surjective, then every `f : B ⟶ B` has a fixed point
`b : 𝟙 ⟶ B` with `b ≫ f = b`. -/
theorem exists_fixedPoint_of_weaklyPointSurjective
    (φ : A ⟶ A ⟹ B) (hφ : WeaklyPointSurjective (A := A) (B := B) φ) (f : B ⟶ B) :
    ∃ b : 𝟙_ C ⟶ B, b ≫ f = b := by
  classical
  let d : A ⟶ B := selfApply (A := A) (B := B) φ
  let h : A ⟶ B := d ≫ f
  let g : 𝟙_ C ⟶ A ⟹ B :=
    CategoryTheory.CartesianClosed.curry (A := A) (Y := (𝟙_ C)) (X := B) ((ρ_ A).hom ≫ h)
  rcases hφ g with ⟨a0, ha0⟩
  let b : 𝟙_ C ⟶ B := lift a0 (a0 ≫ φ) ≫ eval A B
  refine ⟨b, ?_⟩
  -- Evaluate the equality `a0 ≫ φ = g` at `a0` to obtain the diagonal equation `b = b ≫ f`.
  have hb_as_g : b = lift a0 g ≫ eval A B := by
    -- rewrite `a0 ≫ φ` to `g` under `lift`
    simp [b, ha0]
  have hb_f : lift a0 g ≫ eval A B = b ≫ f := by
    -- `g` is the curry of `h = d ≫ f`, so evaluation at `a0` yields `a0 ≫ h = (a0 ≫ d) ≫ f`.
    have h_eval : lift a0 g ≫ eval A B = a0 ≫ h := by
      simpa [g] using (eval_at_point_of_curry (A := A) (B := B) h a0)
    have hb_d : a0 ≫ d = b := by
      -- `d` is self-application; at a point it becomes `lift a0 (a0 ≫ φ) ≫ eval`.
      simpa [b, d] using (point_selfApply (A := A) (B := B) φ a0)
    have h_rhs : a0 ≫ h = b ≫ f := by
      -- `a0 ≫ h = (a0 ≫ d) ≫ f`, and `a0 ≫ d = b`.
      calc
        a0 ≫ h = a0 ≫ d ≫ f := by simp [h]
        _ = b ≫ f := by
            simpa [Category.assoc] using congrArg (fun t => t ≫ f) hb_d
    exact h_eval.trans h_rhs
  -- conclude
  simpa [hb_as_g] using hb_f.symm

end LawvereCategorical

end Bauer
end LoF
end HeytingLean
