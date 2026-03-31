import HeytingLean.Categorical.MonadAlgebra

/-!
# Algebra Homomorphisms

This file proves that nucleus-preserving maps are monad algebra homomorphisms
in the sense of CDL Definition 2.5.

## The Correspondence

A function `f : A → B` between monad algebras (nuclei) `T_A` and `T_B` is an
**algebra homomorphism** if it commutes with the nucleus action:

    f(T_A(x)) = T_B(f(x))

This is exactly CDL's definition of a T-algebra morphism, ensuring that the
"closed structure" is preserved by the map.

## Reference

Gavranovic et al., "Categorical Deep Learning is an Algebraic Theory of All
Architectures", ICML 2024, arXiv:2402.15332, Definition 2.5.
-/

namespace HeytingLean
namespace Categorical

open Core

/-- A function between nucleus algebras is a homomorphism if it commutes with
    the nucleus action: `f(R_A(x)) = R_B(f(x))`.

    This is exactly CDL's monad algebra homomorphism condition (Definition 2.5).

    In neural network terms: a map between activation spaces that preserves
    the "projection to fixed points" structure. -/
structure AlgebraHomomorphism
    {A B : Type*}
    [SemilatticeInf A] [OrderBot A]
    [SemilatticeInf B] [OrderBot B]
    (TA : MonadAlgebra A)
    (TB : MonadAlgebra B) where
  /-- The underlying function. -/
  toFun : A → B
  /-- The homomorphism condition: f commutes with the nucleus. -/
  map_nucleus : ∀ x, toFun (TA.R x) = TB.R (toFun x)

namespace AlgebraHomomorphism

variable {A B C : Type*}
variable [SemilatticeInf A] [OrderBot A]
variable [SemilatticeInf B] [OrderBot B]
variable [SemilatticeInf C] [OrderBot C]

/-- Coercion to function. -/
instance {TA : MonadAlgebra A} {TB : MonadAlgebra B} :
    CoeFun (AlgebraHomomorphism TA TB) (fun _ => A → B) where
  coe f := f.toFun

@[simp]
theorem coe_toFun {TA : MonadAlgebra A} {TB : MonadAlgebra B}
    (f : AlgebraHomomorphism TA TB) : f.toFun = ⇑f := rfl

/-- Extensionality for algebra homomorphisms. -/
@[ext]
theorem ext {TA : MonadAlgebra A} {TB : MonadAlgebra B}
    {f g : AlgebraHomomorphism TA TB} (h : ∀ x, f x = g x) : f = g := by
  cases f; cases g
  congr
  funext x
  exact h x

/-- The identity is an algebra homomorphism. -/
def id (TA : MonadAlgebra A) : AlgebraHomomorphism TA TA where
  toFun := _root_.id
  map_nucleus := fun _ => rfl

@[simp]
theorem id_toFun (TA : MonadAlgebra A) : (id TA).toFun = _root_.id := rfl

/-- Composition of algebra homomorphisms. -/
def comp
    {TA : MonadAlgebra A} {TB : MonadAlgebra B} {TC : MonadAlgebra C}
    (g : AlgebraHomomorphism TB TC) (f : AlgebraHomomorphism TA TB) :
    AlgebraHomomorphism TA TC where
  toFun := g.toFun ∘ f.toFun
  map_nucleus := fun x => by
    simp only [Function.comp_apply]
    rw [f.map_nucleus, g.map_nucleus]

@[simp]
theorem comp_toFun
    {TA : MonadAlgebra A} {TB : MonadAlgebra B} {TC : MonadAlgebra C}
    (g : AlgebraHomomorphism TB TC) (f : AlgebraHomomorphism TA TB) :
    (comp g f).toFun = g.toFun ∘ f.toFun := rfl

/-- Composition is associative. -/
theorem comp_assoc
    {D : Type*} [SemilatticeInf D] [OrderBot D]
    {TA : MonadAlgebra A} {TB : MonadAlgebra B}
    {TC : MonadAlgebra C} {TD : MonadAlgebra D}
    (h : AlgebraHomomorphism TC TD)
    (g : AlgebraHomomorphism TB TC)
    (f : AlgebraHomomorphism TA TB) :
    comp h (comp g f) = comp (comp h g) f := by
  ext x
  simp [comp]

/-- Left identity for composition. -/
theorem id_comp
    {TA : MonadAlgebra A} {TB : MonadAlgebra B}
    (f : AlgebraHomomorphism TA TB) :
    comp (id TB) f = f := by
  ext x
  simp [comp, id]

/-- Right identity for composition. -/
theorem comp_id
    {TA : MonadAlgebra A} {TB : MonadAlgebra B}
    (f : AlgebraHomomorphism TA TB) :
    comp f (id TA) = f := by
  ext x
  simp [comp, id]

/-- Homomorphisms preserve fixed points. -/
theorem map_fixed
    {TA : MonadAlgebra A} {TB : MonadAlgebra B}
    (f : AlgebraHomomorphism TA TB)
    {x : A} (hx : x ∈ TA.fixedPoints) :
    f x ∈ TB.fixedPoints := by
  simp only [Nucleus.fixedPoints, Set.mem_setOf_eq] at hx ⊢
  calc TB.R (f x) = f (TA.R x) := (f.map_nucleus x).symm
    _ = f x := by rw [hx]

/-- The image of a homomorphism restricted to fixed points lands in fixed points. -/
theorem image_fixed_subset_fixed
    {TA : MonadAlgebra A} {TB : MonadAlgebra B}
    (f : AlgebraHomomorphism TA TB) :
    f.toFun '' TA.fixedPoints ⊆ TB.fixedPoints := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact map_fixed f hx

end AlgebraHomomorphism

/-! ## Monotone Homomorphisms -/

/-- A monotone algebra homomorphism preserves both the order and the nucleus. -/
structure MonotoneAlgebraHomomorphism
    {A B : Type*}
    [SemilatticeInf A] [OrderBot A]
    [SemilatticeInf B] [OrderBot B]
    (TA : MonadAlgebra A)
    (TB : MonadAlgebra B)
    extends AlgebraHomomorphism TA TB where
  /-- The function is monotone. -/
  monotone : Monotone toFun

namespace MonotoneAlgebraHomomorphism

variable {A B : Type*}
variable [SemilatticeInf A] [OrderBot A]
variable [SemilatticeInf B] [OrderBot B]

/-- The identity is a monotone homomorphism. -/
def id (TA : MonadAlgebra A) : MonotoneAlgebraHomomorphism TA TA where
  toAlgebraHomomorphism := AlgebraHomomorphism.id TA
  monotone := fun _ _ h => h

end MonotoneAlgebraHomomorphism

end Categorical
end HeytingLean
