import Mathlib.Order.GaloisConnection.Basic

/-!
Comparison Functors — Parametric definition of f and g

This module keeps the comparison path generic: we package the left and right
adjoints along with their facts. Downstream code (comparison nucleus, diamond
factor) works uniformly from this Spec without assuming concrete carriers.
-/

namespace HeytingLean
namespace LoF
namespace Comparison

open Classical

universe u v

/- Spec for the comparison path L ⇄ Ωℓ. -/
structure Spec (L : Type u) (Ωℓ : Type v) where
  f        : L → Ωℓ
  g        : Ωℓ → L
  f_mono   : Monotone f
  g_mono   : Monotone g
  gc       : GaloisConnection f g
  name     : String := "comparison"

/- Derived helper: the comparison closure/nucleus act `g ∘ f`. -/
def Rc {L : Type u} {Ωℓ : Type v} (S : Spec L Ωℓ) : L → L := fun x => S.g (S.f x)

lemma Rc_monotone {L : Type u} {Ωℓ : Type v} (S : Spec L Ωℓ) : Monotone (Rc S) := by
  intro x y hxy
  exact S.g_mono (S.f_mono hxy)

lemma Rc_extensive {L : Type u} {Ωℓ : Type v} (S : Spec L Ωℓ) : ∀ x, x ≤ Rc S x := by
  intro x
  -- x ≤ g (f x) by GC equivalence applied to reflexivity f x ≤ f x
  have hx : S.f x ≤ S.f x := le_rfl
  exact (S.gc.le_iff_le_u).mpr hx

lemma Rc_idempotent {L : Type u} {Ωℓ : Type v} (S : Spec L Ωℓ) : ∀ x, Rc S (Rc S x) = Rc S x := by
  intro x
  -- standard `u_l_u = u` law from GC (in the notation of mathlib: u ∘ l ∘ u = u)
  -- Here u = g and l = f.
  -- We obtain equalities pointwise by antisymmetry from ≤ in both directions.
  apply le_antisymm
  · -- Rc (Rc x) ≤ Rc x via monotonicity of g ∘ f and `l_u_le` (f (g (f x)) ≤ f x)
    have hfg : S.f (S.g (S.f x)) ≤ S.f x := S.gc.l_u_le (b := S.f x)
    exact S.g_mono hfg
  · -- Rc x ≤ Rc (Rc x) using extensivity at `x := Rc x`
    exact Rc_extensive S (Rc S x)

end Comparison
end LoF
end HeytingLean
