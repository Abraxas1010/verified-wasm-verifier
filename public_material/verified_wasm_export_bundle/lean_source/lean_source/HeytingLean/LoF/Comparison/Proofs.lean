import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.Lattice
import HeytingLean.LoF.Comparison.Functors

/-!
Comparison Proofs — general consequences from a Spec

We work parametrically from Spec to avoid repository‑specific carriers.
-/

namespace HeytingLean
namespace LoF
namespace Comparison

open Classical

universe u v

variable {L : Type u} {Ωℓ : Type v}

variable (S : Spec L Ωℓ)

lemma Rc_le_iff {x y : L} : Rc S x ≤ y ↔ S.f x ≤ S.f y := by
  -- From GC: g (f x) ≤ y ↔ f x ≤ f y
  -- Rewrite to the expected shape.
  have := S.gc.le_iff_le_u
  -- le_iff_le_u : a ≤ g b ↔ f a ≤ b; set a := x and b := f y
  simpa using (S.gc.le_iff_le_u (a := x) (b := S.f y))

lemma Rc_inf_le {x y : L} [LE L] : Rc S (x ⊓ y) ≤ Rc S x ⊓ Rc S y := by
  -- Always holds from monotonicity; equality requires frame structure, which we
  -- do not assume in this generic file.
  refine le_inf ?h1 ?h2
  · exact (Rc_monotone S) inf_le_left
  · exact (Rc_monotone S) inf_le_right

end Comparison
end LoF
end HeytingLean
