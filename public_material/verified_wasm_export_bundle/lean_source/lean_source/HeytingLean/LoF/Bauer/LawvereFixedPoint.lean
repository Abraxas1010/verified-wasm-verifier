import Mathlib.Data.Bool.Basic

/-!
# Lawvere fixed-point theorem (Phase 5, core)

This module formalizes a `Type`/`Set`-level version of **Lawvere's fixed-point theorem**:

If `e : A → (A → B)` is point-surjective, then every endomap `f : B → B` has a fixed point.

As a corollary (taking `B := Bool` and `f := not`), we recover a Cantor/diagonal principle:
there is no point-surjective `e : A → (A → Bool)`.
-/

namespace HeytingLean
namespace LoF
namespace Bauer

namespace Lawvere

universe u v

/-- A map `e : A → (A → B)` is point-surjective if every `g : A → B` appears as `e a`. -/
def PointSurjective {A : Type u} {B : Type v} (e : A → A → B) : Prop :=
  ∀ g : A → B, ∃ a : A, e a = g

theorem exists_fixedPoint_of_pointSurjective {A : Type u} {B : Type v}
    (e : A → A → B) (he : PointSurjective e) (f : B → B) :
    ∃ b : B, f b = b := by
  classical
  let g : A → B := fun a => f (e a a)
  rcases he g with ⟨a0, ha0⟩
  refine ⟨e a0 a0, ?_⟩
  have hdiag : e a0 a0 = g a0 := by
    simpa using congrArg (fun h => h a0) ha0
  simpa [g] using hdiag.symm

theorem no_pointSurjective_of_noFixedPoint {A : Type u} {B : Type v}
    (f : B → B) (hf : ∀ b : B, f b ≠ b) :
    ¬ ∃ e : A → A → B, PointSurjective e := by
  intro h
  rcases h with ⟨e, he⟩
  rcases exists_fixedPoint_of_pointSurjective (A := A) (B := B) e he f with ⟨b, hb⟩
  exact hf b hb

theorem bnot_ne_self (b : Bool) : (!b) ≠ b := by
  cases b <;> decide

theorem no_pointSurjective_bool (A : Type u) :
    ¬ ∃ e : A → A → Bool, PointSurjective e := by
  refine no_pointSurjective_of_noFixedPoint (A := A) (B := Bool) (f := fun b => !b) ?_
  intro b
  exact bnot_ne_self b

end Lawvere

end Bauer
end LoF
end HeytingLean
