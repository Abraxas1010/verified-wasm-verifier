import Mathlib.CategoryTheory.Category.GaloisConnection
import HeytingLean.LoF.Nucleus
import HeytingLean.Logic.PSR
import HeytingLean.Logic.Dialectic

/-!
# Three generative laws as categorical invariants (thin-category layer)

This module records a categorical reading of the project’s three “generative laws”
(PSR / Occam / Dialectic) in the **preorder category** induced by a `PrimaryAlgebra`.

Key idea:
* A re-entry nucleus `R : Reentry α` determines a sublocale `Ω_R` of fixed points.
* The restriction map into the sublocale is left adjoint to the inclusion, via the
  Galois insertion `Sublocale.giRestrict` and the standard bridge
  `GaloisConnection.adjunction` for preorder categories.

We keep the scope deliberately thin: these results are *order-theoretic* facts
packaged as categorical statements in the preorder categories.
-/

namespace HeytingLean
namespace LoF
namespace Axioms
namespace GenerativeLaws

open CategoryTheory

universe u

variable {α : Type u} [PrimaryAlgebra α]

/-! ## The reflective adjunction `α ⥤ Ω_R ⥤ α` -/

noncomputable abbrev omegaReflector (R : Reentry α) : α ⥤ R.Omega :=
  (R.nucleus.toSublocale.giRestrict.gc.monotone_l).functor

noncomputable abbrev omegaInclusion (R : Reentry α) : R.Omega ⥤ α :=
  (R.nucleus.toSublocale.giRestrict.gc.monotone_u).functor

noncomputable abbrev omegaAdjunction (R : Reentry α) :
    omegaReflector (R := R) ⊣ omegaInclusion (R := R) :=
  (R.nucleus.toSublocale.giRestrict.gc).adjunction

@[simp] lemma omegaInclusion_obj (R : Reentry α) (x : R.Omega) :
    (omegaInclusion (R := R)).obj x = (x : α) := rfl

@[simp] lemma omegaReflector_obj_coe (R : Reentry α) (a : α) :
    ((omegaReflector (R := R)).obj a : α) = R a := by
  simp [omegaReflector]

@[simp] lemma omegaReflectorInclusion_obj (R : Reentry α) (a : α) :
    ((omegaReflector (R := R) ⋙ omegaInclusion (R := R)).obj a) = R a := by
  simp

/-! ## PSR: fixed points as “unit isomorphisms” -/

theorem psr_iff_unit_isIso (R : Reentry α) (a : α) :
    Logic.PSR.Sufficient (R := R) a ↔
      IsIso ((omegaAdjunction (R := R)).unit.app a) := by
  -- In a partial-order category, a morphism is an iso iff its endpoints are equal.
  have hIso :
      IsIso ((omegaAdjunction (R := R)).unit.app a) ↔
        a = (omegaReflector (R := R) ⋙ omegaInclusion (R := R)).obj a :=
    (PartialOrder.isIso_iff_eq ((omegaAdjunction (R := R)).unit.app a))
  -- The composite object is definably `R a`.
  simpa [Logic.PSR.Sufficient, omegaReflectorInclusion_obj (R := R) (a := a), eq_comm] using
    hIso.symm

/-! ## Occam: reflection / least closed element above -/

lemma reflector_le_iff (R : Reentry α) (a : α) (b : R.Omega) :
    (omegaReflector (R := R)).obj a ≤ b ↔ a ≤ (b : α) := by
  -- This is exactly the Galois connection behind the reflective adjunction.
  simpa [omegaReflector] using (R.nucleus.toSublocale.giRestrict.gc a b)

lemma close_le_of_le_fixed (R : Reentry α) {a b : α}
    (hab : a ≤ b) (hb : R b = b) : R a ≤ b := by
  have := R.monotone hab
  simpa [hb] using this

/-! ## Dialectic: synthesis as least closed above both poles -/

lemma dialectic_least {R : Reentry α} {T A W : α}
    (hT : T ≤ W) (hA : A ≤ W) (hW : R W = W) :
    Logic.Dialectic.synth (R := R) T A ≤ W :=
  Logic.Dialectic.synth_le (R := R) (T := T) (A := A) (W := W) hT hA hW

end GenerativeLaws
end Axioms
end LoF
end HeytingLean

